"use strict";
function ltn(v) { try { return Buffer.from(v).toString("latin1"); } catch (e) { return null; } }

function constby(node) {
  return (node && node.k === "Const" && node.v && node.v.k === "bytes") ? ltn(node.v.v) : null;
}

function bldfnrslv(fn) {
  const defs = {};
  for (const b of fn.order) {
    (function w(n) {
      if (!n) return;
      for (const s of (n.stmts || [])) {
        if (s.s === "Assign" && s.target && s.target.k === "Reg") (defs[s.target.n] = defs[s.target.n] || []).push(s.value);
      }
      if (n.cond !== undefined) { w(n.then); w(n.els); }
    })(b.node);
  }
  const umem = {};
  function ucnst(reg, seen) {
    if (reg in umem) return umem[reg];
    if (seen.has(reg)) return (umem[reg] = null);
    seen.add(reg);
    const ds = defs[reg] || [];
    if (!ds.length) return (umem[reg] = null);
    let res;
    for (const v of ds) {
      let nm = constby(v);
      if (nm === null) { nm = (v && v.k === "Reg") ? ucnst(v.n, seen) : null; }
      if (nm === null) return (umem[reg] = null);
      if (res === undefined) res = nm; else if (res !== nm) return (umem[reg] = null);
    }
    return (umem[reg] = (res === undefined ? null : res));
  }

  function lclback(stmts, upto, reg) {
    let cur = reg;
    for (let i = upto - 1; i >= 0; i--) {
      const s = stmts[i];
      if (s.s === "Assign" && s.target && s.target.k === "Reg" && s.target.n === cur) {
        const c = constby(s.value);
        if (c !== null) return c;
        if (s.value && s.value.k === "Reg") { cur = s.value.n; continue; }
        return { unrslv: cur };
      }
    }
    return { fallthru: cur };
  }
  function rslvkey(stmts, idx, reg) {
    const r = lclback(stmts, idx, reg);
    if (typeof r === "string") return r;
    const cur = (r.fallthru !== undefined) ? r.fallthru : r.unrslv;
    return ucnst(cur, new Set());
  }
  return { rslvkey, lclback };
}

function isenvobj(o) {
  return o && ((o.k === "Global" && o.name === "_ENV") || o.k === "EnvTable");
}

function envidx(fn) {
  const rslv = bldfnrslv(fn);
  const kstr = (k) => (typeof k === "string" ? k : JSON.stringify(k));
  const entk = kstr(fn.entry_key);
  const preds = new Map();
  for (const b of fn.order) {
    const bk = kstr(b.key);
    (function w(n, pth) {
      if (!n) return;
      const p = pth.concat([n]);
      if (n.cond !== null && n.cond !== undefined) { w(n.then, p); w(n.els, p); }
      else if (n.outcome && n.outcome.o === "Next") {
        const k = kstr(n.outcome.key);
        if (!preds.has(k)) preds.set(k, []);
        preds.get(k).push({ bk, pth: p });
      }
    })(b.node, []);
  }
  function upback(pth, reg) {
    let cur = reg;
    for (let i = pth.length - 1; i >= 0; i--) {
      const st = pth[i].stmts || [];
      const r = rslv.lclback(st, st.length, cur);
      if (typeof r === "string") return r;
      if (r.unrslv !== undefined) return null;
      cur = r.fallthru;
    }
    return { fallthru: cur };
  }
  function viapred(bk, reg, seen, dep) {
    if (bk === entk || dep > 64) return null;
    const sk = bk + "|" + reg;
    if (seen.has(sk)) return undefined;
    seen.add(sk);
    let res;
    for (const { bk: pk, pth } of preds.get(bk) || []) {
      let r = upback(pth, reg);
      if (r !== null && typeof r === "object") r = viapred(pk, r.fallthru, seen, dep + 1);
      if (r === null) return null;
      if (r === undefined) continue;
      if (res === undefined) res = r; else if (res !== r) return null;
    }
    return res === undefined ? null : res;
  }
  let at = { bk: "", anc: [] };
  function rslvat(stmts, idx, reg) {
    const r = rslv.lclback(stmts, idx, reg);
    if (typeof r === "string") return r;
    if (r.fallthru !== undefined) {
      let u = upback(at.anc, r.fallthru);
      if (u !== null && typeof u === "object") u = viapred(at.bk, u.fallthru, new Set(), 0);
      if (typeof u === "string") return u;
    }
    return rslv.rslvkey(stmts, idx, reg);
  }
  function rwexpr(x, stmts, idx) {
    if (!x || typeof x !== "object") return;
    if (x.k === "Index" && isenvobj(x.obj)) {
      let nm = null;
      if (x.key && x.key.k === "Reg") nm = rslvat(stmts, idx, x.key.n);
      else if (x.key && x.key.k === "Const") nm = constby(x.key);
      if (nm !== null && nm !== undefined) {
        delete x.obj; delete x.key; x.k = "Global"; x.name = nm;
        return;
      }
    }
    for (const k in x) if (k !== "k") rwexpr(x[k], stmts, idx);
  }
  function rwstmts(stmts) {
    for (let i = 0; i < stmts.length; i++) {
      const s = stmts[i];
      if (s.s === "Assign") { rwexpr(s.value, stmts, i); if (s.target && s.target.k === "Index") rwexpr(s.target, stmts, i); }
      else if (s.s === "CallStmt") { rwexpr(s.fn, stmts, i); rwexpr(s.args, stmts, i); }
      else if (s.s === "SetList") { rwexpr(s.tbl, stmts, i); rwexpr(s.values, stmts, i); }
    }
  }
  function walk(n) {
    if (!n) return;
    const stmts = n.stmts || [];
    if (n.stmts) rwstmts(n.stmts);
    if (n.cond !== null && n.cond !== undefined) {
      const sv = at;
      at = { bk: sv.bk, anc: sv.anc.concat([n]) };
      walk(n.then); walk(n.els);
      at = sv;
    }
    else if (n.outcome && n.outcome.o === "Ret" && n.outcome.values) rwexpr(n.outcome.values, stmts, stmts.length);
  }
  for (const b of fn.order) { at = { bk: kstr(b.key), anc: [] }; walk(b.node); }
}

module.exports = { envidx };

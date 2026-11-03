"use strict";
const lp = require("./loops.js");
const dc = require("./dce.js");
const tf = require("./truthfold.js");
const efx = require("./envfix.js");

const cmps = { CompareEq: ["equal", false, false], CompareNe: ["equal", true, false],
  CompareLt: ["less", false, false], CompareLe: ["less_equal", false, false],
  CompareGt: ["less", false, true], CompareGe: ["less_equal", false, true] };
const arith = { Add: "add", Sub: "subtract", Mul: "multiply", Div: "divide",
  FloorDiv: "floor_divide", Mod: "modulo", Pow: "power" };
const ordcmp = { CompareLt: 1, CompareLe: 1, CompareGt: 1, CompareGe: 1 };
const unop = { Minus: "negate", Not: "logical_not", Len: "length" };

function regkey(e) {
  if (e.k === "Reg") return "r" + e.n;
  if (e.k === "Pseudo") return "p" + e.name + "_" + e.depth;
  return null;
}

function ks(key) { return typeof key === "string" ? key : JSON.stringify(key); }

function erds(e, out) {
  if (!e) return;
  switch (e.k) {
    case "Reg": out.push("r" + e.n); break;
    case "Pseudo": out.push("p" + e.name + "_" + e.depth); break;
    case "Bin": erds(e.a, out); erds(e.b, out); break;
    case "Un": erds(e.a, out); break;
    case "Index": erds(e.obj, out); erds(e.key, out); break;
    case "TailCount": erds(e.tail, out); break;
    case "Multi": e.items.forEach((x) => erds(x, out)); erds(e.tail, out); break;
    case "SymList": e.items.forEach((x) => erds(x, out)); erds(e.tail, out); break;
    case "ClosureExpr": capregs(e).forEach((r) => out.push(r)); break;
    case "NewTable": e.items.forEach(([k, v]) => { erds(k, out); erds(v, out); }); break;
    case "TempTail": break;
    case "Spread": erds(e.m, out); break;
  }
}

function capregs(ce) {
  const regs = [];
  for (let i = 0; i < ce.upvals.length; i++) {
    const u = ce.upvals[i];
    const kind = ce.kinds[String(i + 1)];
    if (kind && "const" in kind) continue;
    if (u.k === "MaybeBox") regs.push("r" + u.reg);
    else if (u.k === "BoxRef") { const t = u.target; if (t && t.k === "Reg") regs.push("r" + t.n); }
    else if (u.k === "Upval") {}
    else erds(u, regs);
  }
  return regs;
}

function srds(s, out) {
  switch (s.s) {
    case "Assign": erds(s.value, out); if (s.target.k === "Index") erds(s.target, out); break;
    case "CallStmt": erds(s.fn, out); erds(s.args, out); break;
    case "SetList": erds(s.tbl, out); erds(s.values, out); break;
    case "Close": break;
  }
}

function iseff(s) {
  if (s.s === "CallStmt" || s.s === "SetList" || s.s === "Close") return true;
  if (s.s === "Assign") {
    const t = s.target;
    if (t.k === "Index" || t.k === "Global" || t.k === "KnownGlobal" || t.k === "Upval") return true;
    return false;
  }
  return true;
}

function bldtree(fns) {
  const byci = new Map();
  for (const f of fns) byci.set(f.ci, f);
  const par = new Map();
  const clsof = new Map();
  function regcls(ce, ci) {
    if (ce.proto.t !== "ci") return;
    const kid = ce.proto.ci;
    if (!par.has(kid)) par.set(kid, ci);
    if (!clsof.has(kid)) clsof.set(kid, ce);
  }
  function v(e, ci) {
    if (!e) return;
    if (e.k === "ClosureExpr") { regcls(e, ci); e.upvals.forEach((x) => v(x, ci)); }
    else if (e.k === "Multi" || e.k === "SymList") { e.items.forEach((x) => v(x, ci)); v(e.tail, ci); }
    else if (e.k === "Bin") { v(e.a, ci); v(e.b, ci); }
    else if (e.k === "Un") v(e.a, ci);
    else if (e.k === "Index") { v(e.obj, ci); v(e.key, ci); }
  }
  function scannode(n, ci) {
    for (const s of n.stmts) {
      if (s.s === "Assign") v(s.value, ci);
      else if (s.s === "CallStmt") { v(s.fn, ci); v(s.args, ci); }
      else if (s.s === "SetList") v(s.values, ci);
    }
    if (n.cond) { if (n.then) scannode(n.then, ci); if (n.els) scannode(n.els, ci); }
    else if (n.outcome && n.outcome.o === "Ret") v(n.outcome.values, ci);
  }
  for (const f of fns) for (const b of f.order) scannode(b.node, f.ci);
  const ordr = [];
  const seen = new Set();
  (function dfs(ci) {
    if (seen.has(ci) || !byci.has(ci)) return;
    seen.add(ci); ordr.push(ci);
    const f = byci.get(ci);
    const kids = [];
    for (const b of f.order) collcis(b.node, kids);
    for (const k of kids) dfs(k);
  })(0);
  return { byci, parent: par, clsof, preorder: ordr };
}

function collcis(n, out) {
  function v(e) {
    if (!e) return;
    if (e.k === "ClosureExpr") { if (e.proto.t === "ci") out.push(e.proto.ci); e.upvals.forEach(v); }
    else if (e.k === "Multi" || e.k === "SymList") { e.items.forEach(v); v(e.tail); }
    else if (e.k === "Bin") { v(e.a); v(e.b); }
    else if (e.k === "Un") v(e.a);
    else if (e.k === "Index") { v(e.obj); v(e.key); }
  }
  for (const s of n.stmts) { if (s.s === "Assign") v(s.value); else if (s.s === "CallStmt") { v(s.fn); v(s.args); } else if (s.s === "SetList") v(s.values); }
  if (n.cond) { if (n.then) collcis(n.then, out); if (n.els) collcis(n.els, out); }
  else if (n.outcome && n.outcome.o === "Ret") v(n.outcome.values);
}

function cval(c) {
  if (c === null || c === undefined) return { nil_value: {} };
  if (c.k === "int") return { number: c.v };
  if (c.k === "float") { const sp = { nan: "nan", inf: "positive_infinity", "-inf": "negative_infinity" }[c.v]; return sp ? { special_number: sp } : { number: Number(c.v) }; }
  if (c.k === "bool") return { boolean: c.v };
  if (c.k === "bytes") return { string: Buffer.from(c.v).toString("latin1") };
  if (c.k === "str") return { string: c.v };
  if (c.k === "repr") return { nil_value: {} };
  throw new Error("const value " + JSON.stringify(c));
}
function strkey(c) {
  if (!c) return null;
  if (c.k === "bytes") return Buffer.from(c.v).toString("latin1");
  if (c.k === "str") return c.v;
  return null;
}

function findfolds(ordr) {
  const skip = new Set(), fold = new Map(), bx = lp.boxd(ordr, new Set());
  const bbs = [], entof = new Map(), predcnt = new Map(), bbof = new Map();
  function walk(node) {
    const id = bbs.length, bb = { uses: new Set(), defs: new Set(), succ: [] }; bbs.push(bb); bbof.set(node, id);
    const add = (e) => { const r = []; erds(e, r); for (const x of r) if (!bb.defs.has(x)) bb.uses.add(x); };
    for (const st of node.stmts) {
      const r = []; srds(st, r); for (const x of r) if (!bb.defs.has(x)) bb.uses.add(x);
      if (st.s === "Assign" && (st.target.k === "Reg" || st.target.k === "Pseudo")) bb.defs.add(regkey(st.target));
    }
    if (node.cond) { add(node.cond); for (const arm of [node.then, node.els]) if (arm) bb.succ.push(walk(arm)); }
    else if (node.outcome) { if (node.outcome.o === "Next") bb.succ.push({ k: ks(node.outcome.key) }); else if (node.outcome.o === "Ret") add(node.outcome.values); }
    return id;
  }
  for (const b of ordr) entof.set(ks(b.key), walk(b.node));
  for (const bb of bbs) {
    const ns = [];
    for (const s of bb.succ) {
      if (typeof s === "object") { const t = entof.get(s.k); if (t !== undefined) { ns.push(t); predcnt.set(s.k, (predcnt.get(s.k) || 0) + 1); } }
      else ns.push(s);
    }
    bb.succ = ns;
  }
  const livein = bbs.map(() => new Set());
  let chg = true;
  while (chg) {
    chg = false;
    for (let i = bbs.length - 1; i >= 0; i--) {
      const bb = bbs[i], inn = new Set(bb.uses);
      for (const s of bb.succ) for (const r of livein[s]) if (!bb.defs.has(r)) inn.add(r);
      if (inn.size !== livein[i].size) { livein[i] = inn; chg = true; }
      else { for (const r of inn) if (!livein[i].has(r)) { livein[i] = inn; chg = true; break; } }
    }
  }
  const ndbykey = new Map();
  for (const b of ordr) ndbykey.set(ks(b.key), b.node);

  const strtpred = new Map();
  for (const b of ordr) {
    const n = b.node;
    if (!n.cond && n.outcome && n.outcome.o === "Next") {
      const tk = ks(n.outcome.key); strtpred.set(tk, strtpred.has(tk) ? null : n);
    }
  }

  for (const b of ordr) {
    const mn = b.node, mkey = ks(b.key);
    if (!mn.cond) continue;
    let c0, ltchnot;
    if (mn.cond.k === "Reg") { c0 = "r" + mn.cond.n; ltchnot = false; }
    else if (mn.cond.k === "Un" && mn.cond.op === "Not" && mn.cond.a && mn.cond.a.k === "Reg") { c0 = "r" + mn.cond.a.n; ltchnot = true; }
    else continue;
    if ((predcnt.get(mkey) || 0) !== 1) continue;
    let cur = c0, cmp = null, brk = false; const chnregs = [c0], skipstmt = [];
    for (let pos = mn.stmts.length - 1; pos >= 0; pos--) {
      const s = mn.stmts[pos];
      if (!(s.s === "Assign" && s.target.k === "Reg" && ("r" + s.target.n) === cur)) { brk = true; break; }
      if (s.value && s.value.k === "Bin" && cmps[s.value.op]) { cmp = s; skipstmt.push(s); break; }
      if (s.value && s.value.k === "Reg") { skipstmt.push(s); cur = "r" + s.value.n; chnregs.push(cur); continue; }
      brk = true; break;
    }
    if (brk) continue;
    if (!cmp) {
      const nn = strtpred.get(mkey);
      if (!nn || !nn.stmts.length) continue;
      const last = nn.stmts[nn.stmts.length - 1];
      if (!(last.s === "Assign" && last.target.k === "Reg" && ("r" + last.target.n) === cur
            && last.value && last.value.k === "Bin" && cmps[last.value.op])) continue;
      cmp = last; skipstmt.push(last);
    }
    const out = new Set();
    for (const s of bbs[entof.get(mkey)].succ) for (const r of livein[s]) out.add(r);
    let live = false; for (const r of chnregs) if (out.has(r) || bx.has(+r.slice(1))) { live = true; break; }
    if (live) continue;
    for (const s of skipstmt) skip.add(s);
    fold.set(mn, { cmp: cmp.value, ltchnot });
  }

  const dfnd = new Set();
  function scandefs(n) {
    for (const s of n.stmts) if (s.s === "Assign" && (s.target.k === "Reg" || s.target.k === "Pseudo")) dfnd.add(regkey(s.target));
    if (n.cond) { if (n.then) scandefs(n.then); if (n.els) scandefs(n.els); }
  }
  for (const b of ordr) scandefs(b.node);
  function liveaftr(node, i, r1, b) {
    for (let j = i + 1; j < node.stmts.length; j++) {
      const s = node.stmts[j]; const rd = []; srds(s, rd);
      if (rd.includes(r1) || (b && !dc.calm(s))) return true;
      if (s.s === "Assign" && (s.target.k === "Reg" || s.target.k === "Pseudo") && regkey(s.target) === r1) return false;
    }
    if (b) return true;
    if (node.cond) { const rd = []; erds(node.cond, rd); if (rd.includes(r1)) return true; }
    else if (node.outcome && node.outcome.o === "Ret") { const rd = []; erds(node.outcome.values, rd); if (rd.includes(r1)) return true; }
    const bid = bbof.get(node); if (bid === undefined) return true;
    for (const s of bbs[bid].succ) if (livein[s].has(r1)) return true;
    return false;
  }
  function scandead(node) {
    for (let i = 0; i < node.stmts.length; i++) {
      const s = node.stmts[i];
      if (s.s === "Assign" && s.target.k === "Reg" && s.value && s.value.k === "Reg") {
        const r1 = "r" + s.target.n, r2 = "r" + s.value.n;
        if (r1 !== r2 && !dfnd.has(r2) && !liveaftr(node, i, r1, bx.has(s.target.n))) skip.add(s);
      }
    }
    if (node.cond) { if (node.then) scandead(node.then); if (node.els) scandead(node.els); }
  }
  for (const b of ordr) scandead(b.node);

  const liveinat = (key) => { const bid = entof.get(typeof key === "string" ? key : ks(key)); return bid === undefined ? null : livein[bid]; };
  return { skip, fold, liveinat };
}

function findwin(ordr) {
  const winopen = new Map(), winmbr = new Map(), bx = lp.boxd(ordr, new Set());
  let nextid = 0;
  const rdsreg = (s, treg) => {
    const o = []; srds(s, o); return o.includes(treg);
  };
  const kvrdsreg = (s, treg) => {
    const o = [];
    if (s.s === "Assign") { erds(s.target.key, o); erds(s.value, o); }
    else if (s.s === "SetList") erds(s.values, o);
    return o.includes(treg);
  };
  function detrun(stmts) {
    for (let idx = 0; idx < stmts.length; idx++) {
      const s = stmts[idx];
      if (!(s.s === "Assign" && s.target.k === "Reg" && s.value && s.value.k === "NewTable"
            && !(s.value.items && s.value.items.length) && !bx.has(s.target.n))) continue;
      const treg = "r" + s.target.n;
      const mbrs = [];
      for (let k = idx + 1; k < stmts.length; k++) {
        const u = stmts[k];
        const issto = u.s === "Assign" && u.target.k === "Index" && u.target.obj.k === "Reg" && ("r" + u.target.obj.n) === treg;
        const isset = u.s === "SetList" && u.tbl && u.tbl.k === "Reg" && ("r" + u.tbl.n) === treg;
        if (issto || isset) {
          if (kvrdsreg(u, treg)) break;
          mbrs.push(u); continue;
        }
        if (u.s === "Assign" && u.target.k === "Reg" && ("r" + u.target.n) === treg) break;
        if (rdsreg(u, treg)) break;

      }
      if (mbrs.length) {
        const id = nextid++;
        winopen.set(s, id);
        for (const m of mbrs) winmbr.set(m, { winid: id, complete: false });
        winmbr.get(mbrs[mbrs.length - 1]).complete = true;
      }
    }
  }

  const gp = new lp.Grf(ordr).preds;
  let i = 0;
  while (i < ordr.length) {
    const stmts = []; let j = i;
    while (j < ordr.length) {
      const n = ordr[j].node;
      for (const s of n.stmts) stmts.push(s);
      j++;
      if (n.cond || !n.outcome || n.outcome.o !== "Next") break;
      if (!(j < ordr.length && ks(n.outcome.key) === ks(ordr[j].key) && (gp.get(ks(ordr[j].key)) || []).length < 2)) break;
    }
    detrun(stmts);
    i = j;
  }

  function scanarms(n) {
    if (!n.cond) return;
    if (n.then) { detrun(n.then.stmts); scanarms(n.then); }
    if (n.els) { detrun(n.els.stmts); scanarms(n.els); }
  }
  for (const b of ordr) scanarms(b.node);
  return { winopen, winmbr };
}

function emfn(ctx, ci) {
  const fn = ctx.byci.get(ci);
  const ordr = fn.order;

  efx.envidx(fn);
  const isroot = ci === 0;

  const prmreg = [];
  let entblk = null;

  if (ordr.length && ks(ordr[0].key) === ks(fn.entry_key)) entblk = ordr[0];
  if (entblk) {
    for (const s of entblk.node.stmts) {
      if (s.s === "Assign" && s.target.k === "Reg" && s.value && s.value.k === "Vararg") prmreg[s.value.i - 1] = "r" + s.target.n;
      else break;
    }
  }
  const pcnt = prmreg.length;
  const folds = findfolds(ordr);

  const dce = dc.finddead(ordr, folds.liveinat, { exprrds: erds, stmtrds: srds, ks });
  const wins = findwin(ordr);
  const winopen = wins.winopen, winmbr = wins.winmbr;
  const wincrt = new Map(), wintblreg = new Map();

  const bodyordr = entblk ? ordr.slice(1) : ordr;
  const rec = lp.recog(bodyordr, folds.liveinat, ordr, dce.skip);
  const lpbyhdr = rec.loops;
  const lpbyprep = {};
  const conshdr = new Set(), lpdrop = new Set();
  const lpexpch = [];
  for (const hk in lpbyhdr) {
    const loop = lpbyhdr[hk];
    if (!loop.cnt) lpbyprep[loop.prepkey] = loop; conshdr.add(hk);
    for (const s of loop.drops || []) lpdrop.add(s);
  }

  const live = new Set();
  const allstmts = [];
  function collst(n) {
    for (const s of n.stmts) allstmts.push(s);
    if (n.cond) { allstmts.push({ _cond: n.cond }); if (n.then) collst(n.then); if (n.els) collst(n.els); }
    else if (n.outcome && n.outcome.o === "Ret") allstmts.push({ _ret: n.outcome.values });
  }
  for (const b of ordr) collst(b.node);
  for (const s of allstmts) {
    if (s._cond) { const o = []; erds(s._cond, o); o.forEach((r) => live.add(r)); }
    else if (s._ret) { const o = []; erds(s._ret, o); o.forEach((r) => live.add(r)); }
    else if (iseff(s)) { const o = []; srds(s, o); o.forEach((r) => live.add(r)); }
  }
  let chg = true;
  while (chg) {
    chg = false;
    for (const s of allstmts) {
      if (s.s === "Assign" && (s.target.k === "Reg" || s.target.k === "Pseudo")) {
        const tk = regkey(s.target);
        if (live.has(tk)) { const o = []; erds(s.value, o); for (const r of o) if (!live.has(r)) { live.add(r); chg = true; } }
      }
    }
  }

  const regdefs = new Map();
  for (const s of allstmts) {
    if (s.s === "Assign" && (s.target.k === "Reg" || s.target.k === "Pseudo")) {
      const k = regkey(s.target); if (!regdefs.has(k)) regdefs.set(k, []); regdefs.get(k).push(s.value);
    }
  }
  for (const n of lp.boxd(ordr, new Set())) regdefs.delete("r" + n);
  const regnum = new Map(), regsnum = new Map();
  for (const k of regdefs.keys()) { regnum.set(k, true); regsnum.set(k, true); }
  function isnum(e) {
    if (!e) return false;
    if (e.k === "Const") return !!(e.v && (e.v.k === "int" || e.v.k === "float"));
    if (e.k === "Reg" || e.k === "Pseudo") return regnum.get(regkey(e)) === true;
    if (e.k === "Un" && e.op === "Minus") return isnum(e.a);
    if (e.k === "Bin" && arith[e.op]) return isnum(e.a) && isnum(e.b);
    return false;
  }
  function issnum(e) {
    if (!e) return false;
    if (e.k === "Const") return !!(e.v && (e.v.k === "int" || e.v.k === "float" || e.v.k === "str" || e.v.k === "bytes"));
    if (e.k === "Reg" || e.k === "Pseudo") return regsnum.get(regkey(e)) === true;
    if (e.k === "Un" && e.op === "Minus") return isnum(e.a);
    if (e.k === "Bin" && arith[e.op]) return isnum(e.a) && isnum(e.b);
    if (e.k === "Bin" && e.op === "Concat") return issnum(e.a) && issnum(e.b);
    return false;
  }
  for (let ch = true; ch;) {
    ch = false;
    for (const [k, vals] of regdefs) {
      const n = vals.every(isnum); if (regnum.get(k) !== n) { regnum.set(k, n); ch = true; }
      const sn = vals.every(issnum); if (regsnum.get(k) !== sn) { regsnum.set(k, sn); ch = true; }
    }
  }
  function nvrerrs(v) {
    if (!v) return false;
    if (v.k === "Bin" && arith[v.op]) return isnum(v.a) && isnum(v.b);
    if (v.k === "Bin" && ordcmp[v.op]) return isnum(v.a) && isnum(v.b);
    if (v.k === "Bin" && v.op === "Concat") return issnum(v.a) && issnum(v.b);
    if (v.k === "Un" && v.op === "Minus") return isnum(v.a);
    return false;
  }

  const asg = (s) => s.s === "Assign" && (s.target.k === "Reg" || s.target.k === "Pseudo");
  for (const s of allstmts) if (asg(s) && dc.delkind(s.value) === null && s.value.k !== "Global" && s.value.k !== "KnownGlobal" && !nvrerrs(s.value)) { const o = []; erds(s.value, o); o.forEach((r) => live.add(r)); }
  for (let ch = true; ch;) { ch = false; for (const s of allstmts) if (asg(s) && live.has(regkey(s.target))) { const o = []; erds(s.value, o); for (const r of o) if (!live.has(r)) { live.add(r); ch = true; } } }
  function dead(s) {
    if (!(s.s === "Assign" && (s.target.k === "Reg" || s.target.k === "Pseudo"))) return false;
    if (live.has(regkey(s.target))) return false;
    const v = s.value;
    if (dc.delkind(v) !== null) return true;
    if (v && (v.k === "Global" || v.k === "KnownGlobal")) return true;
    if (nvrerrs(v)) return true;
    return false;
  }

  const opentmps = new Set();
  function scantt(e) {
    if (!e) return;
    if (e.k === "TempTail") opentmps.add(e.t);
    else if (e.k === "Multi" || e.k === "SymList") { e.items.forEach(scantt); scantt(e.tail); }
    else if (e.k === "Bin") { scantt(e.a); scantt(e.b); }
    else if (e.k === "Un") scantt(e.a);
    else if (e.k === "Index") { scantt(e.obj); scantt(e.key); }
    else if (e.k === "Spread") scantt(e.m);
  }
  for (const s of allstmts) {
    if (s.s === "CallStmt") scantt(s.args);
    else if (s.s === "SetList") scantt(s.values);
    else if (s.s === "Assign") scantt(s.value);
    else if (s._ret) scantt(s._ret);
  }

  let nextreg = pcnt;
  const regmap = new Map();
  for (let i = 0; i < pcnt; i++) if (prmreg[i] !== undefined) regmap.set(prmreg[i], i);
  function hreg(rk) {
    if (regmap.has(rk)) return regmap.get(rk);
    const v = nextreg++; regmap.set(rk, v); return v;
  }
  function fresh() { return nextreg++; }

  const instrs = [];
  const tmpreg = new Map();
  const tblcrtidx = new Map();
  const blkstrt = {};
  const pndjmp = [];
  function push(ins) { instrs.push(ins); return instrs.length - 1; }

  function flat(e) {
    if (e == null) throw new Error("flatten nil");
    switch (e.k) {
      case "Reg": return hreg("r" + e.n);
      case "Pseudo": return hreg("p" + e.name + "_" + e.depth);
      case "Const": { const d = fresh(); push({ kind: "constant", value: cval(e.v), reads: [], writes: [d], successors: [instrs.length + 1], line_number: 1 }); return d; }
      case "Global": case "KnownGlobal": { const d = fresh(); push({ kind: "environment_get", name: e.name, reads: [], writes: [d], line_number: 1 }); return d; }
      case "Upval": { const d = fresh(); push({ kind: "upvalue_get", upvalue: e.idx - 1, reads: [], writes: [d], line_number: 1 }); return d; }
      case "Un": { const d = fresh(); const a = flat(e.a); push({ kind: "unary", operator: unop[e.op], reads: [a], writes: [d], line_number: 1 }); return d; }
      case "Bin": return flatbin(e);
      case "Index": { const d = fresh(); return emtblget(e, d); }
      case "ClosureExpr": { const d = fresh(); emcls(e, d); return d; }
      case "NewTable": { const d = fresh(); emnewtbl(e, d); return d; }
      case "TempVal": { const key = e.t + "#" + e.i; if (tmpreg.has(key)) return tmpreg.get(key); const d = fresh(); tmpreg.set(key, d); return d; }
      default: throw new Error("flatten expr " + e.k);
    }
  }
  function flatbin(e) {
    if (e.op === "Concat") { const rds = []; collcat(e, rds); const d = fresh(); push({ kind: "concat", reads: rds, writes: [d], line_number: 1 }); return d; }
    if (arith[e.op]) { const a = flat(e.a); const b = flat(e.b); const d = fresh(); push({ kind: "binary", operator: arith[e.op], reads: [a, b], writes: [d], line_number: 1 }); return d; }
    if (cmps[e.op]) return emcmpval(e, fresh());
    throw new Error("flattenBin op " + e.op);
  }
  function collcat(e, out) {
    if (e.k === "Bin" && e.op === "Concat") { collcat(e.a, out); collcat(e.b, out); }
    else out.push(flat(e));
  }

  function emlitk(crt, key, valexpr, cmpl, d) {
    const m = { kind: "table_set", constructor: { create: crt, mode: "literal" }, line_number: 1 };
    const sk = (key.k === "Const") ? strkey(key.v) : null;
    if (sk !== null) { m.key_constant = { string: sk }; m.reads = [flat(valexpr)]; }
    else { m.reads = [flat(key), flat(valexpr)]; }
    if (cmpl) { m.complete = true; m.table = d; }
    push(m);
  }
  function emnewtbl(e, d) {
    const itms = e.items || [];

    if (itms.length) {
      const allarr = itms.every(([k]) => k == null);
      const allkeyed = itms.every(([k]) => k != null);
      if (allarr || allkeyed) {
        const crt = push({ kind: "new_table", constructor: { create: -1, mode: "literal" }, reads: [], writes: [d], line_number: 1 });
        instrs[crt].constructor.create = crt; tblcrtidx.set(d, crt);
        if (allarr) {
          const rds = itms.map(([, v]) => flat(v));
          push({ kind: "set_list", constructor: { create: crt, mode: "literal" }, reads: rds, first_index: 1, complete: true, table: d, line_number: 1 });
        } else {
          for (let n = 0; n < itms.length; n++) emlitk(crt, itms[n][0], itms[n][1], n === itms.length - 1, d);
        }
        return d;
      }
    }

    const ix = push({ kind: "new_table", reads: [], writes: [d], line_number: 1 });
    tblcrtidx.set(d, ix);
    let arr = 1;
    for (const [k, v] of itms) {
      if (k == null) {
        const kr = fresh(); push({ kind: "constant", value: { number: arr }, reads: [], writes: [kr], successors: [instrs.length + 1], line_number: 1 });
        push({ kind: "table_set", reads: [d, kr, flat(v)], line_number: 1 }); arr++;
      } else if (k.k === "Const" && strkey(k.v) !== null) {
        push({ kind: "table_set", key_constant: { string: strkey(k.v) }, reads: [d, flat(v)], line_number: 1 });
      } else {
        push({ kind: "table_set", reads: [d, flat(k), flat(v)], line_number: 1 });
      }
    }
    return d;
  }
  function emtblget(e, d) {
    const kc = (e.key.k === "Const") ? strkey(e.key.v) : null;
    if (kc !== null) push({ kind: "table_get", key_constant: { string: kc }, reads: [flat(e.obj)], writes: [d], line_number: 1 });
    else push({ kind: "table_get", reads: [flat(e.obj), flat(e.key)], writes: [d], line_number: 1 });
    return d;
  }
  function emcmpval(e, d) {
    const [op, inv, swap] = cmps[e.op];
    push({ kind: "binary", operator: inv ? "not_equal" : op, reads: [flat(swap ? e.b : e.a), flat(swap ? e.a : e.b)], writes: [d], line_number: 1 });
    return d;
  }

  function emcls(ce, dst) {
    const proto = ce.proto;
    if (proto.t === "stub") { emstub(dst); return; }

    const isgtr = proto.t === "getter" || proto.t === "native";
    const kidci = isgtr ? (1000000 + ctx.synseq++) : proto.ci;
    if (ctx.crtkids) ctx.crtkids.add(kidci);
    const caps = [], rds = [], refs = [], clz = [], dr = !isgtr && ctx.drop.get(kidci);
    for (let i = 0; i < ce.upvals.length; i++) {
      const u = ce.upvals[i], kind = ce.kinds[String(i + 1)];
      if (dr && dr[i]) continue;
      if (kind && "const" in kind) {
        const cv = kind.const;
        const r = fresh(); push({ kind: "constant", value: cval(cv && cv.k ? cv : null), reads: [], writes: [r], successors: [instrs.length + 1], line_number: 1 });
        caps.push({ mode: "value" }); rds.push(r); clz.push("value");
      } else if (u.k === "MaybeBox") {
        const r = hreg("r" + u.reg); caps.push({ mode: "reference", register: r }); refs.push(r); clz.push("place");
      } else if (u.k === "BoxRef" && u.target && u.target.k === "Reg") {
        const r = hreg("r" + u.target.n); caps.push({ mode: "reference", register: r }); refs.push(r); clz.push("place");
      } else if (u.k === "BoxRef" && u.target && u.target.k === "Upval") {
        caps.push({ mode: "upvalue", upvalue: u.target.idx - 1 }); clz.push((ctx.upclz.get(ci) || [])[u.target.idx - 1] || "place");
      } else if (u.k === "Upval") {
        caps.push({ mode: "upvalue", upvalue: u.idx - 1 }); clz.push((ctx.upclz.get(ci) || [])[u.idx - 1] || "place");
      } else {
        const r = flat(u); caps.push({ mode: "value" }); rds.push(r); clz.push("value");
      }
    }
    ctx.upclz.set(kidci, clz);

    if (isgtr) ctx.syn.push({ ci: kidci, parci: ci, out: proto.t === "native" ? synnat(kidci, ci, clz, proto.id) : syngtr(kidci, ci, clz) });
    const ln = []; for (let i = 0; i < caps.length + 2; i++) ln.push(1);
    push({ kind: "closure", function: kidci, captures: caps, references: refs, reads: rds, writes: [dst], line_numbers: ln, line_number: 1 });
  }

  function syngtr(idx, parci, clz) {
    const n = clz.length, ins = [], rr = [];
    for (let i = 0; i < n; i++) { ins.push({ kind: "upvalue_get", upvalue: i, reads: [], writes: [i], line_number: 1 }); rr.push(i); }
    ins.push({ kind: "return", reads: rr, line_number: 1 });
    return { function_index: idx, parent_index: parci, parameter_count: 0, is_variadic: true,
      upvalues: clz.map((c) => ({ class: c, line_number: 1 })), instructions: ins };
  }
  function synnat(idx, parci, clz, id) {
    const ins = [{ kind: "environment_get", name: "__devert_native_" + id, reads: [], writes: [0], line_number: 1 }], rr = [0];
    for (let i = 0; i < clz.length; i++) { ins.push({ kind: "upvalue_get", upvalue: i, reads: [], writes: [i + 1], line_number: 1 }); rr.push(i + 1); }
    ins.push({ kind: "return", reads: rr, line_number: 1 });
    return { function_index: idx, parent_index: parci, parameter_count: 0, is_variadic: false,
      upvalues: clz.map((c) => ({ class: c, line_number: 1 })), instructions: ins };
  }
  function emstub(dst) {
    push({ kind: "constant", value: { nil_value: {} }, reads: [], writes: [dst], successors: [instrs.length + 1], line_number: 1 });
  }

  function emst(s) {
    if (folds.skip.has(s) || dce.skip.has(s) || dead(s) || lpdrop.has(s)) return;
    if (s.s === "Assign") return emasgn(s);
    if (s.s === "SetList") return emsetlst(s);
    if (s.s === "Close") { push({ kind: "close_upvalues", from: typeof s.reg === "number" ? hreg("r" + s.reg) : flat(s.reg), reads: [], line_number: 1 }); return; }
    throw new Error("stmt " + s.s);
  }
  function emlst(stmts, skp) {
    for (let i = 0; i < stmts.length;) {
      const s = stmts[i];
      if (skp && skp(s, i)) i++;
      else if (s.s === "CallStmt" && !(folds.skip.has(s) || dce.skip.has(s) || lpdrop.has(s))) i = emcall(stmts, i);
      else { emst(s); i++; }
    }
  }
  function emasgn(s) {
    const t = s.target, v = s.value;

    if ((t.k === "Reg" || t.k === "Pseudo") && winopen.has(s)) {
      const d = hreg(regkey(t));
      const ix = push({ kind: "new_table", constructor: { create: -1, mode: "literal" }, reads: [], writes: [d], line_number: 1 });
      instrs[ix].constructor.create = ix;
      const id = winopen.get(s); wincrt.set(id, ix); wintblreg.set(id, d); tblcrtidx.set(d, ix);
      return;
    }
    if (t.k === "Reg" || t.k === "Pseudo") { const d = hreg(regkey(t)); return emval(v, d); }
    if (t.k === "Index") {
      const mem = winmbr.get(s);
      if (mem && wincrt.has(mem.winid)) { emlitk(wincrt.get(mem.winid), t.key, v, mem.complete, wintblreg.get(mem.winid)); return; }
      const kc = (t.key.k === "Const") ? strkey(t.key.v) : null;
      if (kc !== null) push({ kind: "table_set", key_constant: { string: kc }, reads: [flat(t.obj), flat(v)], line_number: 1 });
      else push({ kind: "table_set", reads: [flat(t.obj), flat(t.key), flat(v)], line_number: 1 });
      return;
    }
    if (t.k === "Global" || t.k === "KnownGlobal") { push({ kind: "environment_set", name: t.name, reads: [flat(v)], line_number: 1 }); return; }
    if (t.k === "Upval") { push({ kind: "upvalue_set", upvalue: t.idx - 1, reads: [flat(v)], line_number: 1 }); return; }
    throw new Error("assign target " + t.k);
  }
  function emval(v, d) {
    switch (v.k) {
      case "Const": push({ kind: "constant", value: cval(v.v), reads: [], writes: [d], successors: [instrs.length + 1], line_number: 1 }); return;
      case "Reg": push({ kind: "move", reads: [hreg("r" + v.n)], writes: [d], line_number: 1 }); return;
      case "Pseudo": push({ kind: "move", reads: [hreg("p" + v.name + "_" + v.depth)], writes: [d], line_number: 1 }); return;
      case "Global": case "KnownGlobal": push({ kind: "environment_get", name: v.name, reads: [], writes: [d], line_number: 1 }); return;
      case "Upval": push({ kind: "upvalue_get", upvalue: v.idx - 1, reads: [], writes: [d], line_number: 1 }); return;
      case "Un": push({ kind: "unary", operator: unop[v.op], reads: [flat(v.a)], writes: [d], line_number: 1 }); return;
      case "Bin": {
        if (v.op === "Concat") { const rds = []; collcat(v, rds); push({ kind: "concat", reads: rds, writes: [d], line_number: 1 }); return; }
        if (arith[v.op]) { push({ kind: "binary", operator: arith[v.op], reads: [flat(v.a), flat(v.b)], writes: [d], line_number: 1 }); return; }
        if (cmps[v.op]) { emcmpval(v, d); return; }
        throw new Error("assign bin " + v.op);
      }
      case "Index": emtblget(v, d); return;
      case "ClosureExpr": emcls(v, d); return;
      case "NewTable": emnewtbl(v, d); return;
      case "Vararg": {
        const wrs = [];
        for (let k = 1; k < v.i; k++) wrs.push(fresh());
        wrs.push(d);
        push({ kind: "varargs", count: v.i, reads: [], writes: wrs, line_number: 1 });
        if (v.i > pcnt) ctx.variadic.add(ci);
        return;
      }
      case "TempVal": push({ kind: "move", reads: [flat(v)], writes: [d], line_number: 1 }); return;
      default: throw new Error("assign value " + v.k);
    }
  }

  function emvargp() { push({ kind: "varargs", produces_pack_at: 0, reads: [], line_number: 1 }); ctx.variadic.add(ci); }

  function rslvcall(s) {
    const fn = s.fn, args = s.args;
    if (fn.k === "Index" && fn.key.k === "Const" && strkey(fn.key.v) !== null
        && args.items.length >= 1 && issamereg(fn.obj, args.items[0])) {
      return { namecall: true, method: strkey(fn.key.v), base: [flat(fn.obj)], argitms: args.items.slice(1) };
    }
    return { namecall: false, base: [flat(fn)], argitms: args.items };
  }
  function issamereg(a, b) { return a && b && a.k === "Reg" && b.k === "Reg" && a.n === b.n; }

  function emcall(stmts, i) {
    const s = stmts[i], t = s.t;
    const rc = rslvcall(s);
    const rds = rc.base.concat(rc.argitms.map(flat));
    let cons = false;
    if (s.args.tail) {
      if (s.args.tail.k === "VarargTail") { emvargp(); cons = true; }
      else if (s.args.tail.k === "TempTail") cons = true;
      else throw new Error("call arg tail " + s.args.tail.k);
    }
    const base = { kind: rc.namecall ? "namecall" : "call", reads: rds, line_number: 1 };
    if (rc.namecall) { base.method = rc.method; base.line_numbers = [1, 1]; }
    if (cons) base.consumes_pack_from = 0;
    if (opentmps.has(t)) { base.produces_pack_at = 0; push(base); return i + 1; }

    const wrs = []; let j = i + 1;
    while (j < stmts.length && stmts[j].s === "Assign" && stmts[j].target.k === "Reg"
           && stmts[j].value && stmts[j].value.k === "TempVal" && stmts[j].value.t === t) {
      wrs[stmts[j].value.i - 1] = hreg("r" + stmts[j].target.n); j++;
    }
    let rcnt = wrs.length;
    for (let k = 0; k < rcnt; k++) if (wrs[k] === undefined) wrs[k] = fresh();
    for (let ii = 1; ii <= rcnt; ii++) tmpreg.set(t + "#" + ii, wrs[ii - 1]);
    base.result_count = rcnt; base.writes = wrs;
    push(base);
    return j;
  }

  function emsetlst(s) {
    const mem = winmbr.get(s);
    if (mem && wincrt.has(mem.winid)) {
      const crt = wincrt.get(mem.winid), d = wintblreg.get(mem.winid);
      const rds = (s.values.items || []).map(flat);
      let cons = false;
      if (s.values.tail) {
        if (s.values.tail.k === "VarargTail") { emvargp(); cons = true; }
        else if (s.values.tail.k === "TempTail") cons = true;
        else throw new Error("set_list tail " + s.values.tail.k);
      }
      const sl = { kind: "set_list", constructor: { create: crt, mode: "literal" }, reads: rds, first_index: s.start, line_number: 1 };
      if (cons) sl.consumes_pack_from = 0;
      if (mem.complete) { sl.complete = true; sl.table = d; }
      push(sl);
      return;
    }
    const tbl = flat(s.tbl);
    const itms = (s.values.items || []).map(flat);
    const crt = tblcrtidx.get(tbl);
    if (crt === undefined) {
      if (s.values.tail) throw new Error("set_list open tail without a tracked table");
      for (let k = 0; k < itms.length; k++) {
        const idxreg = fresh();
        push({ kind: "constant", value: { number: s.start + k }, reads: [], writes: [idxreg], successors: [instrs.length + 1], line_number: 1 });
        push({ kind: "table_set", reads: [tbl, idxreg, itms[k]], line_number: 1 });
      }
      return;
    }
    instrs[crt].constructor = { create: crt, mode: "ordered" };
    let cons = false;
    if (s.values.tail) {
      if (s.values.tail.k === "VarargTail") { emvargp(); cons = true; }
      else if (s.values.tail.k === "TempTail") cons = true;
      else throw new Error("set_list tail " + s.values.tail.k);
    }
    const sl = { kind: "set_list", constructor: { create: crt, mode: "ordered" }, reads: itms, first_index: s.start, line_number: 1 };
    if (cons) sl.consumes_pack_from = 0;
    push(sl);
  }

  function emret(vals) {
    const itms = (vals && vals.items) || [];
    const rds = itms.map(flat);
    if (vals && vals.tail) {
      if (vals.tail.k === "VarargTail") { emvargp(); push({ kind: "return", reads: rds, consumes_pack_from: 0, line_number: 1 }); return; }
      if (vals.tail.k === "TempTail") { push({ kind: "return", reads: rds, consumes_pack_from: 0, line_number: 1 }); return; }
      throw new Error("return tail " + vals.tail.k);
    }
    push({ kind: "return", reads: rds, line_number: 1 });
  }

  let boxd = null;
  function boxregs() {
    if (boxd) return boxd;
    boxd = new Set();
    (function wk(o) {
      if (!o || typeof o !== "object") return;
      if (o.k === "ClosureExpr") o.upvals.forEach((u, i) => {
        const kd = o.kinds[String(i + 1)];
        if (kd && "const" in kd) return;
        if (u.k === "MaybeBox") boxd.add("r" + u.reg);
        else if (u.k === "BoxRef" && u.target && u.target.k === "Reg") boxd.add("r" + u.target.n);
      });
      for (const v of Object.values(o)) wk(v);
    })(allstmts);
    return boxd;
  }
  function movbl(s, rd) {
    if (!(s.s === "Assign" && (s.target.k === "Reg" || s.target.k === "Pseudo") && s.value)) return false;
    const tk = regkey(s.target), vk = regkey(s.value);
    if (!vk && s.value.k !== "Const") return false;
    return !rd.includes(tk) && !boxregs().has(tk) && !(vk && boxregs().has(vk));
  }
  function pkplan() {
    const pc = new Map(), hoist = new Map(), moved = new Set();
    const cnt = (n) => {
      if (!n) return;
      if (n.cond) { cnt(n.then); cnt(n.els); }
      else if (n.outcome && n.outcome.o === "Next") { const k = ks(n.outcome.key); pc.set(k, (pc.get(k) || 0) + 1); }
    };
    for (const b of ordr) cnt(b.node);
    const ok = (b) => b !== entblk && !lpbyprep[ks(b.key)] && !conshdr.has(ks(b.key));
    for (let i = 0, j; i < ordr.length; i = j) {
      j = i + 1;
      if (!ok(ordr[i])) continue;
      while (j < ordr.length) {
        const n = ordr[j - 1].node, k = ks(ordr[j].key);
        if (n.cond || !n.outcome || n.outcome.o !== "Next" || ks(n.outcome.key) !== k || pc.get(k) !== 1 || !ok(ordr[j])) break;
        j++;
      }
      let out = [];
      for (let k = i; k < j; k++) out = out.concat(ordr[k].node.stmts);
      for (let c = 0; c < out.length; c++) {
        const s = out[c], tl = s.s === "CallStmt" ? s.args.tail : s.s === "SetList" ? s.values.tail : null;
        if (!tl || tl.k !== "TempTail") continue;
        let p = c - 1;
        while (p >= 0 && !(out[p].s === "CallStmt" && out[p].t === tl.t)) p--;
        if (p < 0 || p === c - 1) continue;
        let h = p;
        while (h > 0 && out[h].args.tail && out[h].args.tail.k === "TempTail" && out[h - 1].s === "CallStmt" && out[h - 1].t === out[h].args.tail.t) h--;
        const gap = out.slice(p + 1, c), rd = [];
        for (let k = h; k <= p; k++) srds(out[k], rd);
        if (!gap.some((g) => !(folds.skip.has(g) || dce.skip.has(g) || dead(g))) || !gap.every((g) => movbl(g, rd))) continue;
        hoist.set(out[h], (hoist.get(out[h]) || []).concat(gap));
        for (const g of gap) moved.add(g);
        out = out.slice(0, h).concat(gap, out.slice(h, p + 1), out.slice(c));
      }
    }
    return { hoist, moved };
  }
  const pk = pkplan();

  function emseq(stmts) {
    let i = 0;
    while (i < stmts.length) {
      const s = stmts[i];
      if (pk.hoist.has(s)) pk.hoist.get(s).forEach((g) => emst(g));
      if (dead(s) || dce.skip.has(s) || pk.moved.has(s)) { i++; continue; }
      if (s.s === "CallStmt") { i = emcall(stmts, i); continue; }

      emst(s); i++;
    }
  }

  function emnode(n) {
    emseq(n.stmts);
    if (n.cond) {
      const f = folds.fold.get(n);
      let bi;
      if (f) {
        const [op, inv, swap] = cmps[f.cmp.op];
        const a = flat(swap ? f.cmp.b : f.cmp.a), b = flat(swap ? f.cmp.a : f.cmp.b);
        bi = push({ kind: "branch", operator: op, reads: [a, b], target: -1, inverted: inv !== f.ltchnot, line_number: 1 });
      } else {
        const br = { kind: "branch", reads: [], target: -1, inverted: false, line_number: 1 };
        setbrcond(br, n.cond);
        bi = push(br);
      }
      if (n.els) emnode(n.els); else push({ kind: "return", reads: [], line_number: 1 });
      instrs[bi].target = instrs.length;
      if (n.then) emnode(n.then); else push({ kind: "return", reads: [], line_number: 1 });
    } else if (n.outcome) {
      const o = n.outcome;
      if (o.o === "Next") {
        const tk = ks(o.key);
        if (conshdr.has(tk)) {
          const loop = lpbyhdr[tk];
          if (loop.entout === o) emcnt(loop);
          else push({ kind: "iteration_loop", reads: [], loop: { iteration: loop.kind, prepare: lppreidx[tk] }, line_number: 1 });
        } else { const idx = push({ kind: "jump", target: -1, reads: [], line_number: 1 }); pndjmp.push({ idx, target: tk }); }
      }
      else if (o.o === "Ret") emret(o.values);
      else throw new Error("outcome " + o.o);
    } else if (n.error) {
      throw new Error("error node: " + n.error);
    } else {
      throw new Error("node without cond/outcome");
    }
  }
  function cmpt(ins) {
    const rmv = new Array(ins.length).fill(false);
    for (let i = 0; i < ins.length; i++) if (ins[i].kind === "jump" && ins[i].target === i + 1) rmv[i] = true;

    const snaptgt = ins.map((x) => (x.kind === "jump" ? x.target : -1));
    function rslv(r) { let g = 0; while (r < ins.length && (rmv[r] || ins[r].kind === "jump") && g++ < ins.length + 1) r = snaptgt[r]; return r; }
    const seen = new Uint8Array(ins.length), st = [];
    const go = (r, f) => { if (f) while (r < ins.length && rmv[r]) r++; else { r = rslv(r); if (rmv[r]) rmv[r] = false; } if (r >= 0 && r < ins.length && !seen[r]) { seen[r] = 1; st.push(r); } };
    for (go(0, 1); st.length;) {
      const i = st.pop(), x = ins[i];
      if (x.kind === "jump") go(x.target);
      else if (x.kind === "branch") { go(x.target); go(i + 1, 1); }
      else if (x.kind === "constant" && x.successors) go(x.successors[0]);
      else if (x.kind === "iteration_prepare") { go(i + 1, 1); go(x.loop.exit); }
      else if (x.kind === "iteration_loop") go(x.loop.prepare);
      else if (x.kind !== "return") go(i + 1, 1);
    }
    for (let i = 0; i < ins.length; i++) if (!seen[i]) rmv[i] = true;
    const nidx = new Array(ins.length); let n = 0;
    for (let i = 0; i < ins.length; i++) if (!rmv[i]) nidx[i] = n++;
    const map = (r) => nidx[rslv(r)];
    const out = [];
    for (let i = 0; i < ins.length; i++) {
      if (rmv[i]) continue;
      const x = ins[i];
      if (x.kind === "jump") x.target = map(x.target);
      else if (x.kind === "branch") x.target = map(x.target);
      else if (x.kind === "constant" && x.successors) x.successors = [map(x.successors[0])];
      else if (x.kind === "iteration_prepare") { x.loop.prepare = map(x.loop.prepare); x.loop.exit = map(x.loop.exit); }
      else if (x.kind === "iteration_loop") x.loop.prepare = map(x.loop.prepare);
      if (Object.prototype.hasOwnProperty.call(x, "constructor") && typeof x.constructor.create === "number") x.constructor.create = map(x.constructor.create);
      out.push(x);
    }
    return out;
  }
  function setbrcond(ins, cond) {
    if (cond.k === "Bin" && cmps[cond.op]) {
      const [op, inv, swap] = cmps[cond.op];
      ins.operator = op; ins.inverted = inv;
      ins.reads = [flat(swap ? cond.b : cond.a), flat(swap ? cond.a : cond.b)];
    } else if (cond.k === "Un" && cond.op === "Not") {
      ins.reads = [flat(cond.a)]; ins.inverted = true;
    } else {
      ins.reads = [flat(cond)]; ins.inverted = false;
    }
  }

  const ndbykey = new Map();
  for (const b of bodyordr) ndbykey.set(ks(b.key), b.node);
  const lppreidx = {};
  const laid = new Set();

  function emprep(prepkey, loop) {
    const prepnode = ndbykey.get(prepkey);

    if (loop.kind === "numeric") {
      emlst(prepnode.stmts, (s, i) => prepnode.stmts === loop.prepstmts && i === loop.prepidx);
      const idx = hreg("r" + loop.a), lim = hreg("r" + (loop.a + 1)), step = hreg("r" + (loop.a + 2));
      const vbls = [hreg("r" + loop.v)];
      const pidx = push({ kind: "iteration_prepare", reads: [idx, lim, step], writes: [],
        loop: { iteration: "numeric", variables: vbls, prepare: -1, exit: -1 }, line_number: 1 });
      instrs[pidx].loop.prepare = pidx;
      lppreidx[loop.header] = pidx;
      lpexpch.push({ pidx, exitkey: loop.exitkey });
    } else if (loop.fused) {
      emlst(prepnode.stmts, (s) => s.s === "Assign" && s.target.k === "Pseudo" && s.target.name === loop.gentgt.name && s.target.depth === loop.gentgt.depth);
      const rds = loop.reads3.map((e) => flat(e));
      const vbls = loop.vars.map((r) => hreg("r" + r));
      const pidx = push({ kind: "iteration_prepare", reads: rds, writes: [], loop: { iteration: "generic", variables: vbls, prepare: -1, exit: -1 }, line_number: 1 });
      instrs[pidx].loop.prepare = pidx;
      lppreidx[loop.header] = pidx;
      lpexpch.push({ pidx, exitkey: loop.exitkey });
    } else if (loop.ipairs) {
      emlst(prepnode.stmts);
      const ig = fresh(); push({ kind: "environment_get", name: "ipairs", reads: [], writes: [ig], line_number: 1 });
      const iter = fresh(), st = fresh(), ctl = fresh();
      push({ kind: "call", result_count: 3, reads: [ig, hreg("r" + loop.tbl)], writes: [iter, st, ctl], line_number: 1 });
      const vbls = loop.vars.map((r) => hreg("r" + r));
      const pidx = push({ kind: "iteration_prepare", reads: [iter, st, ctl], writes: [],
        loop: { iteration: "generic", variables: vbls, prepare: -1, exit: -1 }, line_number: 1 });
      instrs[pidx].loop.prepare = pidx;
      lppreidx[loop.header] = pidx;
      lpexpch.push({ pidx, exitkey: loop.exitkey });
    } else {
      emlst(prepnode.stmts);
      const iter = hreg("r" + loop.a), st = hreg("r" + (loop.a + 1)), ctl = hreg("r" + (loop.a + 2));
      const vbls = loop.vars.map(([r]) => hreg("r" + r));
      const pidx = push({ kind: "iteration_prepare", reads: [iter, st, ctl], writes: [],
        loop: { iteration: "generic", variables: vbls, prepare: -1, exit: -1 }, line_number: 1 });
      instrs[pidx].loop.prepare = pidx;
      lppreidx[loop.header] = pidx;
      lpexpch.push({ pidx, exitkey: loop.exitkey });
    }
  }

  function emcnt(lp) {
    const iv = hreg("r" + lp.ind), pidx = push({ kind: "iteration_prepare", reads: [iv, flat(lp.lim), hreg("r" + lp.step)], writes: [], loop: { iteration: "numeric", variables: [iv], prepare: -1, exit: -1 }, line_number: 1 });
    instrs[pidx].loop.prepare = pidx; lppreidx[lp.header] = pidx;
    const lay = (n) => { const o = []; collnxt(n, o); for (const k of o) laykey(k); };
    emnode(lp.bodynd); lay(lp.bodynd);
    instrs[pidx].loop.exit = instrs.length;
    emnode(lp.exitnd); lay(lp.exitnd);
  }
  function layexit(ek) {
    const t = typeof ek === "string" ? ek : ks(ek);
    if (conshdr.has(t) && lppreidx[t] !== undefined && blkstrt[t] === undefined) {
      const loop = lpbyhdr[t];
      blkstrt[t] = instrs.length;
      push({ kind: "iteration_loop", reads: [], loop: { iteration: loop.kind, prepare: lppreidx[t] }, line_number: 1 });
      return;
    }
    laykey(ek);
  }
  function laykey(key0) {
    const todo = [[0, key0]];
    while (todo.length) {
      const [exit, key] = todo.pop();
      if (exit) { layexit(key); continue; }
      const tk = typeof key === "string" ? key : ks(key);
      if (laid.has(tk) || conshdr.has(tk)) continue;
      if (lpbyprep[tk]) {
        const loop = lpbyprep[tk];
        laid.add(tk);
        blkstrt[tk] = instrs.length;
        emprep(tk, loop);
        todo.push([1, loop.exitkey]);
        if (loop.fused) emnode(loop.bodynd); else todo.push([0, loop.bodykey]);
        continue;
      }
      laid.add(tk);
      blkstrt[tk] = instrs.length;
      const node = ndbykey.get(tk);
      emnode(node);
      const succ = [];
      collnxt(node, succ);
      for (let i = succ.length - 1; i >= 0; i--) todo.push([0, succ[i]]);
    }
  }
  function collnxt(n, out) {
    if (n.cond) { if (n.els) collnxt(n.els, out); if (n.then) collnxt(n.then, out); }
    else if (n.outcome && n.outcome.o === "Next") { const k = ks(n.outcome.key); if (!conshdr.has(k)) out.push(k); }
  }

  let firstbody = null;
  if (entblk) {
    emlst(entblk.node.stmts, (s) => s.s === "Assign" && s.target.k === "Reg" && s.value && s.value.k === "Vararg");
    if (entblk.node.outcome && entblk.node.outcome.o === "Next") firstbody = ks(entblk.node.outcome.key);
    const jidx = push({ kind: "jump", target: -1, reads: [], line_number: 1 });
    pndjmp.push({ idx: jidx, target: firstbody });
  } else {
    firstbody = bodyordr.length ? ks(bodyordr[0].key) : null;
  }
  if (firstbody) laykey(firstbody);

  for (const b of bodyordr) laykey(ks(b.key));

  for (const pj of pndjmp) {
    const t = blkstrt[pj.target];
    if (t === undefined) throw new Error("jump target block not found in ci " + ci + ": " + pj.target);
    instrs[pj.idx].target = t;
  }
  for (const ep of lpexpch) {
    const t = blkstrt[ep.exitkey];
    if (t === undefined) throw new Error("loop exit block not found in ci " + ci);
    instrs[ep.pidx].loop.exit = t;
  }
  const finins = cmpt(instrs);

  const rnd = () => { const re = cmpt(finins); finins.length = 0; for (const x of re) finins.push(x); };
  while (tf.foldfn(finins)) rnd();
  while (tf.dcefn(finins)) { rnd(); while (tf.foldfn(finins)) rnd(); }

  const vard = ctx.variadic.has(ci);
  const out = { function_index: ci, parameter_count: pcnt, is_variadic: vard, instructions: finins };
  if (fn.params && fn.params.length && pcnt) out.parameter_names = fn.params.slice(0, pcnt);
  if (!isroot) {
    out.parent_index = ctx.parent.get(ci);
    const cls = ctx.upclz.get(ci) || [];
    out.upvalues = cls.map((c) => ({ class: c, line_number: 1 }));
  }
  return out;
}

function dropup(byci) {
  const cst = new Map(), refd = new Map(), drop = new Map();
  for (const f of byci.values()) {
    const rs = new Set(); refd.set(f.ci, rs);
    (function wk(o) {
      if (!o || typeof o !== "object") return;
      if (o.k === "Upval") rs.add(o.idx);
      if (o.k === "ClosureExpr" && o.proto.t === "ci") {
        const k = o.upvals.map((_, i) => { const kd = o.kinds[String(i + 1)]; return !!(kd && "const" in kd); });
        const p = cst.get(o.proto.ci); cst.set(o.proto.ci, p ? k.map((x, i) => x && p[i]) : k);
      }
      for (const v of Object.values(o)) wk(v);
    })(f.order);
  }
  for (const [ci, k] of cst) {
    const d = k.map((x, i) => x && refd.has(ci) && !refd.get(ci).has(i + 1));
    if (!d.some(Boolean)) continue;
    const nw = []; let n = 0; d.forEach((x, i) => { nw[i + 1] = x ? 0 : ++n; });
    (function wk(o) { if (!o || typeof o !== "object") return; if (o.k === "Upval") o.idx = nw[o.idx]; for (const v of Object.values(o)) wk(v); })(byci.get(ci).order);
    drop.set(ci, d);
  }
  return drop;
}

function emhnd(grph) {
  const tree = bldtree(grph.funcs);
  const ctx = { byci: tree.byci, parent: tree.parent, clsof: tree.clsof,
    upclz: new Map(), variadic: new Set(), crtkids: new Set(),
    synseq: 0, syn: [], drop: dropup(tree.byci) };
  const map = new Map();
  for (const ci of tree.preorder) map.set(ci, emfn(ctx, ci));
  const root = map.get(0);

  const keep = new Set([0]);
  for (const ci of tree.preorder) {
    if (ci === 0) continue;
    const p = tree.parent.get(ci);
    if (ctx.crtkids.has(ci) && keep.has(p)) keep.add(ci);
  }
  const fns = [];
  for (const ci of tree.preorder) {
    if (ci !== 0 && keep.has(ci)) fns.push(map.get(ci));

    if (keep.has(ci)) for (const s of ctx.syn) if (s.parci === ci) fns.push(s.out);
  }
  return {
    schema_version: "compiler_disassembly_handoff_v3",
    listing_sha256: "00",
    function_index: 0,
    parameter_count: root.parameter_count,
    is_variadic: root.is_variadic,
    module_root: true,
    fold_registers: true,
    instructions: root.instructions,
    functions: fns,
  };
}

module.exports = { emhnd };

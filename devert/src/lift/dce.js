"use strict";
const { Grf, boxd } = require("./loops.js");
function isnumcnst(x) { return x && x.k === "Const" && x.v && (x.v.k === "int" || x.v.k === "float"); }
function isstrcnst(x) { return x && x.k === "Const" && x.v && (x.v.k === "str" || x.v.k === "bytes"); }
const csafe = (k) => k.k === "Const" && !!k.v && k.v.v != null && k.v.k !== "repr" && k.v.v !== "nan";

const arith = new Set(["Add", "Sub", "Mul", "Div", "FloorDiv", "Mod", "Pow"]);
const ordcmp = new Set(["CompareLt", "CompareLe", "CompareGt", "CompareGe"]);

function cnstcat(e) {
  if (e.k === "Bin" && e.op === "Concat") return cnstcat(e.a) && cnstcat(e.b);
  return isnumcnst(e) || isstrcnst(e);
}

function delkind(e) {
  if (!e) return null;
  switch (e.k) {
    case "Const": return "const";
    case "Reg": case "Pseudo": return "move";
    case "NewTable": return pure(e) ? "table" : null;
    case "ClosureExpr": return e.upvals.every((u) => u.k === "MaybeBox" || u.k === "BoxRef" || pure(u)) ? "closure" : null;
    case "Un":
      if (e.op === "Not") return "unary";
      if (e.op === "Minus" ? isnumcnst(e.a) : isstrcnst(e.a)) return "unary";
      return null;
    case "Bin":
      if (e.op === "CompareEq" || e.op === "CompareNe") return "compare";
      if (e.op === "Concat") return cnstcat(e) ? "concat" : null;
      if (isnumcnst(e.a) && isnumcnst(e.b)) return "other";
      return null;
    default: return null;
  }
}

const calm = (s) => s.s === "Assign" && (s.target.k === "Reg" || s.target.k === "Pseudo") && (["const", "move", "table", "closure", "other"].includes(delkind(s.value)) || (s.value.k === "Un" && s.value.op === "Not"));

function finddead(ordr, liveinat, hlp) {
  const { exprrds, stmtrds, ks } = hlp;
  const skip = new Set();
  const gp = new Grf(ordr).preds, bx = boxd(ordr, new Set());

  let bi = 0;
  while (bi < ordr.length) {
    if (ordr[bi].node.cond) { bi++; continue; }
    const blk = [];
    let j = bi;
    while (j < ordr.length) {
      const n = ordr[j].node;
      if (n.cond) break;
      blk.push(ordr[j]);
      j++;
      if (!n.outcome || n.outcome.o !== "Next") break;
      if (!(j < ordr.length && ks(n.outcome.key) === ks(ordr[j].key))) break;
    }
    if (blk.length) anlzrun(blk);
    bi = j > bi ? j : bi + 1;
  }
  deadtbl(ordr, skip, ks, bx);
  return { skip };

  function anlzrun(blk) {
    const stmt = [];
    const seg = [];
    let sg = 0;
    for (const b of blk) { if (b !== blk[0] && (gp.get(ks(b.key)) || []).length > 1) sg++; for (const s of b.node.stmts) { stmt.push(s); seg.push(sg); } }
    if (!stmt.length) return;
    const lastnode = blk[blk.length - 1].node;

    let nver = 0;
    const cur = new Map();
    const defs = [];
    const info = new Array(stmt.length), bxo = [];
    const curv = (rk) => (cur.has(rk) ? cur.get(rk) : -1);
    const valvers = (e) => { const o = []; exprrds(e, o); return o.map(curv); };

    const regkof = (x) => x.k === "Reg" ? "r" + x.n : (x.k === "Pseudo" ? "p" + x.name + "_" + x.depth : null);
    function numdesc(e) {
      if (!e) return { k: "other" };
      if (e.k === "Const") return { k: "const", num: isnumcnst(e), snum: isnumcnst(e) || isstrcnst(e) };
      if (e.k === "Reg" || e.k === "Pseudo") return { k: "ref", v: e.k === "Reg" && bx.has(e.n) ? -1 : curv(regkof(e)) };
      if (e.k === "Un" && e.op === "Minus") return { k: "neg", a: numdesc(e.a) };
      if (e.k === "Bin" && arith.has(e.op)) return { k: "arith", a: numdesc(e.a), b: numdesc(e.b) };
      if (e.k === "Bin" && ordcmp.has(e.op)) return { k: "cmp", a: numdesc(e.a), b: numdesc(e.b) };
      if (e.k === "Bin" && e.op === "Concat") return { k: "concat", a: numdesc(e.a), b: numdesc(e.b) };
      return { k: "other" };
    }

    const fresh = (v, j) => v >= 0 && defs[v].kind === "table" && seg[defs[v].at] === seg[j] && !bx.has(defs[v].stmt.target.n);
    const vsafe = (v, j) => v >= 0 && seg[defs[v].at] === seg[j] && !bx.has(defs[v].stmt.target.n) && (fresh(v, j) || defs[v].kind === "closure" || (defs[v].kind === "const" && csafe(defs[v].expr)) || (defs[v].kind === "move" && vsafe(defs[v].vr[0], j)));
    for (let idx = 0; idx < stmt.length; idx++) {
      const s = stmt[idx];
      if (!calm(s)) for (const n of bx) bxo.push(curv("r" + n));
      if (s.s === "Assign" && s.target.k === "Reg") {
        const rk = "r" + s.target.n;
        const vrds = valvers(s.value.k === "ClosureExpr" ? { k: "Multi", items: s.value.upvals.filter((u) => u.k !== "MaybeBox" && u.k !== "BoxRef") } : s.value);
        const nd = numdesc(s.value);
        const v = nver++;
        defs[v] = { stmt: s, kind: delkind(s.value), expr: s.value, nd, at: idx, vr: vrds };
        info[idx] = { type: "def", v, vreads: vrds };
        cur.set(rk, v);
      } else if (s.s === "Assign" && s.target.k === "Index" && s.target.obj.k === "Reg") {
        const tver = curv("r" + s.target.obj.n);
        const kv = []; exprrds(s.target.key, kv); exprrds(s.value, kv);
        info[idx] = { type: "store", tver, kv: kv.map(curv), stmt: s, keep: !fresh(tver, idx) || !pure(s.value) || !(s.target.key.k === "Const" ? csafe(s.target.key) : vsafe(curv(regkof(s.target.key)), idx)) };
      } else if (s.s === "SetList" && s.tbl && s.tbl.k === "Reg") {
        const tver = curv("r" + s.tbl.n);
        const kv = []; exprrds(s.values, kv);
        info[idx] = { type: "store", tver, kv: kv.map(curv), stmt: s, keep: !fresh(tver, idx) || !!s.values.tail || !s.values.items.every(pure) };
      } else {
        const rd = []; stmtrds(s, rd);
        info[idx] = { type: "sink", vreads: rd.map(curv) };
      }
    }

    const numof = new Array(nver).fill(false);
    const snumof = new Array(nver).fill(false);
    function rnum(d) {
      switch (d.k) {
        case "const": return d.num;
        case "ref": return d.v >= 0 ? numof[d.v] : false;
        case "neg": return rnum(d.a);
        case "arith": return rnum(d.a) && rnum(d.b);
        default: return false;
      }
    }
    function rsnum(d) {
      switch (d.k) {
        case "const": return d.snum;
        case "ref": return d.v >= 0 ? snumof[d.v] : false;
        case "neg": return rnum(d.a);
        case "arith": return rnum(d.a) && rnum(d.b);
        case "concat": return rsnum(d.a) && rsnum(d.b);
        default: return false;
      }
    }
    for (let nch = true; nch;) {
      nch = false;
      for (let v = 0; v < nver; v++) {
        const d = defs[v] && defs[v].nd; if (!d) continue;
        const n = rnum(d), s = rsnum(d);
        if (n !== numof[v]) { numof[v] = n; nch = true; }
        if (s !== snumof[v]) { snumof[v] = s; nch = true; }
      }
    }

    const safedrop = new Array(nver).fill(false);
    for (let v = 0; v < nver; v++) {
      const d = defs[v]; if (!d || d.kind !== null) continue;
      const e = d.expr, nd = d.nd; if (!e || !nd) continue;
      if (e.k === "Bin" && arith.has(e.op)) safedrop[v] = rnum(nd.a) && rnum(nd.b);
      else if (e.k === "Bin" && ordcmp.has(e.op)) safedrop[v] = rnum(nd.a) && rnum(nd.b);
      else if (e.k === "Bin" && e.op === "Concat") safedrop[v] = rsnum(nd.a) && rsnum(nd.b);
      else if (e.k === "Un" && e.op === "Minus") safedrop[v] = rnum(nd.a);
    }

    const obs = new Set();
    const mark = (v) => { if (v >= 0) obs.add(v); };

    if (lastnode.outcome && lastnode.outcome.o === "Next") {
      const el = liveinat(lastnode.outcome.key);
      if (el) for (const rk of el) { if (cur.has(rk)) mark(cur.get(rk)); }
      else for (const v of cur.values()) mark(v);
    } else if (lastnode.outcome && lastnode.outcome.o === "Ret") {
      const rd = []; exprrds(lastnode.outcome.values, rd); for (const rk of rd) mark(curv(rk));
    } else {
      for (const v of cur.values()) mark(v);
    }

    for (const it of info) if (it && it.type === "sink") for (const v of it.vreads) mark(v);
    for (const v of bxo) mark(v);
    for (const n of bx) mark(curv("r" + n));

    let chg = true;
    while (chg) {
      chg = false;
      for (const it of info) {
        if (!it) continue;
        if (it.type === "def") {
          const need = (defs[it.v].kind === null && !safedrop[it.v]) || obs.has(it.v);
          if (need) for (const rv of it.vreads) if (rv >= 0 && !obs.has(rv)) { obs.add(rv); chg = true; }
        } else if (it.type === "store") {
          if (it.tver === -1 || obs.has(it.tver) || it.keep) {
            for (const rv of it.kv) if (rv >= 0 && !obs.has(rv)) { obs.add(rv); chg = true; }

            if (it.keep && it.tver >= 0 && !obs.has(it.tver)) { obs.add(it.tver); chg = true; }
          }
        }
      }
    }

    for (let idx = 0; idx < stmt.length; idx++) {
      const it = info[idx];
      if (!it || it.type !== "def") continue;
      const d = defs[it.v];
      if (obs.has(it.v)) continue;
      if (d.kind === null && !safedrop[it.v]) continue;
      skip.add(d.stmt);
      if (d.kind === "table") {
        for (let k = 0; k < stmt.length; k++) {
          const t = info[k];
          if (t && t.type === "store" && t.tver === it.v) skip.add(t.stmt);
        }
      }
    }
  }
}

function regs(o, out) {
  if (!o || typeof o !== "object") return;
  if (o.k === "Reg") out.push("r" + o.n); else if (o.k === "MaybeBox") out.push("r" + o.reg);
  for (const v of Object.values(o)) regs(v, out);
}
function pure(e) { return !e || e.k === "Const" || e.k === "Reg" || e.k === "Pseudo" || e.k === "Upval" || (e.k === "NewTable" && e.items.every(([k, v]) => (!k || csafe(k)) && pure(v))); }

function deadtbl(ordr, skip, ks, bx) {
  const at = new Map(), ndef = new Map(), cand = new Map(), roots = [], sts = [];
  const walk = (n, bk, pth) => {
    n.stmts.forEach((s, i) => { at.set(s, [bk, pth, i]); sts.push(s); if (s.s === "Assign" && s.target.k === "Reg") ndef.set(s.target.n, (ndef.get(s.target.n) || 0) + 1); });
    if (n.cond) { regs(n.cond, roots); if (n.then) walk(n.then, bk, pth.concat([n.then])); if (n.els) walk(n.els, bk, pth.concat([n.els])); }
    else regs(n.outcome, roots);
  };
  for (const b of ordr) walk(b.node, ks(b.key), []);
  let g = null;
  const dom = (d, s) => { const [b1, p1, i1] = at.get(d), [b2, p2, i2] = at.get(s); return b1 === b2 ? p1.every((x, j) => p2[j] === x) && (p1.length < p2.length || i1 < i2) : !p1.length && (g || (g = new Grf(ordr))).dom(b1, b2); };
  const tb = (x) => x && x.k === "Reg" ? cand.get("r" + x.n) : undefined;
  const safe = (k, s) => k.k === "Const" ? csafe(k) : !!tb(k) && !bx.has(k.n) && dom(tb(k).def, s);
  for (const s of sts) if (s.s === "Assign" && s.target.k === "Reg" && s.value && s.value.k === "NewTable" && ndef.get(s.target.n) === 1 && !skip.has(s)) cand.set("r" + s.target.n, { def: s, sts: [s], deps: [] });
  for (const s of sts) {
    if (skip.has(s)) continue;
    const d = s.s === "Assign" && s.target.k === "Reg" ? tb(s.target) : undefined;
    if (d && d.def === s) { if (!s.value.items.every(([k, v]) => k && safe(k, s) && pure(v))) roots.push("r" + s.target.n); regs(s.value, d.deps); continue; }
    const c = s.s === "Assign" && s.target.k === "Index" ? tb(s.target.obj) : s.s === "SetList" ? tb(s.tbl) : undefined;
    if (c && dom(c.def, s) && (s.s === "Assign" ? safe(s.target.key, s) && pure(s.value) : !s.values.tail && s.values.items.every(pure))) { c.sts.push(s); regs(s.s === "Assign" ? [s.target.key, s.value] : s.values, c.deps); }
    else regs(s, roots);
  }
  const live = new Set(roots), wl = [...live];
  while (wl.length) { const c = cand.get(wl.pop()); if (c) for (const r of c.deps) if (!live.has(r)) { live.add(r); wl.push(r); } }
  for (const [r, c] of cand) if (!live.has(r)) for (const s of c.sts) skip.add(s);
}

module.exports = { finddead, delkind, calm };

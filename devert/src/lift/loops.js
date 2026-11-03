"use strict";
function ks(key) { return typeof key === "string" ? key : JSON.stringify(key); }
function isreg(e, n) { return e && e.k === "Reg" && (n === undefined || e.n === n); }

function lvs(node, out, pth) {
  if (!node) return;
  if (node.cond != null) { lvs(node.then, out, (pth || []).concat([node])); lvs(node.els, out, (pth || []).concat([node])); }
  else out.push([node, pth || []]);
}
function succkeys(node) {
  const lv = []; lvs(node, lv);
  const out = [];
  for (const [x] of lv) if (x.outcome && x.outcome.o === "Next") out.push(ks(x.outcome.key));
  return out;
}

class Grf {
  constructor(ordr) {
    this.nodes = new Map();
    this.keyof = new Map();
    this.preds = new Map();
    this.order = ordr;
    for (const { key, node } of ordr) { this.nodes.set(ks(key), node); this.keyof.set(ks(key), key); }
    for (const { key, node } of ordr) {
      const lv = []; lvs(node, lv);
      for (const [leaf] of lv) if (leaf.outcome && leaf.outcome.o === "Next") {
        const tk = ks(leaf.outcome.key);
        if (!this.preds.has(tk)) this.preds.set(tk, []);
        this.preds.get(tk).push([ks(key), leaf]);
      }
    }
    this.entry = ordr.length ? ks(ordr[0].key) : null;
    this._idom = null;
  }
  idom() {
    if (this._idom) return this._idom;
    const post = [], seen = new Set();
    const st = [];
    if (this.entry && this.nodes.has(this.entry)) { st.push([this.entry, succkeys(this.nodes.get(this.entry))[Symbol.iterator]()]); seen.add(this.entry); }
    while (st.length) {
      const top = st[st.length - 1];
      let adv = false;
      for (let r = top[1].next(); !r.done; r = top[1].next()) {
        const s = r.value;
        if (!seen.has(s) && this.nodes.has(s)) { seen.add(s); st.push([s, succkeys(this.nodes.get(s))[Symbol.iterator]()]); adv = true; break; }
      }
      if (!adv) { post.push(top[0]); st.pop(); }
    }
    const rpo = post.reverse();
    const num = new Map(); rpo.forEach((k, i) => num.set(k, i));
    const idom = new Map();
    if (rpo.length) idom.set(this.entry, this.entry);
    const meet = (a, b) => {
      while (a !== b) { while (num.get(a) > num.get(b)) a = idom.get(a); while (num.get(b) > num.get(a)) b = idom.get(b); }
      return a;
    };
    let chg = true;
    while (chg) {
      chg = false;
      for (let i = 1; i < rpo.length; i++) {
        const k = rpo[i];
        const ps = (this.preds.get(k) || []).map(([p]) => p).filter((p) => idom.has(p));
        if (!ps.length) continue;
        let nw = ps[0];
        for (let j = 1; j < ps.length; j++) nw = meet(ps[j], nw);
        if (idom.get(k) !== nw) { idom.set(k, nw); chg = true; }
      }
    }
    this._idom = idom;
    return idom;
  }
  dom(a, b) {
    const idom = this.idom();
    if (!idom.has(b)) return false;
    while (true) { if (b === a) return true; const nb = idom.get(b); if (nb === b) return false; b = nb; }
  }
  entpreds(hk) {
    const ent = [], back = [];
    for (const [k, lf] of (this.preds.get(hk) || [])) (this.dom(hk, k) ? back : ent).push([k, lf]);
    return [ent, back];
  }
}

function numhdr(n) {
  const c = n.cond;
  if (!(c && c.k === "Bin" && (c.op === "CompareLe" || c.op === "CompareGe")) || !n.then || !n.els) return null;
  const st = n.stmts;
  let a, x, add, cut;
  if (st.length >= 2 && st[st.length - 1].s === "Assign" && isreg(st[st.length - 1].target) && isreg(st[st.length - 1].value)
      && st[st.length - 2].s === "Assign" && isreg(st[st.length - 2].target, st[st.length - 1].value.n)) {
    a = st[st.length - 1].target.n; x = st[st.length - 1].value; add = st[st.length - 2].value; cut = 2;
  } else if (st.length >= 1 && st[st.length - 1].s === "Assign" && isreg(st[st.length - 1].target)) {
    a = st[st.length - 1].target.n; x = { k: "Reg", n: a }; add = st[st.length - 1].value; cut = 1;
  } else return null;
  if (!(add && add.k === "Bin" && add.op === "Add" && isreg(add.a, a) && isreg(add.b, a + 2))) return null;
  if (!(isreg(c.a, x.n) && isreg(c.b, a + 1))) return null;
  const t = n.then, e = n.els;
  if (t.cond != null || e.cond != null || (e.stmts && e.stmts.length) || !(t.outcome && t.outcome.o === "Next") || !(e.outcome && e.outcome.o === "Next")) return null;
  if (t.stmts.length !== 1 || t.stmts[0].s !== "Assign" || !isreg(t.stmts[0].target) || !isreg(t.stmts[0].value, x.n)) return null;
  return { a, v: t.stmts[0].target.n, cut, ge: c.op === "CompareGe", bodykey: ks(t.outcome.key), exitkey: ks(e.outcome.key) };
}

function findpsub(g, pk, leaf, a) {
  const seen = new Set();
  while (true) {
    for (let i = leaf.stmts.length - 1; i >= 0; i--) {
      const s = leaf.stmts[i];
      if (s.s === "Assign" && isreg(s.target, a)) {
        const v = s.value;
        if (v && v.k === "Bin" && v.op === "Sub" && isreg(v.a, a) && isreg(v.b, a + 2)) return { stmts: leaf.stmts, i };
        return null;
      }
      if (s.s === "Assign" && isreg(s.target) && (s.target.n === a + 1 || s.target.n === a + 2)) return null;
      if (s.s !== "Assign") return null;
    }
    const n = g.nodes.get(pk);
    if (!n || n !== leaf || n.stmts.length || seen.has(pk)) return null;
    seen.add(pk);
    const ps = g.preds.get(pk) || [];
    if (ps.length !== 1) return null;
    pk = ps[0][0]; leaf = ps[0][1];
  }
}

function genhdr(n) {
  if (!n.stmts.length || n.stmts[n.stmts.length - 1].s !== "CallStmt" || !n.then || !n.els) return null;
  const call = n.stmts[n.stmts.length - 1];
  if (!isreg(call.fn) || (call.args.tail != null) || call.args.items.length !== 2) return null;
  const a = call.fn.n;
  if (!(isreg(call.args.items[0], a + 1) && isreg(call.args.items[1], a + 2))) return null;
  const c = n.cond;
  if (!(c && c.k === "Bin" && c.op === "CompareNe" && c.a && c.a.k === "TempVal" && c.a.t === call.t && c.a.i === 1 && c.b && c.b.k === "Const" && (c.b.v == null || c.b.v.v == null))) return null;
  const t = n.then, e = n.els;
  if (t.cond != null || e.cond != null || (e.stmts && e.stmts.length) || !(t.outcome && t.outcome.o === "Next") || !(e.outcome && e.outcome.o === "Next")) return null;
  const vars = []; let ctl = false;
  for (const s of t.stmts) {
    if (!(s.s === "Assign" && isreg(s.target) && s.value && s.value.k === "TempVal" && s.value.t === call.t)) return null;
    if (s.target.n === a + 2 && s.value.i === 1 && !ctl) { ctl = true; continue; }
    vars.push([s.target.n, s.value.i]);
  }
  vars.sort((p, q) => p[0] - q[0]);
  const regs = vars.map((p) => p[0]), idxs = vars.map((p) => p[1]);
  const wantr = []; for (let i = 0; i < vars.length; i++) wantr.push(a + 3 + i);
  const wanti = []; for (let i = 0; i < vars.length; i++) wanti.push(i + 1);
  if (!vars.length || JSON.stringify(regs) !== JSON.stringify(wantr) || JSON.stringify(idxs) !== JSON.stringify(wanti)) return null;
  return { a, call, vars, bodykey: ks(t.outcome.key), exitkey: ks(e.outcome.key) };
}

function fusgenhdr(g, bk, n) {
  if (!n.stmts.length || !n.then || !n.els) return null;
  const call = n.stmts[n.stmts.length - 1];
  if (call.s !== "CallStmt" || !call.fn || call.fn.k !== "Pseudo") return null;
  if (!(call.args && call.args.items.length === 0 && call.args.tail == null)) return null;
  const c = n.cond;
  if (!(c && c.k === "TempVal" && c.t === call.t && c.i === 1)) return null;
  const t = n.then, e = n.els;
  if (e.cond != null || (e.stmts && e.stmts.length) || !(e.outcome && e.outcome.o === "Next")) return null;

  const vars = []; let bi = 0;
  while (bi < t.stmts.length && t.stmts[bi].s === "Assign" && t.stmts[bi].target.k === "Reg"
         && t.stmts[bi].value && t.stmts[bi].value.k === "TempVal" && t.stmts[bi].value.t === call.t) {
    vars.push([t.stmts[bi].value.i, t.stmts[bi].target.n]); bi++;
  }
  if (!vars.length) return null;

  for (const [pk] of (g.preds.get(bk) || [])) {
    if (pk === bk) continue;
    for (const s of (g.nodes.get(pk).stmts || [])) {
      if (s.s === "Assign" && s.target.k === "Pseudo" && s.target.name === call.fn.name && s.target.depth === call.fn.depth
          && s.value && s.value.k === "GenIter" && s.value.args && s.value.args.items.length >= 4) {
        const it = s.value.args.items;
        const bodystmt = t.stmts.slice(bi);

        vars.sort((a, b) => a[0] - b[0]);
        return { kind: "generic", fused: true, header: bk, prepkey: pk, gentgt: { name: call.fn.name, depth: call.fn.depth },
          reads3: [it[1], it[2], it[3]], vars: vars.map((v) => v[1]),
          bodynd: { stmts: bodystmt, cond: t.cond || null, then: t.then || null, els: t.els || null, outcome: t.outcome || null },
          exitkey: ks(e.outcome.key) };
      }
    }
  }
  return null;
}

const lvbase = 600000;
function nilcnst(e) { return e && e.k === "Const" && (e.v == null || e.v.v == null); }
function cnstintof(e) { return (e && e.k === "Const" && e.v && (e.v.k === "int" || e.v.k === "float")) ? e.v.v : undefined; }
function plus1(e, ctl) { return e && e.k === "Bin" && e.op === "Add" && isreg(e.a, ctl) && cnstintof(e.b) === 1; }
function ctltest(cond) {
  if (isreg(cond)) return cond.n;
  if (cond && cond.k === "Bin" && cond.op === "CompareNe" && isreg(cond.a) && nilcnst(cond.b)) return cond.a.n;
  return null;
}
function nenilidx(cond, tbl) {
  if (!(cond && cond.k === "Bin" && cond.op === "CompareNe" && nilcnst(cond.b))) return null;
  const ix = cond.a;
  if (!(ix && ix.k === "Index" && isreg(ix.obj) && (tbl === undefined || ix.obj.n === tbl))) return null;
  return [ix.obj.n, ix.key];
}
function mapsub(e, fn) {
  const r = fn(e); if (r !== null && r !== undefined) return r;
  if (!e || typeof e !== "object") return e;
  if (e.k === "Index") return { k: "Index", obj: mapsub(e.obj, fn), key: mapsub(e.key, fn) };
  if (e.k === "Bin") return { k: "Bin", op: e.op, a: mapsub(e.a, fn), b: mapsub(e.b, fn) };
  if (e.k === "Un") return { k: "Un", op: e.op, a: mapsub(e.a, fn) };
  return e;
}
function rslvmv(stmt) {
  const vals = {};
  const sub = (e) => mapsub(e, (x) => (isreg(x) && x.n >= lvbase && (x.n in vals)) ? vals[x.n] : null);
  for (const s of stmt) { if (!(s.s === "Assign" && isreg(s.target))) return null; vals[s.target.n] = sub(s.value); }
  return vals;
}

function fgliphdr(n) {
  if ((n.stmts && n.stmts.length) || n.cond === undefined || !n.then || !n.els) return null;
  const ctl = ctltest(n.cond); if (ctl === null) return null;
  const first = n.els, cont = n.then;
  for (const br of [first, cont]) {
    if ((br.stmts && br.stmts.length) || br.cond === undefined || !br.then || !br.els) return null;
    if ((br.els.stmts && br.els.stmts.length) || !(br.els.outcome && br.els.outcome.o === "Next")
        || !(br.then.outcome && br.then.outcome.o === "Next")) return null;
  }
  const m1 = nenilidx(first.cond); if (!m1 || cnstintof(m1[1]) !== 1) return null;
  const tbl = m1[0];
  const m2 = nenilidx(cont.cond, tbl); if (!m2 || !plus1(m2[1], ctl)) return null;
  const bodyout = first.then.outcome, exitout = first.els.outcome;
  if (ks(cont.then.outcome.key) !== ks(bodyout.key) || ks(cont.els.outcome.key) !== ks(exitout.key)) return null;
  let strt = rslvmv(first.then.stmts), adv = rslvmv(cont.then.stmts);
  if (!strt || !adv) return null;
  const filt = (m) => { const o = {}; for (const r in m) if (+r < lvbase) o[r] = m[r]; return o; };
  strt = filt(strt); adv = filt(adv);
  if (!(ctl in strt) || !(ctl in adv)
      || JSON.stringify(Object.keys(strt).sort()) !== JSON.stringify(Object.keys(adv).sort())) return null;
  if (!(cnstintof(strt[ctl]) === 1 && plus1(adv[ctl], ctl))) return null;
  const vregs = Object.keys(strt).map(Number).filter((r) => r !== ctl).sort((a, b) => a - b);
  if (!vregs.length) return null;
  for (const r of vregs) {
    const sv = strt[r], av = adv[r];
    const isidx = cnstintof(sv) === 1 && plus1(av, ctl);
    const isval = sv && sv.k === "Index" && isreg(sv.obj, tbl) && cnstintof(sv.key) === 1
      && av && av.k === "Index" && isreg(av.obj, tbl) && plus1(av.key, ctl);
    if (!isidx && !isval) return null;
  }
  return { tbl, ctl, varregs: vregs, bodykey: ks(bodyout.key), exitkey: ks(exitout.key) };
}

function hasreg(o, r) { return !!o && typeof o === "object" && ((o.k === "Reg" && o.n === r) || (o.k === "MaybeBox" && o.reg === r) || Object.values(o).some((v) => hasreg(v, r))); }
function boxd(o, bx) {
  if (!o || typeof o !== "object") return bx;
  if (o.k === "MaybeBox") bx.add(o.reg); else if (o.k === "BoxRef" && isreg(o.target)) bx.add(o.target.n);
  for (const v of Object.values(o)) boxd(v, bx);
  return bx;
}
function cstat(g, pk, lf, r, bx, memo = new Map()) {
  for (let i = lf.stmts.length - 1; i >= 0; i--) {
    const s = lf.stmts[i];
    if (s.s !== "Assign" || !isreg(s.target, r) || bx.has(r)) continue;
    if (!isreg(s.value)) { const v = Number(cnstintof(s.value)); return Number.isNaN(v) ? undefined : v; }
    r = s.value.n;
  }
  const key = pk + "|" + r;
  if (bx.has(r) || g.nodes.get(pk) !== lf) return undefined;
  if (memo.has(key)) return memo.get(key);
  memo.set(key, undefined);
  const vs = (g.preds.get(pk) || []).map(([p, l]) => cstat(g, p, l, r, bx, memo));
  const v = vs.length && vs.every((x) => x !== undefined && x === vs[0]) ? vs[0] : undefined;
  memo.set(key, v);
  return v;
}
const nonnum = (v) => v.k === "Const" ? cnstintof(v) === undefined : v.k === "NewTable" || v.k === "ClosureExpr" || (v.k === "Un" && v.op === "Not") || (v.k === "Bin" && /^(Concat|Compare)/.test(v.op));
const pth = (n, l) => n === l ? n.stmts : n && n.cond != null ? ((a) => a && n.stmts.concat(a))(pth(n.then, l) || pth(n.els, l)) : null;
function anyn(g, pk, lf, r, bx, seen = new Set()) {
  const st = pth(g.nodes.get(pk), lf);
  for (let i = st ? st.length - 1 : -1; i >= 0 && !bx.has(r); i--) if (st[i].s === "Assign" && isreg(st[i].target, r)) { if (!isreg(st[i].value)) return nonnum(st[i].value); r = st[i].value.n; }
  if (!st || bx.has(r)) return true;
  if (seen.has(pk + "|" + r)) return false;
  seen.add(pk + "|" + r);
  return (g.preds.get(pk) || []).some(([p, l]) => anyn(g, p, l, r, bx, seen));
}
const sgnt = (c) => c && c.k === "Bin" && (c.op === "CompareGt" || c.op === "CompareLe") && isreg(c.a) && cnstintof(c.b) === 0;
function cnthdr(g, hk, n, liveinat, all) {
  if (n.stmts.length || n.cond == null) return null;
  const [ent, back] = g.entpreds(hk);
  if (ent.length !== 1 || !back.length) return null;
  const [pk, lf] = ent[0], bx = boxd(all, new Set());
  let s = sgnt(n.cond) ? n.cond.a.n : null, sv = s === null ? undefined : cstat(g, pk, lf, s, bx);
  if (s !== null && sv === undefined) return null;
  const nav = (m) => { while (m && s !== null && sgnt(m.cond) && isreg(m.cond.a, s)) m = m.stmts.length ? null : (m.cond.op === "CompareGt") === (sv > 0) ? m.then : m.els; return m; };
  const m = nav(n), c = m && !m.stmts.length && m.cond;
  if (!(c && c.k === "Bin" && (c.op === "CompareLe" || c.op === "CompareGe") && isreg(c.a) && (isreg(c.b) || !Number.isNaN(Number(cnstintof(c.b)))))) return null;
  const ind = c.a.n, lim = isreg(c.b) ? c.b.n : null, drops = new Set();
  for (const [, l] of back) {
    const t = l.stmts[l.stmts.length - 1], v = t && t.s === "Assign" && isreg(t.target, ind) && t.value;
    if (!(v && v.k === "Bin" && v.op === "Add" && isreg(v.a, ind) && isreg(v.b) && (s === null || v.b.n === s))) return null;
    s = v.b.n; drops.add(t);
  }
  if (sv === undefined) sv = cstat(g, pk, lf, s, bx);
  if (sv === undefined || (c.op === "CompareLe") !== (sv > 0) || ind === s || ind === lim || s === lim || [ind, lim, s].some((r) => bx.has(r))) return null;
  if ([ind, lim].some((r) => r !== null && anyn(g, pk, lf, r, bx))) return null;
  const T = nav(m.then), E = nav(m.els);
  if (!T || !E || E.cond != null || !(E.outcome && E.outcome.o === "Next") || ks(E.outcome.key) === hk) return null;
  const ek = ks(E.outcome.key), rg = lpreg(g, hk, back), nds = [];
  let brk = false;
  if (!rg) return null;
  const wn = (x) => { if (!x) return; nds.push(x); if (x.cond != null) { wn(x.then); wn(x.els); } };
  wn(T); for (const k of rg) wn(g.nodes.get(k));
  for (const x of nds) {
    for (const t of x.stmts) if (t.s === "Assign" && [ind, lim, s].some((r) => isreg(t.target, r)) && !drops.has(t)) { if (isreg(t.value, t.target.n)) drops.add(t); else return null; }
    const k = x.cond == null && x.outcome && x.outcome.o === "Next" ? ks(x.outcome.key) : hk;
    if (k !== hk && !rg.has(k)) { if (k !== ek) return null; brk = true; }
  }
  const lv = liveinat(ek);
  if (!lv || lv.has("r" + ind)) return null;
  let i = 0;
  for (; i < E.stmts.length; i++) {
    const t = E.stmts[i];
    if (!(t.s === "Assign" && t.target.k === "Reg" && (isreg(t.value, ind) || nilcnst(t.value)))) break;
    if (lv.has("r" + t.target.n) || bx.has(t.target.n) || E.stmts.slice(i + 1).some((x) => hasreg(x, t.target.n))) return null;
    drops.add(t);
  }
  if ((brk && i < E.stmts.length) || E.stmts.slice(i).some((x) => hasreg(x, ind))) return null;
  return { kind: "numeric", cnt: true, header: hk, ind, lim: c.b, step: s, entout: lf.outcome, bodynd: T, exitnd: E, drops };
}

function lpreg(g, hk, back) {
  const rg = new Set(), wl = back.map(([k]) => k).filter((k) => k !== hk), id = g.idom();
  while (wl.length) { const k = wl.pop(); if (rg.has(k) || !id.has(k)) continue; if (!g.dom(hk, k)) return null; rg.add(k); for (const [p] of g.preds.get(k) || []) if (p !== hk) wl.push(p); }
  return rg;
}

function rdaft(g, k, r, sk, seen = new Set()) {
  if (!g.nodes.has(k) || seen.has(k)) return false;
  seen.add(k);
  const go = (x) => {
    for (const t of x.stmts) { if (sk.has(t)) continue; if (t.s === "Assign" ? hasreg(t.value, r) || (!isreg(t.target) && hasreg(t.target, r)) : hasreg(t, r)) return true; if (t.s === "Assign" && isreg(t.target, r)) return false; }
    return x.cond != null ? hasreg(x.cond, r) || go(x.then) || go(x.els) : x.outcome && x.outcome.o === "Next" ? rdaft(g, ks(x.outcome.key), r, sk, seen) : hasreg(x.outcome, r);
  };
  return go(g.nodes.get(k));
}

function recog(ordr, liveinat, all, sk = new Set()) {
  const g = new Grf(ordr);
  const lps = {}, bx = boxd(all || ordr, new Set());
  for (const { key, node } of ordr) {
    const hk = ks(key);

    let m = numhdr(node);
    if (m) {
      const [ent, back] = g.entpreds(hk);
      if (ent.length === 1 && back.length) {
        const [pk, leaf] = ent[0];
        const fnd = findpsub(g, pk, leaf, m.a), rg = lpreg(g, hk, back);
        const wr = (x) => !!x && (x.stmts.some((t, i) => t.s === "Assign" && isreg(t.target) && t.target.n >= m.a && t.target.n <= m.a + 2 && !(x === node && i >= x.stmts.length - m.cut)) || (x.cond != null && (wr(x.then) || wr(x.els))));
        if (fnd && rg && !wr(node) && ![...rg].some((k) => wr(g.nodes.get(k))) && !rdaft(g, m.exitkey, m.a, sk) && ![0, 1, 2].some((d) => bx.has(m.a + d)) && (!m.ge || cstat(g, pk, leaf, m.a + 2, bx) < 0)) {
          lps[hk] = { kind: "numeric", header: hk, a: m.a, v: m.v, cut: m.cut,
            bodykey: m.bodykey, exitkey: m.exitkey, prepkey: pk, prepstmts: fnd.stmts, prepidx: fnd.i,
            backedges: back.map(([k]) => k) };
          continue;
        }
      }
    }
    m = genhdr(node);
    if (m) {
      const [ent, back] = g.entpreds(hk);
      if (ent.length === 1 && back.length) {
        const [pk] = ent[0];
        lps[hk] = { kind: "generic", header: hk, a: m.a, call: m.call, vars: m.vars,
          bodykey: m.bodykey, exitkey: m.exitkey, prepkey: pk, backedges: back.map(([k]) => k) };
        continue;
      }
    }
    const fg = fusgenhdr(g, hk, node);
    if (fg) { lps[hk] = fg; continue; }
    const cn = cnthdr(g, hk, node, liveinat, all || ordr);
    if (cn) { lps[hk] = cn; continue; }
    const ip = fgliphdr(node);
    if (ip) {
      const [ent, back] = g.entpreds(hk);
      if (ent.length === 1 && back.length) {
        const [pk] = ent[0];
        lps[hk] = { kind: "generic", ipairs: true, header: hk, tbl: ip.tbl, vars: ip.varregs,
          bodykey: ip.bodykey, exitkey: ip.exitkey, prepkey: pk, backedges: back.map(([k]) => k) };
        continue;
      }
    }
  }
  return { graph: g, loops: lps };
}

module.exports = { recog, Grf, boxd, genhdr, numhdr, fgliphdr };

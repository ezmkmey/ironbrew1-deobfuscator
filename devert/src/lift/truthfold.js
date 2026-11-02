"use strict";
function edges(ins) {
  const n = ins.length, succ = [];
  for (let i = 0; i < n; i++) {
    const x = ins[i]; const e = [];
    if (x.kind === "return") {}
    else if (x.kind === "jump") e.push({ to: x.target, edge: "u" });
    else if (x.kind === "branch") { const t = x.inverted ? i + 1 : x.target, f = x.inverted ? x.target : i + 1; e.push({ to: t, edge: "T" }); e.push({ to: f, edge: "F" }); }
    else if (x.kind === "constant") e.push({ to: x.successors[0], edge: "u" });
    else if (x.kind === "iteration_prepare") { e.push({ to: i + 1, edge: "u" }); e.push({ to: x.loop.exit, edge: "u" }); }
    else if (x.kind === "iteration_loop") e.push({ to: x.loop.prepare, edge: "u" });
    else if (i + 1 < n) e.push({ to: i + 1, edge: "u" });
    succ.push(e);
  }
  return succ;
}
function foldfn(ins) {
  const n = ins.length, succ = edges(ins);
  const preds = Array.from({ length: n }, () => []);
  for (let i = 0; i < n; i++) for (const s of succ[i]) if (s.to >= 0 && s.to < n) preds[s.to].push({ from: i, edge: s.edge });
  const refd = new Set();
  for (const x of ins) for (const q of x.references || []) refd.add(q);
  const kof = (k, r) => { const y = ins[k]; return y && y.kind === "constant" && y.writes[0] === r && y.successors[0] === k + 1 ? ("nil_value" in y.value ? "nil" : y.value.boolean === false ? "false" : undefined) : undefined; };
  const dead = (r, from) => {
    if (refd.has(r)) return false;
    const seen = new Set(), st = [...from];
    while (st.length) { const k = st.pop(); if (k < 0 || k >= n || seen.has(k)) continue; seen.add(k); const y = ins[k]; if ((y.reads || []).includes(r) || y.kind === "iteration_prepare" || y.kind === "iteration_loop") return false; if ((y.writes || []).includes(r)) continue; for (const s of succ[k]) st.push(s.to); }
    return true;
  };
  let nf = 0;
  for (let i = 1; i + 2 < n; i++) {
    let k = i + 1;
    for (let g = 0; g < n && k < n && ins[k].kind === "jump" && preds[k].length === 1; g++) k = ins[k].target;
    const x = ins[i], y = ins[k + 1];
    if (!y || x.kind !== "branch" || y.kind !== "branch" || x.operator !== "equal" || y.operator !== "equal" || x.inverted || y.inverted || x.target !== y.target) continue;
    const r = x.reads[0], a = kof(i - 1, x.reads[1]), b = kof(k, y.reads[1]);
    if (y.reads[0] !== r || !a || !b || a === b || x.reads[1] === r || y.reads[1] === r || preds[i].length !== 1 || preds[k].length !== 1 || preds[k + 1].length !== 1) continue;
    if (!dead(y.reads[1], [x.target])) continue;
    ins[i] = { kind: "branch", reads: [r], target: x.target, inverted: true, line_number: x.line_number || 1 };
    ins[k + 1] = { kind: "jump", target: k + 2, reads: [], line_number: y.line_number || 1 };
    nf++;
  }
  if (nf) return nf;
  const dynk = new Set(["call", "namecall", "binary", "unary", "concat", "table_get", "table_set", "environment_get", "environment_set", "iteration_prepare"]);
  const wrof = (x) => { const w = x.writes && x.writes.length ? x.writes.slice() : []; if (x.kind === "iteration_prepare") w.push(...x.loop.variables); if (x.complete && x.constructor && x.constructor.mode === "literal") w.push(x.table); if (dynk.has(x.kind) || (x.kind === "branch" && x.operator)) w.push(...refd); return w; };
  const ent = Array.from({ length: n }, () => null);
  function out(i, inm, edge) {
    const x = ins[i]; const m = new Map(inm);
    const nt = x.kind === "unary" && x.operator === "logical_not";
    if (x.kind === "move" || nt) {
      const a = x.reads[0], b = x.writes[0];
      if (a === b && !nt) return m;
      if (!m.has(a) || m.get(a).c === undefined) {
        const c = "m" + i;
        for (const [k, e] of m) if (e.c === c) { if (e.t === undefined) m.delete(k); else m.set(k, { t: e.t }); }
        m.set(a, { t: m.has(a) ? m.get(a).t : undefined, c });
      }
      const e = m.get(a);
      m.set(b, nt ? { t: e.t === undefined ? undefined : !e.t, c: e.c, n: !e.n } : e);
      return m;
    }
    for (const w of wrof(x)) m.delete(w);
    if (x.kind === "branch" && !x.operator && (edge === "T" || edge === "F")) {
      const r = x.reads[0], t = edge === "T", o = m.get(r), c = o ? o.c : undefined, nr = !!(o && o.n);
      if (o && o.t !== undefined && o.t !== t) return null;
      m.set(r, { t, c, n: o && o.n });
      if (c !== undefined) for (const [k, e] of m) if (e.c === c) m.set(k, { t: (t !== nr) !== !!e.n, c, n: e.n });
    }
    return m;
  }
  function meet(a, b) {
    if (a === null) return new Map(b); if (b === null) return new Map(a);
    const m = new Map();
    for (const [k, v] of a) {
      const w = b.get(k); if (!w) continue;
      const t = v.t === w.t ? v.t : undefined, c = v.c === w.c && !v.n === !w.n ? v.c : undefined;
      if (t !== undefined || c !== undefined) m.set(k, { t, c, n: c === undefined ? undefined : v.n });
    }
    return m;
  }
  ent[0] = new Map(); let chg = true, g = 0;
  while (chg && g++ < 20000) {
    chg = false;
    for (let i = 0; i < n; i++) {
      let m = null; if (i === 0) m = new Map();
      for (const p of preds[i]) { if (ent[p.from] === null) continue; const o = out(p.from, ent[p.from], p.edge); if (o === null) continue; m = m === null ? o : meet(m, o); }
      if (m === null) continue;
      const old = ent[i]; if (old !== null && g > 50) m = meet(old, m);
      if (old === null || old.size !== m.size || [...m].some(([k, v]) => { const o = old.get(k); return !o || o.t !== v.t || o.c !== v.c || !o.n !== !v.n; })) { ent[i] = m; chg = true; }
    }
  }
  if (chg) return 0;
  const live = new Set([0]), st = [0];
  while (st.length) { const i = st.pop(); for (const e of succ[i]) if (e.to >= 0 && e.to < n && !live.has(e.to)) { live.add(e.to); st.push(e.to); } }
  const cyc = (i, j) => { let k = j; for (let s = 0; s <= n && k !== i && k >= 0 && k < n && ins[k].kind === "jump"; s++) k = ins[k].target; return k === i && j !== i; };
  let folds = 0;
  for (let i = 0; i < n; i++) {
    const x = ins[i];
    if (x.kind !== "branch" || x.operator) continue;
    const t = x.inverted ? i + 1 : x.target, f = x.inverted ? x.target : i + 1;
    let to;
    if (ent[i] === null) { if (live.has(i)) to = [i + 1, x.target].find((j) => !cyc(i, j)); }
    else { const e = ent[i].get(x.reads[0]); if (e && e.t !== undefined && !cyc(i, e.t ? t : f)) to = e.t ? t : f; }
    if (to === undefined) continue;
    ins[i] = { kind: "jump", target: to, reads: [], line_number: x.line_number || 1 };
    folds++;
  }
  return folds;
}

function dcefn(ins) {
  const n = ins.length, succ = edges(ins), b = (rs) => (rs || []).reduce((a, r) => a | (1n << BigInt(r)), 0n);
  let cap = 0n, pin = 0n;
  for (const x of ins) { cap |= b(x.references); pin |= x.loop ? b(x.reads) | b(x.loop.variables) : 0n; }
  pin |= cap;
  const kl = ins.map((x) => x.produces_pack_at == null && /^(constant|move|unary|binary|concat|table_get|environment_get|upvalue_get|closure|call|namecall)$/.test(x.kind) && !Object.hasOwn(x, "constructor") ? b(x.writes) : 0n);
  const rd = ins.map((x) => b(x.reads)), li = new Array(n).fill(0n), lo = (i) => succ[i].reduce((a, s) => s.to >= 0 && s.to < n ? a | li[s.to] : a, 0n);
  for (let chg = true; chg;) { chg = false; for (let i = n - 1; i >= 0; i--) { const v = rd[i] | (lo(i) & ~kl[i]); if (v !== li[i]) { li[i] = v; chg = true; } } }
  const rs = (j) => { for (let g = 0; g <= n && j < n && ins[j].kind === "jump"; g++) j = ins[j].target; return j; };
  const pc = new Array(n).fill(0), regs = (z) => { const o = []; for (let r = 0; z; r++, z >>= 1n) if (z & 1n) o.push(r); return o; };
  for (const e of succ) for (const s of e) if (s.to >= 0 && s.to < n) pc[s.to]++;
  const arm = (j) => {
    const m = new Map(), fx = [], v = (r) => m.has(r) ? m.get(r) : "i" + r;
    for (let g = 0; g <= n; g++) {
      if (j >= n || pc[j] !== 1) return { j, v, fx };
      const x = ins[j];
      if (x.kind === "jump") { j = x.target; continue; }
      if (/^(branch|return|iteration|close)/.test(x.kind) || x.produces_pack_at != null || x.consumes_pack_from != null || Object.hasOwn(x, "constructor") || (x.references || []).length || b(x.writes) & cap) return null;
      const a = (x.reads || []).map(v);
      if (x.kind === "constant" || (x.kind === "move" && !(b(x.reads) & cap))) m.set(x.writes[0], x.kind === "move" ? a[0] : Object.is(x.value.number, -0) ? "-0" : JSON.stringify(x.value));
      else { const { reads, writes, line_number, line_numbers, successors, ...o } = x; fx.push([o, a]); (writes || []).forEach((w, q) => m.set(w, "e" + fx.length + "." + q)); }
      j = x.successors ? x.successors[0] : j + 1;
    }
    return null;
  };
  const kc = (i, r) => i > 0 && ins[i - 1].kind === "constant" && ins[i - 1].writes[0] === r && ins[i - 1].successors[0] === i && pc[i] === 1;
  const same = (i, x) => { const A = arm(i + 1), B = arm(x.target); return A && B && A.j === B.j && A.j < n && JSON.stringify(A.fx) === JSON.stringify(B.fx) && regs(li[A.j]).every((r) => A.v(r) === B.v(r)); };
  let nd = 0;
  for (let i = 0; i < n; i++) {
    const x = ins[i], w = x.writes && x.writes.length === 1 ? 1n << BigInt(x.writes[0]) : 0n;
    const pure = /^(constant|move|new_table)$/.test(x.kind) || x.operator === "logical_not";
    if (pure && w && !Object.hasOwn(x, "constructor") && !((pin | lo(i)) & w)) ins[i] = { kind: "jump", target: x.successors ? x.successors[0] : i + 1, reads: [], line_number: 1 };
    else if (x.kind === "branch" && !x.operator && rs(x.target) === rs(i + 1)) ins[i] = { kind: "jump", target: x.target, reads: [], line_number: 1 };
    else if (x.kind === "branch" && (!x.operator || (x.operator === "equal" && x.reads.some((r) => kc(i, r)))) && same(i, x)) ins[i] = { kind: "jump", target: i + 1, reads: [], line_number: 1 };
    else continue;
    nd++;
  }
  return nd;
}

module.exports = { foldfn, dcefn };

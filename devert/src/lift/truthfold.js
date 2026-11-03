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
function latchfn(ins) {
  const byp = new Map();
  for (let i = 0; i < ins.length; i++) if (ins[i].kind === "iteration_loop") { const p = ins[i].loop.prepare; if (!byp.has(p)) byp.set(p, []); byp.get(p).push(i); }
  let nm = 0;
  for (const [p, ls] of byp) {
    if (ls.length < 2 || !ins[p] || ins[p].kind !== "iteration_prepare") continue;
    const ex = ins[p].loop.exit, inl = ls.filter((l) => l > p && l < ex), keep = inl.length ? inl[inl.length - 1] : ls[0];
    for (const l of ls) if (l !== keep) { ins[l] = { kind: "jump", target: keep, reads: [], line_number: ins[l].line_number || 1 }; nm++; }
  }
  return nm;
}
function prepfn(ins) {
  const seen = new Map();
  let nm = 0;
  for (let i = 0; i < ins.length; i++) {
    const x = ins[i];
    if (x.kind !== "iteration_prepare") continue;
    const k = JSON.stringify([x.reads, x.loop.iteration, x.loop.variables]);
    const f = seen.get(k);
    if (f === undefined) { seen.set(k, i); continue; }
    const l = ins.findIndex((y) => y.kind === "iteration_loop" && y.loop.prepare === f);
    if (l < 0) continue;
    ins[i] = { kind: "jump", target: l, reads: [], line_number: x.line_number || 1 };
    for (const y of ins) if (y.kind === "iteration_loop" && y.loop.prepare === i) y.loop.prepare = f;
    nm++;
  }
  return nm;
}
function foldfn(ins) {
  const np = 0;
  if (np) return np;
  const nl = 0;
  if (nl) return nl;
  const n = ins.length, succ = edges(ins);
  const preds = Array.from({ length: n }, () => []);
  for (let i = 0; i < n; i++) for (const s of succ[i]) if (s.to >= 0 && s.to < n) preds[s.to].push({ from: i, edge: s.edge });
  const refd = new Set();
  for (const x of ins) for (const q of x.references || []) refd.add(q);
  const kof = (k, r) => { const y = ins[k]; return y && y.kind === "constant" && y.writes[0] === r && y.successors[0] === k + 1 ? ("nil_value" in y.value ? "nil" : y.value.boolean === false ? "false" : undefined) : undefined; };
  const dead = (r, from) => {
    if (refd.has(r)) return false;
    const seen = new Set(), st = [...from];
    while (st.length) { const k = st.pop(); if (k < 0 || k >= n || seen.has(k)) continue; seen.add(k); const y = ins[k]; if ((y.reads || []).includes(r)) return false; if ((y.writes || []).includes(r) || (y.kind === "iteration_prepare" && y.loop.variables.includes(r))) continue; for (const s of succ[k]) st.push(s.to); }
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
  return folds || cstfn(ins, succ, preds, wrof, cyc) || dupfn(ins);
}

function dupfn(ins) {
  const n = ins.length, succ = edges(ins);
  const preds = Array.from({ length: n }, () => []);
  for (let i = 0; i < n; i++) for (const s of succ[i]) if (s.to >= 0 && s.to < n) preds[s.to].push(i);
  const pure = new Set(["constant", "move", "unary", "binary"]);
  let nd = 0;
  for (let t = 0; t < n; t++) {
    const ps = preds[t];
    if (ps.length < 2 || !ps.every((p) => ins[p].kind === "branch" && ins[p].target === t)) continue;
    let k = t, out = -1;
    for (; k < n && k - t < 4; k++) {
      const y = ins[k];
      if (!pure.has(y.kind) && y.kind !== "jump") break;
      if (k > t && !(preds[k].length === 1 && preds[k][0] === k - 1)) break;
      const s = succ[k][0].to;
      if (y.kind === "jump" || s !== k + 1) { out = s; break; }
    }
    if (out < 0 || out >= n || (out >= t && out <= k)) continue;
    for (const p of ps.slice(1)) {
      const base = ins.length;
      for (let j = t; j <= k; j++) {
        const c = JSON.parse(JSON.stringify(ins[j]));
        if (c.kind === "constant") c.successors = [j < k ? base + (j - t) + 1 : out];
        ins.push(c);
      }
      ins[p].target = base;
      nd++;
    }
  }
  return nd;
}

function shiftidx(ins, pos, d) {
  const b = (v) => (typeof v === "number" && v >= pos ? v + d : v);
  for (const x of ins) {
    if (x.kind === "jump" || x.kind === "branch") x.target = b(x.target);
    else if (x.kind === "constant" && x.successors) x.successors = [b(x.successors[0])];
    else if (x.kind === "iteration_prepare") { x.loop.prepare = b(x.loop.prepare); x.loop.exit = b(x.loop.exit); }
    else if (x.kind === "iteration_loop") x.loop.prepare = b(x.loop.prepare);
    if (Object.prototype.hasOwnProperty.call(x, "constructor") && typeof x.constructor.create === "number") x.constructor.create = b(x.constructor.create);
  }
}
function orhoist(ins) {
  const n = ins.length, succ = edges(ins);
  const preds = Array.from({ length: n }, () => []);
  for (let i = 0; i < n; i++) for (const s of succ[i]) if (s.to >= 0 && s.to < n) preds[s.to].push(i);
  const ctl = new Set(["branch", "jump", "return", "iteration_prepare", "iteration_loop"]);
  const rslv = (k) => { let g = 0; while (k < n && ins[k].kind === "jump" && g++ < n) k = ins[k].target; return k; };
  const plain = (x) => x.kind === "branch" && !x.operator && x.reads.length === 1;
  for (let i = 0; i < n; i++) {
    const x = ins[i];
    if (!plain(x)) continue;
    const te = x.inverted ? i + 1 : x.target, c = x.inverted ? x.target : i + 1;
    if (te === c || c >= n || preds[c].length !== 1 || preds[c][0] !== i) continue;
    const t = rslv(te);
    let k = c;
    while (k < n && !ctl.has(ins[k].kind) && !(ins[k].kind === "constant" && ins[k].successors[0] !== k + 1) && (k === c || (preds[k].length === 1 && preds[k][0] === k - 1))) k++;
    if (k >= n || k === c) continue;
    const y = ins[k];
    if (!plain(y) || y.reads[0] !== x.reads[0] || preds[k].length !== 1 || preds[k][0] !== k - 1) continue;
    const t2 = rslv(y.inverted ? k + 1 : y.target), f2 = rslv(y.inverted ? y.target : k + 1);
    if (t2 !== t || f2 === t) continue;
    if (!x.inverted) { x.target = k; return 1; }
    shiftidx(ins, i + 1, 1);
    ins.splice(i + 1, 0, { kind: "jump", target: c + 1, reads: [], line_number: x.line_number });
    x.target = k + 1; x.inverted = false;
    return 1;
  }
  return 0;
}

function cstfn(ins, succ, preds, wrof, cyc) {
  const n = ins.length;
  const key = (v) => "nil_value" in v ? "nil" : "boolean" in v ? "b" + v.boolean : "number" in v ? (Number.isFinite(v.number) ? "n" + (v.number === 0 ? 0 : v.number) : undefined) : "string" in v && v.string.length <= 64 ? "s" + v.string : undefined;
  const truthy = (k) => k !== "nil" && k !== "bfalse";
  const cmp = (x, m) => { const a = m.get(x.reads[0]), b = m.get(x.reads[1]); return a === undefined || b === undefined ? undefined : (a === b) === (x.operator === "equal"); };
  function out(i, inm) {
    const x = ins[i], m = new Map(inm);
    let k;
    if (x.kind === "constant") k = key(x.value);
    else if (x.kind === "move") k = m.get(x.reads[0]);
    else if (x.kind === "unary" && x.operator === "logical_not") { const a = m.get(x.reads[0]); k = a === undefined ? undefined : "b" + !truthy(a); }
    else if (x.kind === "binary" && (x.operator === "equal" || x.operator === "not_equal")) { const e = cmp(x, m); k = e === undefined ? undefined : "b" + e; }
    for (const w of wrof(x)) m.delete(w);
    if (k !== undefined) m.set(x.writes[0], k);
    return m;
  }
  const meet = (a, b) => { const m = new Map(); for (const [k, v] of a) if (b.get(k) === v) m.set(k, v); return m; };
  const ent = new Array(n).fill(null);
  ent[0] = new Map();
  for (let chg = true, g = 0; chg && g < 20000; g++) {
    chg = false;
    for (let i = 0; i < n; i++) {
      let m = i === 0 ? new Map() : null;
      for (const p of preds[i]) { if (ent[p.from] === null) continue; const o = out(p.from, ent[p.from]); m = m === null ? o : meet(m, o); }
      if (m === null) continue;
      const old = ent[i];
      if (old === null || old.size !== m.size || [...m].some(([k, v]) => old.get(k) !== v)) { ent[i] = m; chg = true; }
    }
  }
  let folds = 0;
  for (let i = 0; i < n; i++) {
    const x = ins[i], m = ent[i];
    if (m === null) continue;
    if (x.kind === "branch" && (x.operator === "equal" || x.operator === "not_equal")) {
      const e = cmp(x, m);
      if (e === undefined) continue;
      const to = e !== !!x.inverted ? x.target : i + 1;
      if (cyc(i, to)) continue;
      ins[i] = { kind: "jump", target: to, reads: [], line_number: x.line_number || 1 };
    } else if (x.kind === "binary" && (x.operator === "equal" || x.operator === "not_equal")) {
      const e = cmp(x, m);
      if (e === undefined) continue;
      ins[i] = { kind: "constant", value: { boolean: e }, reads: [], writes: [x.writes[0]], successors: [i + 1], line_number: x.line_number || 1 };
    } else if (x.kind === "unary" && x.operator === "logical_not" && m.get(x.reads[0]) !== undefined) {
      ins[i] = { kind: "constant", value: { boolean: !truthy(m.get(x.reads[0])) }, reads: [], writes: [x.writes[0]], successors: [i + 1], line_number: x.line_number || 1 };
    } else continue;
    folds++;
  }
  for (let i = 0; i < n; i++) if (ent[i] === null && !(ins[i].kind === "jump" && ins[i].target === i + 1)) { ins[i] = { kind: "jump", target: i + 1, reads: [], line_number: 1 }; folds++; }
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

module.exports = { foldfn, dcefn, orhoist };

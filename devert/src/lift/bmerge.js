"use strict";
function stbl(v) {
  if (Array.isArray(v)) return "[" + v.map(stbl).join(",") + "]";
  if (v && typeof v === "object") return "{" + Object.keys(v).sort().map((k) => JSON.stringify(k) + ":" + stbl(v[k])).join(",") + "}";
  if (typeof v === "number") return Object.is(v, -0) ? "-0" : Number.isNaN(v) ? "nan" : String(v);
  return JSON.stringify(v);
}
function txt(x) {
  const o = {};
  for (const k of Object.keys(x)) if (!/^(line_number|line_numbers|target|successors|loop|constructor)$/.test(k)) o[k] = x[k];
  if (x.loop) o.loop = [x.loop.iteration, x.loop.variables || null];
  if (Object.hasOwn(x, "constructor")) o.constructor = x.constructor.mode;
  return stbl(o);
}
function intern(keys) {
  const m = new Map();
  return keys.map((k) => { if (!m.has(k)) m.set(k, m.size); return m.get(k); });
}
function blocks(ins) {
  const n = ins.length, lead = new Uint8Array(n + 1);
  lead[0] = 1;
  for (let i = 0; i < n; i++) {
    const x = ins[i], k = x.kind;
    if (k === "jump" || k === "branch") { lead[x.target] = 1; lead[i + 1] = 1; }
    else if (k === "return") lead[i + 1] = 1;
    else if (k === "constant") { if (x.successors[0] !== i + 1) { lead[x.successors[0]] = 1; lead[i + 1] = 1; } }
    else if (k === "iteration_prepare") { lead[i] = 1; lead[i + 1] = 1; lead[x.loop.exit] = 1; }
    else if (k === "iteration_loop") { lead[i + 1] = 1; lead[x.loop.prepare] = 1; }
  }
  const start = [], bof = new Int32Array(n);
  for (let i = 0; i < n; i++) { if (lead[i]) start.push(i); bof[i] = start.length - 1; }
  return { start, bof };
}
function part(ins) {
  const n = ins.length;
  const { start, bof } = blocks(ins), nb = start.length;
  const end = (b) => (b + 1 < nb ? start[b + 1] : n);
  const edges = [], crts = [], texts = [];
  for (let b = 0; b < nb; b++) {
    const e = end(b) - 1, x = ins[e], k = x.kind;
    edges.push(k === "jump" ? [x.target] : k === "branch" ? [x.target, e + 1] : k === "return" ? [] : k === "constant" ? [x.successors[0]] : k === "iteration_prepare" ? [e + 1, x.loop.exit] : k === "iteration_loop" ? [x.loop.prepare] : [e + 1]);
    const cr = [], tx = [];
    for (let i = start[b]; i <= e; i++) { tx.push(txt(ins[i])); if (Object.hasOwn(ins[i], "constructor") && typeof ins[i].constructor.create === "number") cr.push(ins[i].constructor.create); }
    crts.push(cr); texts.push(tx.join(";"));
  }
  const tag = (t) => (t >= 0 && t < n ? bof[t] : -1);
  const one = (b) => end(b) - start[b] === 1 && ins[start[b]].kind === "jump";
  const thr = (t) => { for (let g = 0; g < nb && tag(t) >= 0 && one(tag(t)); g++) t = ins[t].target; return t; };
  for (let b = 0; b < nb; b++) if (one(b) || ins[end(b) - 1].kind === "return") texts[b] = "one#" + b;
  let cls = intern(texts), cnt = new Set(cls).size;
  for (;;) {
    const keys = [];
    for (let b = 0; b < nb; b++) keys.push(cls[b] + "|" + edges[b].map(thr).map((t) => (tag(t) < 0 ? "x" : cls[tag(t)])).join(",") + "|" + crts[b].map((c) => (tag(c) < 0 ? "x" : cls[bof[c]] + ":" + (c - start[bof[c]]))).join(","));
    const nc = intern(keys), m = new Set(nc).size;
    cls = nc;
    if (m === cnt) break;
    cnt = m;
  }
  return { start, bof, nb, cls, cnt, end };
}
function mrgfn(ins) {
  const n = ins.length;
  if (!n) return 0;
  const { start, bof, nb, cls, cnt, end } = part(ins);
  if (cnt === nb) return 0;
  const rep = new Map();
  for (let b = 0; b < nb; b++) if (!rep.has(cls[b])) rep.set(cls[b], b);
  const rb = (b) => rep.get(cls[b]);
  const kept = [];
  for (let b = 0; b < nb; b++) if (rb(b) === b) kept.push(b);
  const nstart = new Map(), out = [];
  for (let q = 0; q < kept.length; q++) {
    const b = kept[q];
    nstart.set(b, out.length);
    for (let i = start[b]; i < end(b); i++) out.push(ins[i]);
    const k = ins[end(b) - 1].kind, t = end(b);
    if (k === "jump" || k === "return" || k === "constant" || k === "iteration_loop" || t >= n) continue;
    if (rb(bof[t]) !== (q + 1 < kept.length ? kept[q + 1] : -1)) out.push({ kind: "jump", target: t, reads: [], line_number: 1 });
  }
  const nidx = (o) => (o >= n ? out.length : nstart.get(rb(bof[o])) + (o - start[bof[o]]));
  for (const x of out) {
    if (x.kind === "jump" || x.kind === "branch") x.target = nidx(x.target);
    else if (x.kind === "constant" && x.successors) x.successors = [nidx(x.successors[0])];
    else if (x.kind === "iteration_prepare") { x.loop.prepare = nidx(x.loop.prepare); x.loop.exit = nidx(x.loop.exit); }
    else if (x.kind === "iteration_loop") x.loop.prepare = nidx(x.loop.prepare);
    if (Object.hasOwn(x, "constructor") && typeof x.constructor.create === "number") x.constructor.create = nidx(x.constructor.create);
  }
  ins.length = 0;
  for (const x of out) ins.push(x);
  return nb - kept.length;
}
module.exports = { mrgfn, part };

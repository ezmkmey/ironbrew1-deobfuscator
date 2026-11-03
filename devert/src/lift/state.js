"use strict";
const crypto = require("crypto");
const sym = require("./sym.js");
const dvl = require("./dval.js");
const { _kval, _multik, repr, Stor, tktop, tktab, tkiter, tkloc, tkovl } = dvl;

const ovlrs = new WeakMap();
function _ovlrep(e) {
  let v = e.v; if (v instanceof Stor) v = v.const;
  if (v === undefined) v = null;
  const c = ovlrs.get(e);
  if (c !== undefined && Object.is(c.v, v)) return c;
  const scal = v === null || typeof v === "boolean" || typeof v === "bigint" || typeof v === "number";
  if (!scal && !sym.isby(v)) return null;
  const slot = e.slot;
  const r = { v, s: "('ovl', " + String(slot[1]) + ", " + repr(slot[2]) + ")", r: repr(v), t: tkovl(slot[1], slot[2]) };
  if (scal) ovlrs.set(e, r);
  return r;
}

function _vmmem(fcts, live) {
  const out = [];
  for (const e of fcts.values()) {
    const slot = e.slot;
    if (!Array.isArray(slot) || slot[0] !== "ovl") continue;
    const r = _ovlrep(e);
    if (r !== null && (live === null || live.has(r.t))) out.push(r);
  }
  out.sort((a, b) => (a.s < b.s ? -1 : a.s > b.s ? 1 : (a.r < b.r ? -1 : a.r > b.r ? 1 : 0)));
  return out;
}

class St {
  constructor(pc, vals, tabs, bxs, top, itrs, fcts, lost, sub, live) {
    this.pc = pc; this.vals = vals; this.tabs = tabs; this.boxes = bxs; this.top = top;
    this.iters = itrs; this.facts = fcts; this.lost = lost;
    this.sub = sub === undefined ? null : sub;
    this.live = live === undefined ? null : live;
    this._key = null; this.dead = false;
  }

  keytpl() {
    const live = this.live !== null ? (this.live.get(this.pc) || null) : null;
    const valst = [];
    for (const [k, v] of this.vals) if (live === null || live.has(tkloc(k))) valst.push([k, _kval(v)]);
    const tabst = [];
    for (const [t, h] of this.tabs) {
      const inr = [];
      for (const e of h.values()) { const k = e.kk, v = e.v; if (live === null || live.has(tktab(t, k))) inr.push([repr(k), _kval(v)]); }
      inr.sort((a, b) => (a[0] < b[0] ? -1 : a[0] > b[0] ? 1 : 0));
      tabst.push([t, inr]);
    }
    const bxst = [];
    for (const [r, v] of this.boxes) bxst.push([BigInt(r), _kval(v)]);
    bxst.sort((a, b) => (a[0] < b[0] ? -1 : a[0] > b[0] ? 1 : 0));
    let topt = null;
    if (!(this.top === null || (live !== null && !live.has(tktop)))) topt = [this.top[0], _multik(this.top[1])];
    const itrst = [];
    for (const [r, v] of this.iters) if (live === null || live.has(tkiter(r))) itrst.push([BigInt(r), _kval(v)]);
    itrst.sort((a, b) => (a[0] < b[0] ? -1 : a[0] > b[0] ? 1 : 0));
    const vm = _vmmem(this.facts, live);
    return [0n, this.pc, valst, tabst, bxst, topt, itrst, this.sub, vm];
  }

  key() {
    if (this._key === null) {
      const tp = this.keytpl();
      const vm = tp.pop();
      const s = repr(tp);
      const prt = [s.length + ":" + s];
      for (const r of vm) prt.push(r.s.length + ":" + r.s + r.r.length + ":" + r.r);
      this._key = crypto.createHash("sha256").update(prt.join(""), "utf16le").digest("hex");
    }
    return this._key;
  }
}

module.exports = { St };

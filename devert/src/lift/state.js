"use strict";
const sym = require("./sym.js");
const dvl = require("./dval.js");
const { _kval, _multik, repr, Stor, tktop, tktab, tkiter, tkloc, tkovl } = dvl;

function _vmmem(fcts, live) {
  const out = [];
  for (const e of fcts.values()) {
    const slot = e.slot;
    if (Array.isArray(slot) && slot[0] === "ovl" && (live === null || live.has(tkovl(slot[1], slot[2])))) {
      let v = e.v; if (v instanceof Stor) v = v.const;
      if (v === null || v === undefined || typeof v === "boolean" || typeof v === "bigint" || typeof v === "number" || sym.isby(v)) {
        const slotrepr = "('ovl', " + String(slot[1]) + ", " + repr(slot[2]) + ")";
        out.push([slotrepr, repr(v === undefined ? null : v)]);
      }
    }
  }
  out.sort((a, b) => (a[0] < b[0] ? -1 : a[0] > b[0] ? 1 : (a[1] < b[1] ? -1 : a[1] > b[1] ? 1 : 0)));
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
    const live = this.live !== null ? (this.live.get(this.pc) || new Set()) : null;
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
    if (this._key === null) this._key = repr(this.keytpl());
    return this._key;
  }
}

module.exports = { St };

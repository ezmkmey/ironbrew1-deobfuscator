"use strict";
const sym = require("./sym.js");
const ir = require("./ir.js");
const dvl = require("./dval.js");
const { LTbl, Bltn } = sym;
const { FnRef, KGlob, env, vcls, hsetraw } = dvl;

function fhex(h) { return Buffer.from(h, "hex"); }

class Dump {
  constructor(d, fns) {
    this.funcs = fns || {};
    this.strings = (d.strings || []).map(fhex);
    const raw = d.tables;

    const envmt = new Set();
    for (const tid of Object.keys(raw)) {
      for (const [k, v] of raw[tid].e) {
        if (k && typeof k === "object" && k.s === "5f5f696e646578" && v && typeof v === "object" && v.env) envmt.add(parseInt(tid, 10));
      }
    }
    this.envtids = new Set();
    for (const tid of Object.keys(raw)) {
      const mt = raw[tid].mt;
      if (mt && typeof mt === "object" && envmt.has(mt.t)) this.envtids.add(parseInt(tid, 10));
    }
    this.tables = new Map();
    for (const tid of Object.keys(raw)) this.tables.set(parseInt(tid, 10), new LTbl(undefined, parseInt(tid, 10)));
    for (const tid of Object.keys(raw)) {
      const lt = this.tables.get(parseInt(tid, 10));
      for (const [k, v] of raw[tid].e) {
        let kk = this.val(k);
        if (typeof kk === "number" && kk === Math.trunc(kk) && Number.isFinite(kk)) kk = BigInt(kk);
        hsetraw(lt, kk, this.val(v));
      }
    }
    this.envvals = new Map();
    this._envvalitms = [];
    for (const tid of this.envtids) {
      for (const [k, v] of dvl.hitems(this.tables.get(tid))) {
        const ks = sym.kstr(sym.nmkey(k));
        if (!this.envvals.has(ks)) { this.envvals.set(ks, v); this._envvalitms.push([k, v]); }
      }
    }
    this.caps = [];
    this.prxflds = new Map();
    for (const c of d.caps) {
      this.caps.push({
        mk: c.mk,
        params: (c.params || []).map((x) => this.val(x)),
        vars: this._valmap(c.vars),
        order: c.order,
      });
      for (const px of (c.proxies || [])) {
        const pt = this.val(px.t);
        const flds = new Map();
        for (const [k, t] of px.map) {
          const kv = this.val(k), tv = this.val(t);
          if (tv instanceof LTbl) flds.set(sym.kstr(sym.nmkey(kv)), tv);
        }
        if (pt instanceof LTbl && flds.size) this.prxflds.set(pt, flds);
      }
    }
    this.skip = null;
    if (d.skip) {
      const t = this.val(d.skip.t);
      const ci = this.caps.findIndex((c) => [...c.vars.values()].includes(t));
      if (t instanceof LTbl && ci >= 0) this.skip = { ci, pc: BigInt(d.skip.pc) };
    }
    this.capof = new Map();
    this.capoftid = new Map();
    for (let i = 0; i < this.caps.length; i++) {
      const p = this.caps[i].params[0];
      if (p instanceof LTbl) {
        if (!this.capof.has(p)) this.capof.set(p, i);
        if (p.tid !== null && !this.capoftid.has(p.tid)) this.capoftid.set(p.tid, i);
      }
    }
    this.pccap = new Map();
    for (const [k, v] of Object.entries(d.pcproto || {})) {
      const tid = (v && typeof v === "object") ? v.t : undefined;
      const ci = tid !== undefined ? this.capoftid.get(tid) : undefined;
      if (ci !== undefined) this.pccap.set(parseInt(k, 10), ci);
    }
    this.cntcap = new Map();
    for (const [k, v] of Object.entries(d.countproto || {})) {
      const tid = (v && typeof v === "object") ? v.t : undefined;
      const ci = tid !== undefined ? this.capoftid.get(tid) : undefined;
      if (ci !== undefined) this.cntcap.set(parseInt(k, 10), ci);
    }
  }

  _valmap(obj) {
    const m = new Map();
    for (const [k, v] of Object.entries(obj || {})) m.set(k, this.val(v));
    return m;
  }

  val(v) {
    if (v === null || v === undefined) return null;
    const t = typeof v;
    if (t === "boolean") return v;
    if (t === "number") return Number.isInteger(v) ? BigInt(v) : v;
    if (t === "object") {
      if ("t" in v) {
        if (this.envtids.has(v.t)) return env;
        return this.tables.get(v.t);
      }
      if ("s" in v) return fhex(v.s);
      if ("S" in v) return this.strings[v.S - 1];
      if ("n" in v) return v.n === "nan" ? NaN : v.n === "inf" ? Infinity : -Infinity;
      if ("f" in v) {
        let up = v.up;
        up = up ? this._valmap(up) : null;
        return new FnRef(v.f, this.funcs[v.f], up);
      }
      if ("c" in v) return v.c === "?" ? vcls : new Bltn(v.c);
      if ("g" in v) return new KGlob(v.g);
      if (v.env) return env;
      if ("v" in v) return ir.Vec(v.v.map((x) => (typeof x === "number" ? x : Number(x))));
      if ("b" in v) return new sym.Buf(fhex(v.b));
      if ("u" in v) return ir.Opq(v.u, "nil --[[ " + v.u + " ]]");
    }
    throw new sym.Unsup("dump val " + JSON.stringify(v));
  }
}

module.exports = { Dump };

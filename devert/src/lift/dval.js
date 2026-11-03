"use strict";
const sym = require("./sym.js");
const ir = require("./ir.js");
const { LTbl, Bin, Multi, Const, EnvTbl, RegF, Bltn, LFn, Buf,
  issym, isby, nmkey, kstr } = sym;

const sbase = 1000000, obase = 800000, lbase = 900000, hbase = 700000;
const lvbase = 600000, bbase = 500000, snbase = 400000;
const mst = 60000, pslk = 4, mrst = 64, cmod = 2147483629n;

function hks(k) { return kstr(nmkey(k)); }
function hhas(t, k) { return t.h.has(hks(k)); }
function hgetd(t, k, dflt) { const r = t.h.get(hks(k)); return r === undefined ? dflt : r.v; }
function hget(t, k) { return hgetd(t, k, null); }
function hsetraw(t, k, v) { const ks = hks(k); const e = t.h.get(ks); if (e !== undefined) { e.v = v; } else t.h.set(ks, { kk: nmkey(k), v }); }
function hdel(t, k) { t.h.delete(hks(k)); }
function hitems(t) { const o = []; for (const e of t.h.values()) o.push([e.kk, e.v]); return o; }
function hkeys(t) { const o = []; for (const e of t.h.values()) o.push(e.kk); return o; }
function hclr(t) { t.h = new Map(); }

function tkloc(k) { return "L:" + k; }
function tkiter(r) { return "iter:" + r; }
const tktop = "top";
function tktab(tid, k) { return "tab:" + tid + ":" + kstr(nmkey(k)); }
function tkovl(tid, k) { return "ovl:" + tid + ":" + kstr(nmkey(k)); }

class FnRef { constructor(loc, node, up) { this.loc = loc; this.node = node; this.up = up || null; } }
class Stor { constructor(expr, kon) { this.expr = expr; this.const = kon; } }
function _unsto(v) { return v instanceof Stor ? v.const : v; }
class InsPrx { constructor(flds, pc) { this.fields = flds; this.pc = pc; } }
class BoxTbl extends LTbl {}
class KGlob { constructor(name) { this.k = "Global"; this.name = name; this.known = true; } }
class Lin { constructor(c, tail) { this.k = "Lin"; this.c = c; this.tail = tail; }
  asexpr() { const tc = sym.TailCnt(this.tail); return this.c === 0n ? tc : Bin("Add", tc, Const(this.c)); } }
class SprIdx { constructor(strt) { this.k = "SpreadIdx"; this.start = strt; } }
class Spr { constructor(m) { this.m = m; } }
class BoxRef { constructor(tgt) { this.target = tgt; } }
class MbBox { constructor(reg) { this.reg = reg; } }
class UpLst { constructor(kinds) { this.kinds = kinds || {}; } }
class VmCls {}
class GtrProto { constructor(n) { this.n = n; } }
class GiRef { constructor(args) { this.args = args; } }
class ChkRes { constructor(i) { this.i = i; } }

const vcls = new VmCls();
const env = new EnvTbl();
const vglob = new LTbl(undefined, "VMG");
const nfold = { _nofold: true };
const trt = { _s: "TRUTHY" };
const bool = { _s: "BOOL" };
const taint = { _s: "TAINT" };
const tblid = { _s: "TBLID" };
class _Lost { constructor(reg) { this.reg = reg; }
  fail() { throw new sym.Unsup("register " + preprreg(this.reg) + " lost its VM value at a merge"); } }
function preprreg(r) { return typeof r === "bigint" ? r.toString() : repr(r); }

function clzrepr(v) {
  if (v instanceof FnRef) return "Fn@" + v.loc;
  if (v instanceof Stor) return "Stored(" + repr(v.const) + ")";
  if (v instanceof InsPrx) return "InsProxy(" + repr(v.pc) + ")";
  if (v instanceof Lin) return "Lin(" + v.c + "," + ir.fmttail(v.tail) + ")";
  if (v instanceof SprIdx) return "SpreadIdx(" + v.start + ")";
  if (v instanceof Spr) return "Spread(" + ir.fmtmulti(v.m) + ")";
  if (v instanceof BoxRef) return "Box(" + ir.fmtexpr(v.target) + ")";
  if (v instanceof MbBox) return "box r" + v.reg;
  if (v instanceof UpLst) return "UpList";
  if (v instanceof VmCls) return "VMClosure";
  if (v instanceof GtrProto) return "GetterProto(" + v.n + ")";
  if (v instanceof ChkRes) return "CheckResult(" + v.i + ")";
  if (v instanceof _Lost) return "LOST(" + preprreg(v.reg) + ")";
  return null;
}

function srepr(s) {
  const hass = s.indexOf("'") !== -1, hasd = s.indexOf('"') !== -1;
  const q = (hass && !hasd) ? '"' : "'";
  let r = "";
  for (const ch of s) {
    const c = ch.codePointAt(0);
    if (ch === "\\") r += "\\\\";
    else if (ch === q) r += "\\" + q;
    else if (ch === "\n") r += "\\n";
    else if (ch === "\r") r += "\\r";
    else if (ch === "\t") r += "\\t";
    else if (c < 32 || c === 127) r += "\\x" + c.toString(16).padStart(2, "0");
    else r += ch;
  }
  return q + r + q;
}
function brepr(b) {
  const hass = b.includes(0x27), hasd = b.includes(0x22);
  const q = (hass && !hasd) ? 0x22 : 0x27; const qc = String.fromCharCode(q);
  let r = "";
  for (const c of b) {
    if (c === 0x5c) r += "\\\\";
    else if (c === q) r += "\\" + qc;
    else if (c === 9) r += "\\t";
    else if (c === 10) r += "\\n";
    else if (c === 13) r += "\\r";
    else if (c >= 32 && c < 127) r += String.fromCharCode(c);
    else r += "\\x" + c.toString(16).padStart(2, "0");
  }
  return "b" + qc + r + qc;
}
function frepr(v) {
  if (Number.isNaN(v)) return "nan";
  if (v === Infinity) return "inf";
  if (v === -Infinity) return "-inf";
  if (Number.isInteger(v)) {
    if (Object.is(v, -0)) return "-0.0";
    if (Math.abs(v) < 1e16) return v.toString() + ".0";
  }
  let s = v.toString();

  s = s.replace(/e([+-])(\d)$/, "e$10$2");
  return s;
}
function repr(v) {
  if (v === null || v === undefined) return "None";
  if (v === true) return "True";
  if (v === false) return "False";
  if (typeof v === "bigint") return v.toString();
  if (typeof v === "number") return frepr(v);
  if (typeof v === "string") return srepr(v);
  if (isby(v)) return brepr(v);
  if (Array.isArray(v)) {
    if (v.length === 0) return "()";
    if (v.length === 1) return "(" + repr(v[0]) + ",)";
    return "(" + v.map(repr).join(", ") + ")";
  }
  if (v === trt) return "TRUTHY";
  if (v === bool) return "BOOL";
  if (v === taint) return "TAINT";
  if (v === tblid) return "TBLID";
  if (v === vglob) return objrepr(v);
  const cr = clzrepr(v);
  if (cr !== null) return cr;
  if (issym(v)) return ir.fmtexpr(v);
  return objrepr(v);
}

let _addr = 0; const _addrmap = new WeakMap();
function objrepr(v) {
  let a = _addrmap.get(v); if (a === undefined) { a = (++_addr); _addrmap.set(v, a); }
  const name = clzname(v);
  return "<" + name + " object at 0x" + a.toString(16).toUpperCase().padStart(16, "0") + ">";
}
function clzname(v) {
  if (v instanceof LFn) return "luasym.LuaFunc";
  if (v instanceof RegF) return "luasym.RegFile";
  if (v instanceof LTbl) return "luasym.LTable";
  if (v instanceof Bltn) return "luasym.Builtin";
  if (v instanceof EnvTbl) return "luasym.EnvTable";
  if (v instanceof Buf) return "luasym.Buf";
  return "object";
}

let _objid = 0; const _objids = new WeakMap();
function objn(v) { let i = _objids.get(v); if (i === undefined) { i = (++_objid); _objids.set(v, i); } return "obj" + i; }

function _multik(m) {
  const t = m.tail;
  return [BigInt(m.items.length),
    t === null || t === undefined ? null : (t.k === "TempTail" ? "call" : ir.fmttail(t))];
}

function _kval(v, open) {
  if (v === null || v === undefined) return null;
  const t = typeof v;
  if (t === "boolean" || t === "bigint" || t === "number" || t === "string") return v;
  if (isby(v)) return v;
  if (v instanceof Lin) return ["Lin", v.c, _multik(Multi([], v.tail))];
  if (v instanceof SprIdx) return repr(v);
  if (issym(v)) return "E:" + ir.fmtexpr(v);
  if (v instanceof Stor) return "Stored(" + fmtkv(_kval(v.const, open)) + ")";
  if (v instanceof Spr) return ["Spread", _multik(v.m)];
  if (v instanceof BoxRef || v instanceof FnRef || v instanceof UpLst) return clzrepr(v);
  if (v instanceof LTbl && v.tid === null && !v.fixed) {
    open = open || [];
    for (let i = 0; i < open.length; i++) if (open[i] === v) {
      let idx = 0; for (let j = open.length - 1; j >= 0; j--, idx++) if (open[j] === v) return "^" + idx;
    }
    open.push(v);
    try {
      const prts = [];
      for (const [k, x] of hitems(v)) {
        if (k === tblid || k === taint) continue;
        const ks = (k instanceof LTbl) ? fmtkv(_kval(k, open)) : repr(k);
        prts.push(ks + "=" + fmtkv(_kval(x, open)));
      }
      prts.sort();
      return "{" + prts.join(",") + "}";
    } finally { open.pop(); }
  }
  if (v instanceof LTbl || v instanceof RegF || (v && v.k === "SymList") || (v && v.k === "Multi") || v instanceof GiRef) return objn(v);
  return repr(v);
}

function fmtkv(kv) {
  if (kv === null || kv === undefined) return "None";
  if (typeof kv === "string") return kv;
  if (typeof kv === "boolean") return kv ? "True" : "False";
  if (typeof kv === "bigint") return kv.toString();
  if (typeof kv === "number") return frepr(kv);
  if (isby(kv)) return brepr(kv);
  if (Array.isArray(kv)) return repr(kv);
  return String(kv);
}

function _cpfresh(v, memo) {
  if (!(v instanceof LTbl) || v.tid !== null) return v;
  let c = memo.get(v);
  if (c === undefined) {
    c = (v instanceof BoxTbl) ? new BoxTbl() : new LTbl();
    memo.set(v, c);
    c.h = new Map();
    for (const e of v.h.values()) {
      const nk = _cpfresh(e.kk, memo), nv = _cpfresh(e.v, memo);
      c.h.set(kstr(nmkey(nk)), { kk: nmkey(nk), v: nv });
    }
    if (v.fixed) c.fixed = v.fixed;
  }
  return c;
}

function _isphan(v) {
  return (v instanceof FnRef || v instanceof Bltn || v instanceof VmCls ||
    v instanceof UpLst || v instanceof InsPrx) || (v instanceof LTbl && v.tid !== null);
}

function _samefact(a, b) {
  if (a === b) return true;
  if (a instanceof ChkRes || b instanceof ChkRes) return (a instanceof ChkRes) && (b instanceof ChkRes) && a.i === b.i;
  if (a instanceof InsPrx || b instanceof InsPrx) return (a instanceof InsPrx) && (b instanceof InsPrx) && a.fields === b.fields && a.pc === b.pc;
  if (a instanceof LTbl && b instanceof LTbl && a.tid === null && b.tid === null) return keyvaleq(_kval(a), _kval(b));
  const sametype = (x, y) => x.constructor === y.constructor;
  if (!(a && b && typeof a === "object" && typeof b === "object" && sametype(a, b)) ||
    a instanceof LTbl || a instanceof FnRef || a instanceof Bltn || a instanceof UpLst) {
    return (a instanceof FnRef) && (b instanceof FnRef) && a.loc === b.loc;
  }
  if (a instanceof Stor) return _samefact(a.expr, b.expr) && _samefact(a.const, b.const);
  if (issym(a)) return ir.fmtexpr(a) === ir.fmtexpr(b);
  return sym.leq(a, b) && !(typeof a === "number" && Number.isNaN(a));
}
const fbnd = 24;
class Fcts {
  constructor(nil, m, gone, ng, par) {
    this.nil = nil === undefined ? new Map() : nil;
    this.m = m === undefined ? new Map() : m;
    this.gone = gone === undefined ? new Uint8Array(0) : gone;
    this.ng = ng === undefined ? 0 : ng;
    this.par = par === undefined ? null : par;
    this.tomb = null;
    this.fresh = null;
    this.xn = this.par === null ? this.m.size : this.par.xn;
    this.dep = this.par === null ? 0 : this.par.dep + 1;
    this.gsh = this.par !== null;
    if (this.par !== null) this.par.gsh = true;
  }
  isgone(s) { return (this.gone[s >> 3] >> (s & 7)) & 1; }
  _gown() { if (this.gsh) { this.gone = this.gone.slice(); this.gsh = false; } }
  mkgone(s) { if (!this.isgone(s)) { this._gown(); this.gone[s >> 3] |= 1 << (s & 7); this.ng += 1; } }
  ungone(s) { if (this.isgone(s)) { this._gown(); this.gone[s >> 3] &= ~(1 << (s & 7)); this.ng -= 1; } }
  _x(fk) {
    for (let f = this; f !== null; f = f.par) {
      const r = f.m.get(fk);
      if (r !== undefined) return r;
      if (f.tomb !== null && f.tomb.has(fk)) return undefined;
    }
    return undefined;
  }
  get(fk) {
    const r = this._x(fk);
    if (r !== undefined) return r;
    const e = this.nil.get(fk);
    return e === undefined || this.isgone(e.slot) ? undefined : e;
  }
  has(fk) { return this.get(fk) !== undefined; }
  _xset(fk, e) {
    if (this.m.has(fk)) { this.m.set(fk, e); return; }
    if (this.par === null) { this.xn += 1; this.m.set(fk, e); return; }
    if (this.tomb !== null && this.tomb.has(fk)) this.tomb.delete(fk);
    else {
      const p = this.par._x(fk);
      if (p === e) return;
      if (p !== undefined) { this.m.set(fk, e); return; }
    }
    if (this.fresh === null) this.fresh = new Set();
    this.fresh.add(fk); this.xn += 1; this.m.set(fk, e);
  }
  _xdel(fk) {
    if (this.par === null) { if (this.m.delete(fk)) this.xn -= 1; return; }
    if (this.m.has(fk)) {
      this.m.delete(fk); this.xn -= 1;
      if (this.fresh !== null && this.fresh.delete(fk) && this.par._x(fk) === undefined) return;
    } else if (this.tomb !== null && this.tomb.has(fk)) return;
    else if (this.par._x(fk) === undefined) return;
    else this.xn -= 1;
    if (this.tomb === null) this.tomb = new Set();
    this.tomb.add(fk);
  }
  set(fk, e) {
    const n = this.nil.get(fk);
    if (n === undefined) { this._xset(fk, e); return; }
    if (e.v === null) { this._xdel(fk); this.ungone(n.slot); return; }
    this._xset(fk, e); this.mkgone(n.slot);
  }
  delete(fk) { this._xdel(fk); const n = this.nil.get(fk); if (n !== undefined) this.mkgone(n.slot); }
  get size() { return this.xn + this.nil.size - this.ng; }
  pairs() {
    if (this.par === null) return [...this.m];
    const lys = []; for (let f = this; f !== null; f = f.par) lys.push(f);
    const eff = new Map(), pos = new Set(), win = [];
    for (const f of lys) {
      const w = [];
      for (const [fk, e] of f.m) {
        if (!eff.has(fk)) eff.set(fk, e);
        if (!pos.has(fk) && (f.par === null || (f.fresh !== null && f.fresh.has(fk)))) { pos.add(fk); w.push(fk); }
      }
      if (f.tomb !== null) for (const fk of f.tomb) if (!eff.has(fk)) eff.set(fk, null);
      win.push(w);
    }
    const out = [];
    for (let i = win.length - 1; i >= 0; i--) for (const fk of win[i]) { const e = eff.get(fk); if (e !== null) out.push([fk, e]); }
    return out;
  }
  values() { return this.pairs().map((p) => p[1]); }
  keys() { return this.pairs().map((p) => p[0]); }
  flat() { const f = new Fcts(this.nil, new Map(this.pairs()), this.gone, this.ng); f.gsh = true; this.gsh = true; return f; }
  child() { const p = this.dep >= fbnd ? this.flat() : this; return new Fcts(p.nil, new Map(), p.gone, p.ng, p); }
  copy() {
    if (this.par !== null && this.m.size === 0 && (this.tomb === null || this.tomb.size === 0) && this.gone === this.par.gone) return this.par;
    let f;
    if (this.dep >= fbnd) f = this.flat();
    else { f = new Fcts(this.nil, this.m, this.gone, this.ng, this.par); f.tomb = this.tomb; f.fresh = this.fresh; f.xn = this.xn; f.gsh = true; }
    this.m = new Map(); this.tomb = null; this.fresh = null; this.par = f; this.dep = f.dep + 1; this.gsh = true;
    return f;
  }
}
function keyvaleq(x, y) {
  if (x === y) return true;
  if (typeof x === "bigint" || typeof y === "bigint") return x === y;
  if (isby(x) && isby(y)) return x.equals(y);
  if (Array.isArray(x) && Array.isArray(y)) return x.length === y.length && x.every((e, i) => keyvaleq(e, y[i]));
  return x === y;
}
function _tbleq1(f, p, inv, ok) {
  const a = f.h.entries(), b = p.h.entries();
  for (;;) {
    const x = a.next(), y = b.next();
    if (x.done) return y.done === true;
    if (y.done) return false;
    const [ks, ef] = x.value, [ps, ep] = y.value;
    if (ks !== ps) return false;
    if (ef.kk !== ep.kk && !keyvaleq(ef.kk, ep.kk)) return false;
    const vf = ef.v, vp = ep.v;
    if (vf === vp) continue;
    if (vf instanceof LTbl) { if (ok.has(vf) && inv.get(vf) === vp) continue; return false; }
    if (vp instanceof LTbl || !keyvaleq(vf, vp)) return false;
  }
}
function _tbleqs(inv) {
  const ok = new Set();
  for (const [f, p] of inv) if (f.tid === null && p.tid === null && !f.fixed && !p.fixed && f.constructor === p.constructor && f.h.size === p.h.size) ok.add(f);
  let chg = true;
  while (chg) {
    chg = false;
    for (const f of ok) if (!_tbleq1(f, inv.get(f), inv, ok)) { ok.delete(f); chg = true; }
  }
  return ok;
}

module.exports = {
  sbase, obase, lbase, hbase, lvbase, bbase, snbase,
  mst, pslk, mrst, cmod,
  hhas, hget, hsetraw, hdel, hitems, hkeys, hclr,
  tkloc, tkiter, tktop, tktab, tkovl,
  FnRef, Stor, _unsto, InsPrx, BoxTbl, KGlob, Lin, SprIdx, Spr,
  BoxRef, MbBox, UpLst, VmCls, GtrProto, GiRef, ChkRes, _Lost,
  vcls, env, vglob, nfold, trt, bool, taint, tblid,
  repr, frepr,
  _multik, _kval, _cpfresh, _isphan, _samefact, _tbleqs, Fcts,
};

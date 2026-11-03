"use strict";
class Unsup extends Error {}

class ValErr extends Error {}
class OvfErr extends Error {}
class ZeroDivErr extends Error {}
class BrkSig extends Error {}
class ContSig extends Error {}
class RetSig extends Error { constructor(vals) { super("return"); this.values = vals; } }
class YldSig extends Error { constructor(node) { super("yield"); this.node = node; } }

let _objid = 0;
const _objkeymap = new WeakMap();

class LTbl {
  constructor(h, tid) {
    this.h = (h instanceof Map) ? h : new Map();
    this.tid = (tid === undefined) ? null : tid;
  }
  get(k) { const r = this.h.get(kstr(nmkey(k))); return r === undefined ? null : r.v; }
  set(k, v) {
    const ks = kstr(nmkey(k));
    if (v === null || v === undefined) { this.h.delete(ks); return; }

    const e = this.h.get(ks);
    if (e !== undefined) e.v = v;
    else this.h.set(ks, { kk: nmkey(k), v });
  }
  length() {
    let n = 0n;
    while (this.h.has(kstr(n + 1n))) n += 1n;
    return n;
  }
}

class Buf {
  constructor(data) { this.data = Buffer.from(data); }
}
class Bltn {
  constructor(name, fn) { this.name = name; this.fn = fn === undefined ? null : fn; }
}
class LFn {
  constructor(node, env) { this.node = node; this.env = env; }
}
class RegF {}
class EnvTbl {}
class UpCtnr { constructor(idx) { this.idx = idx; } }

const Const = (v) => ({ k: "Const", v });
const Reg = (n) => ({ k: "Reg", n });
const Psd = (name, dep) => ({ k: "Pseudo", name, depth: dep });
const Glob = (name) => ({ k: "Global", name });
const Upv = (idx) => ({ k: "Upval", idx });
const Idx = (obj, key) => ({ k: "Index", obj, key });
const Bin = (op, a, b) => ({ k: "Bin", op, a, b });
const Un = (op, a) => ({ k: "Un", op, a });
const TmpVal = (t, i) => ({ k: "TempVal", t, i });
const Varg = (i) => ({ k: "Vararg", i });
const NewTbl = (itms) => ({ k: "NewTable", items: itms || [] });
const ClsExpr = (proto, upv) => ({ k: "ClosureExpr", proto, upvals: upv });
const TailCnt = (tail) => ({ k: "TailCount", tail });

function Multi(itms, tail) { return { k: "Multi", items: Array.from(itms || []), tail: tail === undefined ? null : tail }; }
function multifst(m) {
  if (m.items.length) return m.items[0];
  if (m.tail != null) return tailat(m.tail, 1);
  return null;
}
const TmpTail = (t, strt) => ({ k: "TempTail", t, start: strt === undefined ? 1 : strt });
const VargTail = (strt) => ({ k: "VarargTail", start: strt === undefined ? 1 : strt });
function tailat(t, i) {
  if (t.k === "TempTail") return TmpVal(t.t, t.start + i - 1);
  if (t.k === "VarargTail") return Varg(t.start + i - 1);
  throw new Unsup("tail " + (t && t.k));
}
function taildrop(t, k) {
  if (t.k === "TempTail") return TmpTail(t.t, t.start + k);
  if (t.k === "VarargTail") return VargTail(t.start + k);
  throw new Unsup("tail " + (t && t.k));
}
function SymLst(itms, tail, nkey) {
  return { k: "SymList", items: Array.from(itms || []), tail: tail === undefined ? null : tail, nkey: nkey === undefined ? null : nkey, extra: {} };
}
const nexpr = new Set(["Multi", "SymList", "TempTail", "VarargTail"]);
function issym(v) {
  return v !== null && typeof v === "object" && typeof v.k === "string" && !nexpr.has(v.k);
}
function islt(v) { return v instanceof LTbl; }
function isby(v) { return Buffer.isBuffer(v); }
function isnum(v) { const t = typeof v; return t === "bigint" || t === "number"; }
function isint(v) { return typeof v === "bigint"; }
function isflt(v) { return typeof v === "number"; }

function nmkey(k) {
  if (typeof k === "number") {
    const ik = toi(k);
    return k === Number(ik) ? ik : k;
  }
  if (issym(k)) throw new Unsup("symbolic table key on a concrete table: " + repr(k));
  return k;
}
function kstr(k) {
  const t = typeof k;
  if (t === "bigint") return "i" + k.toString();
  if (t === "number") return "f" + String(k);

  if (t === "boolean") return "i" + (k ? "1" : "0");
  if (t === "string") return "S" + k;
  if (k === null || k === undefined) return "nil";
  if (isby(k)) return "s" + k.toString("hex");
  let id = _objkeymap.get(k); if (id === undefined) { id = ++_objid; _objkeymap.set(k, id); }
  return "o" + id;
}

function tru(v) { return !(v === null || v === undefined || v === false); }

const ws = "\\t\\n\\x0b\\f\\r\\x1c\\x1d\\x1e\\x1f \\x85\\xa0";
const wstrp = new RegExp("^[" + ws + "]+|[" + ws + "]+$", "g");

function lnum(v) {
  if (typeof v === "boolean" || v === null || v === undefined) return null;
  if (isnum(v)) return v;
  if (isby(v)) {
    const s = v.toString("latin1").replace(wstrp, "");
    const low = s.toLowerCase();
    if (low.startsWith("0x") || low.startsWith("-0x")) {
      const r = pyhex(s); return r;
    }
    return pyfloat(s);
  }
  return null;
}

function pyhex(s) {
  let neg = false; let t = s;
  if (t[0] === "+" || t[0] === "-") { neg = t[0] === "-"; t = t.slice(1); }
  if (!/^0[xX][0-9a-fA-F](_?[0-9a-fA-F])*$/.test(t)) return null;
  const hex = t.slice(2).replace(/_/g, "");
  let val = 0n; for (const ch of hex) val = val * 16n + BigInt(parseInt(ch, 16));
  return neg ? -val : val;
}

function pyfloat(s) {
  let t = s;
  const m = /^[+-]?(?:inf|infinity)$/i.test(t);
  if (m) return t[0] === "-" ? -Infinity : Infinity;
  if (/^[+-]?nan$/i.test(t)) return NaN;

  const re = /^[+-]?(?:\d(?:_?\d)*(?:\.(?:\d(?:_?\d)*)?)?|\.\d(?:_?\d)*)(?:[eE][+-]?\d(?:_?\d)*)?$/;
  if (!re.test(t)) return null;
  return Number(t.replace(/_/g, ""));
}

const two63 = 9223372036854775808;
function fixint(x) {
  if (typeof x === "number" && Number.isFinite(x) && Number.isInteger(x) && Math.abs(x) < two63) return BigInt(x);
  return x;
}

function arith(op, a, b) {
  const bothint = isint(a) && isint(b);
  if (op === "Add") return bothint ? (a + b) : fixint(num(a) + num(b));
  if (op === "Sub") return bothint ? (a - b) : fixint(num(a) - num(b));
  if (op === "Mul") return bothint ? (a * b) : fixint(num(a) * num(b));
  if (op === "Div") {
    if (eqzero(b)) {
      if (eqzero(a)) return NaN;
      const sgn = (num(a) < 0 || Object.is(num(a), -0)) ? -1 : 1;
      let r = sgn * Infinity;
      if (isflt(b) && (b < 0 || Object.is(b, -0))) r = -r;
      return r;
    }
    return fixint(num(a) / num(b));
  }
  if (op === "FloorDiv") {
    if (eqzero(b)) return arith("Div", a, b);
    if (bothint) return bigflrdiv(a, b);
    return fixint(Math.floor(num(a) / num(b)));
  }
  if (op === "Mod") {
    if (eqzero(b)) return NaN;
    if (bothint) return bigflrmod(a, b);
    let r = fmod(num(a), num(b));
    if (r !== 0 && ((r < 0) !== (num(b) < 0))) r += num(b);
    return fixint(r);
  }
  if (op === "Pow") {
    const x = num(a), y = num(b);
    if (x === 0 && y < 0 && Number.isFinite(y)) throw new ZeroDivErr("zero to a negative power");
    const r = Math.pow(x, y);
    if ((r === Infinity || r === -Infinity) && Number.isFinite(x) && Number.isFinite(y)) throw new OvfErr("(34, 'Result too large')");
    return fixint(r);
  }
  throw new Unsup(op);
}
function num(x) { return typeof x === "bigint" ? Number(x) : x; }
function eqzero(x) { return typeof x === "bigint" ? x === 0n : x === 0; }
function fmod(a, b) { const r = a % b; return r; }
function bigflrdiv(a, b) { let q = a / b; if ((a % b) !== 0n && ((a < 0n) !== (b < 0n))) q -= 1n; return q; }
function bigflrmod(a, b) { let r = a % b; if (r !== 0n && ((r < 0n) !== (b < 0n))) r += b; return r; }

function u32(x) {
  return BigInt.asUintN(32, toi(x));
}
function toi(n) {
  if (typeof n === "number" && !Number.isFinite(n)) {
    if (Number.isNaN(n)) throw new ValErr("cannot convert float NaN to integer");
    throw new OvfErr("cannot convert float infinity to integer");
  }
  return typeof n === "bigint" ? n : BigInt(Math.trunc(n));
}
const bit = {
  band: (...a) => { let r = 0xFFFFFFFFn; for (const x of a) r &= u32(x); return r; },
  bor: (...a) => { let r = 0n; for (const x of a) r |= u32(x); return r; },
  bxor: (...a) => { let r = 0n; for (const x of a) r ^= u32(x); return r; },
  lshift: (x, n) => { n = toi(n); const an = n < 0n ? -n : n; return an >= 32n ? 0n : (n >= 0n ? BigInt.asUintN(32, u32(x) << n) : (u32(x) >> -n)); },
  rshift: (x, n) => { n = toi(n); const an = n < 0n ? -n : n; return an >= 32n ? 0n : (n >= 0n ? (u32(x) >> n) : BigInt.asUintN(32, u32(x) << -n)); },
  arshift: (x, n) => { let xi = u32(x); n = toi(n); if (xi & 0x80000000n) xi -= (1n << 32n); return n >= 0n ? u32(xi >> (n < 31n ? n : 31n)) : bit.lshift(xi, -n); },
  lrotate: (x, n) => { let xi = u32(x); n = ((toi(n) % 32n) + 32n) % 32n; return BigInt.asUintN(32, (xi << n) | (xi >> (32n - n))); },
  rrotate: (x, n) => bit.lrotate(x, -toi(n)),
  bnot: (x) => BigInt.asUintN(32, ~u32(x)),
  extract: (x, f, w) => { w = w === undefined ? 1 : w; return (u32(x) >> toi(f)) & ((1n << toi(w)) - 1n); },
  replace: (x, v, f, w) => { w = w === undefined ? 1 : w; const m = ((1n << toi(w)) - 1n) << toi(f); return BigInt.asUintN(32, (u32(x) & ~m) | ((u32(v) << toi(f)) & m)); },
  btest: (...a) => bit.band(...a) !== 0n,
  countlz: (x) => { const xi = u32(x); return 32n - BigInt(bitlen(xi)); },
  countrz: (x) => { const xi = u32(x); return xi === 0n ? 32n : BigInt(bitlen(xi & (-xi & 0xFFFFFFFFn)) - 1); },
};
function bitlen(n) { let b = 0; let x = n < 0n ? -n : n; while (x > 0n) { x >>= 1n; b++; } return b; }
const bit32 = ["band", "bor", "bxor", "bnot", "lshift", "rshift", "arshift", "lrotate", "rrotate", "extract", "replace", "btest", "countlz", "countrz"];

const bfmt = { i8: ["Int8", 1], u8: ["Uint8", 1], i16: ["Int16", 2], u16: ["Uint16", 2], i32: ["Int32", 4], u32: ["Uint32", 4], f32: ["Float32", 4], f64: ["Float64", 8] };
function _buffns() {
  const out = {};
  for (const k of Object.keys(bfmt)) {
    const [acc, size] = bfmt[k];
    out["buffer.read" + k] = (b, off) => {
      const dv = new DataView(b.data.buffer, b.data.byteOffset, b.data.byteLength);
      const v = dv["get" + acc](Number(toi(off)), true);
      return fixint(k[0] === "f" ? v : BigInt(v));
    };
    out["buffer.write" + k] = (b, off, v) => {
      const dv = new DataView(b.data.buffer, b.data.byteOffset, b.data.byteLength);
      let val;
      if (k[0] === "u" || k[0] === "i") {
        const bits = BigInt(size * 8);
        let iv = BigInt.asUintN(Number(bits), toi(v));
        if (k[0] === "i") iv = BigInt.asIntN(Number(bits), iv);
        val = Number(iv);
      } else { val = num(v); }
      dv["set" + acc](Number(toi(off)), val, true);
    };
  }
  out["buffer.len"] = (b) => BigInt(b.data.length);
  out["buffer.tostring"] = (b) => Buffer.from(b.data);
  out["buffer.fromstring"] = (s) => new Buf(s);
  out["buffer.create"] = (n) => new Buf(Buffer.alloc(Number(toi(n))));
  out["buffer.readstring"] = (b, o, n) => Buffer.from(b.data.subarray(Number(toi(o)), Number(toi(o)) + Number(toi(n))));
  return out;
}

function _strbyte(s, i, j) {
  const n = s.length;
  i = i === undefined ? 1 : Number(toi(i));
  j = j === undefined ? i : Number(toi(j));
  if (i < 0) i += n + 1;
  if (j < 0) j += n + 1;
  i = Math.max(i, 1);
  j = Math.min(j, n);
  const itms = [];
  for (let p = i - 1; p < j; p++) itms.push(BigInt(s[p]));
  return Multi(itms);
}
function _strsub(s, i, j) {
  const n = s.length;
  i = i === undefined ? 1 : Number(toi(i));
  j = j === undefined ? -1 : Number(toi(j));
  if (i < 0) i = Math.max(n + i + 1, 1);
  else if (i === 0) i = 1;
  if (j < 0) j = n + j + 1;
  else if (j > n) j = n;
  return i <= j ? Buffer.from(s.subarray(i - 1, j)) : Buffer.alloc(0);
}

function digval(ch) {
  const c = ch.charCodeAt(0);
  if (c >= 48 && c <= 57) return c - 48;
  if (c >= 97 && c <= 122) return c - 87;
  if (c >= 65 && c <= 90) return c - 55;
  return 99;
}
function pyintstr(str, base) {
  let t = str.replace(wstrp, "");
  let neg = false;
  if (t[0] === "+" || t[0] === "-") { neg = t[0] === "-"; t = t.slice(1); }
  if (base === 16 && /^0[xX]/.test(t)) t = t.slice(2);
  else if (base === 8 && /^0[oO]/.test(t)) t = t.slice(2);
  else if (base === 2 && /^0[bB]/.test(t)) t = t.slice(2);
  const bad = () => { throw new ValErr("invalid literal for int() with base " + base + ": '" + str + "'"); };
  if (t.length === 0 || /^_|_$|__/.test(t)) bad();
  const dig = t.replace(/_/g, "");
  if (dig.length === 0) bad();
  let val = 0n; const b = BigInt(base);
  for (const ch of dig) { const d = digval(ch); if (d >= base) bad(); val = val * b + BigInt(d); }
  return neg ? -val : val;
}

const conc = {
  "string.byte": _strbyte,
  "string.sub": _strsub,
  "string.len": (s) => BigInt(s.length),
  "string.char": (...a) => Buffer.from(a.map((x) => { const n = Number(toi(x)); if (n < 0 || n > 255) throw new ValErr("bytes must be in range(0, 256)"); return n; })),
  "string.rep": (s, n, sep) => {
    const cnt = Number(toi(n)); if (cnt <= 0) return Buffer.alloc(0);
    const prts = []; for (let i = 0; i < cnt; i++) prts.push(s);
    return Buffer.concat(joinbuf(prts, sep === undefined ? Buffer.alloc(0) : sep));
  },
  "math.floor": (x) => fixint(bigflr(x)),
  "math.ceil": (x) => fixint(bigceil(x)),
  "math.abs": (x) => (typeof x === "bigint" ? (x < 0n ? -x : x) : Math.abs(x)),
  "math.max": (...a) => pyextr(a, true),
  "math.min": (...a) => pyextr(a, false),
  "tonumber": (x, b) => (b === undefined || b === null) ? lnum(x) : pyintstr(x.toString("latin1"), Number(toi(b))),
};
function joinbuf(prts, sep) { const out = []; for (let i = 0; i < prts.length; i++) { if (i) out.push(sep); out.push(prts[i]); } return out; }
function bigflr(x) { return typeof x === "bigint" ? x : toi(Math.floor(x)); }
function bigceil(x) { return typeof x === "bigint" ? x : toi(Math.ceil(x)); }
function pyextr(a, wantmax) {
  let best = a[0];
  for (let i = 1; i < a.length; i++) { const c = a[i]; const cmp = numcmp(c, best); if (wantmax ? cmp > 0 : cmp < 0) best = c; }
  return best;
}
function numcmp(a, b) {
  const af = typeof a === "number", bf = typeof b === "number";
  if ((af && Number.isNaN(a)) || (bf && Number.isNaN(b))) return NaN;
  if (!af && !bf) return a < b ? -1 : a > b ? 1 : 0;
  if (af && bf) return a < b ? -1 : a > b ? 1 : 0;
  return af ? -cmpif(b, a) : cmpif(a, b);
}
function cmpif(i, f) {
  if (f === Infinity) return -1;
  if (f === -Infinity) return 1;
  const ai = i < 0n ? -i : i;
  if (ai < 9007199254740992n) { const x = Number(i); return x < f ? -1 : x > f ? 1 : 0; }
  const [m, e] = floatme(f);
  let a2 = i, b2 = m;
  if (e >= 0) b2 = m << BigInt(e); else a2 = i << BigInt(-e);
  return a2 < b2 ? -1 : a2 > b2 ? 1 : 0;
}
function floatme(f) {
  const buf = Buffer.alloc(8); buf.writeDoubleBE(Math.abs(f), 0);
  const hi = BigInt(buf.readUInt32BE(0)), lo = BigInt(buf.readUInt32BE(4));
  const ef = Number((hi >> 20n) & 0x7FFn);
  const mant = ((hi & 0xFFFFFn) << 32n) | lo;
  let m, e;
  if (ef === 0) { m = mant; e = -1074; } else { m = mant | (1n << 52n); e = ef - 1075; }
  if (f < 0) m = -m;
  return [m, e];
}
for (const n of bit32) conc["bit32." + n] = bit[n];
Object.assign(conc, _buffns());

function leq(a, b) {
  if (typeof a === "boolean" || typeof b === "boolean") return a === b;
  if (isnum(a) && isnum(b)) return numeq(a, b);
  if (isby(a) && isby(b)) return a.equals(b);
  return a === b || (a == null && b == null);
}
function numeq(a, b) {
  if (typeof a === "number" && Number.isNaN(a)) return false;
  if (typeof b === "number" && Number.isNaN(b)) return false;
  if (typeof a === typeof b) return a === b;
  return a == b;
}

function fmtnum(v) {
  if (typeof v === "bigint") return v.toString();
  if (Number.isNaN(v)) return "nan";
  if (!Number.isFinite(v)) return v > 0 ? "inf" : "-inf";
  if (Number.isInteger(v) && Math.abs(v) < 1e15) return BigInt(v).toString();
  let r = fmtg(v, 14);
  if (Number(r) !== v) r = fmtg(v, 17);
  return r;
}

function fmtg(v, prec) {
  if (prec < 1) prec = 1;
  if (v === 0) return Object.is(v, -0) ? "-0" : "0";
  const neg = v < 0; const a = Math.abs(v);

  const buf = Buffer.alloc(8); buf.writeDoubleBE(a, 0);
  const hi = BigInt(buf.readUInt32BE(0)), lo = BigInt(buf.readUInt32BE(4));
  const efld = Number((hi >> 20n) & 0x7FFn);
  const mantfld = ((hi & 0xFFFFFn) << 32n) | lo;
  let sig, p2;
  if (efld === 0) { sig = mantfld; p2 = -1074; }
  else { sig = mantfld | (1n << 52n); p2 = efld - 1075; }

  let x = Math.floor(Math.log10(a));

  const ten = (n) => 10n ** BigInt(n);
  function digfor(x) {
    const k = prec - 1 - x;

    let num = sig, den = 1n;
    if (p2 >= 0) num *= (1n << BigInt(p2)); else den *= (1n << BigInt(-p2));
    if (k >= 0) num *= ten(k); else den *= ten(-k);
    let q = num / den; const r = num - q * den; const twc = 2n * r;
    if (twc > den || (twc === den && (q & 1n) === 1n)) q += 1n;
    return q;
  }
  let d = digfor(x);
  const lo10 = ten(prec - 1), hi10 = ten(prec);
  if (d >= hi10) { x += 1; d = digfor(x); }
  else if (d < lo10) { x -= 1; d = digfor(x); }
  if (d >= hi10) { d /= 10n; x += 1; }
  let dig = d.toString();
  if (dig.length < prec) dig = "0".repeat(prec - dig.length) + dig;
  let out;
  if (x < -4 || x >= prec) {
    const frac = dig.slice(1).replace(/0+$/, "");
    const m = dig[0] + (frac ? "." + frac : "");
    out = m + "e" + (x < 0 ? "-" : "+") + String(Math.abs(x)).padStart(2, "0");
  } else if (x >= 0) {
    const ipart = dig.slice(0, x + 1);
    const frac = dig.slice(x + 1).replace(/0+$/, "");
    out = ipart + (frac ? "." + frac : "");
  } else {
    const frac = ("0".repeat(-x - 1) + dig).replace(/0+$/, "");
    out = "0." + frac;
  }
  return neg ? "-" + out : out;
}

function repr(v) {
  if (v === null || v === undefined) return "None";
  if (typeof v === "bigint") return v.toString();
  if (typeof v === "number") return String(v);
  if (typeof v === "boolean") return v ? "True" : "False";
  if (isby(v)) return "b'" + v.toString("latin1") + "'";
  if (issym(v)) return "<" + v.k + ">";
  return "<obj>";
}

class Scp {
  constructor(par) { this.vars = new Map(); this.parent = par || null; }
  lookup(key) { let s = this; while (s !== null) { if (s.vars.has(key)) return s; s = s.parent; } return null; }
}

class Itp {
  constructor(lftr) {
    this.lft = lftr;
    this.dec = [];
    this.dpos = 0;
    this.dlog = [];
    this.seen = new Map();
    this.steps = 0;
  }

  decide(cond) {
    let d;
    if (this.dpos < this.dec.length) d = this.dec[this.dpos];
    else { d = true; this.dec.push(d); }
    this.dlog.push([this.dpos, this.lft.out.length, cond, d]);
    this.dpos += 1;
    return d;
  }
  condtru(v) {
    if (issym(v)) {
      let base = v, neg = false;
      while (base && base.k === "Un" && base.op === "Not") { base = base.a; neg = !neg; }
      const hit = this.seen.get(base);
      if (hit !== undefined && hit[0] === base) return hit[1] !== neg;
      const d = this.decide(v);
      this.seen.set(base, [base, d !== neg]);
      return d;
    }
    if (v instanceof RegF || v instanceof EnvTbl || v instanceof UpCtnr) return true;
    if (v !== null && typeof v === "object" && (v.k === "SymList" || v.k === "Multi")) return true;
    return tru(v);
  }

  getvar(scp, lcl) {
    const key = lcl.location;
    const sp = this.lft.special[key];
    if (sp !== undefined) return this.lft.specget(sp, this);
    const s = scp.lookup(key);
    if (s === null) throw new Unsup("unbound local " + lcl.name + "@" + key);
    return s.vars.get(key);
  }
  setvar(scp, lcl, v) {
    const key = lcl.location;
    const sp = this.lft.special[key];
    if (sp !== undefined) { this.lft.specset(sp); return; }
    const s = scp.lookup(key);
    if (s === null) throw new Unsup("assign to unbound local " + lcl.name);
    s.vars.set(key, v);
  }

  execblk(stmt, scp) { for (const st of stmt) this.execstmt(st, scp); }
  execstmt(st, scp) {
    this.steps += 1;
    if (this.steps > 2000000) throw new Unsup("interpreter step limit");
    const t = st.type;
    if (t === "AstStatBlock") {
      this.execblk(st.body, new Scp(scp));
    } else if (t === "AstStatLocal") {
      const vals = this.evallst(st.values, scp, st.vars.length);
      for (let i = 0; i < st.vars.length; i++) {
        const v = st.vars[i];
        scp.vars.set(v.location, vals[i]);
        const sp = this.lft.special[v.location];
        if (sp !== undefined && sp[0] === "reg") this.lft.specset(sp);
      }
    } else if (t === "AstStatAssign") {
      const tgt = st.vars.map((v) => this.lvalue(v, scp));
      let vals = this.evallst(st.values, scp, tgt.length);
      if (tgt.length > 1 && this.lft.parvals) vals = this.lft.parvals(vals);

      let _pi = 0;
      for (const _v of vals) { this.assign(tgt[_pi], _v, scp); _pi += 1; }
    } else if (t === "AstStatCompoundAssign") {
      const tg = this.lvalue(st.var, scp);
      const cur = this.rdlval(tg, scp);
      this.assign(tg, this.binop(st.op, cur, this.eval(st.value, scp)), scp);
    } else if (t === "AstStatIf") {
      if (this.condtru(this.eval(st.condition, scp))) {
        this.execblk(st.thenbody.body, new Scp(scp));
      } else if (st.elsebody != null) {
        const e = st.elsebody;
        if (e.type === "AstStatIf") this.execstmt(e, scp);
        else this.execblk(e.body, new Scp(scp));
      }
    } else if (t === "AstStatWhile") {
      if (this.lft.isdisp(st)) throw new YldSig(st);
      let n = 0;
      while (this.condtru(this.eval(st.condition, scp))) {
        n += 1; if (n > 100000) throw new Unsup("while loop limit");
        try { this.execblk(st.body.body, new Scp(scp)); }
        catch (ex) { if (ex instanceof BrkSig) break; if (ex instanceof ContSig) continue; throw ex; }
      }
    } else if (t === "AstStatRepeat") {
      let n = 0;
      while (true) {
        n += 1; if (n > 100000) throw new Unsup("repeat loop limit");
        const inr = new Scp(scp);
        try { this.execblk(st.body.body, inr); }
        catch (ex) { if (ex instanceof BrkSig) break; else if (ex instanceof ContSig) {} else throw ex; }
        if (this.condtru(this.eval(st.condition, inr))) break;
      }
    } else if (t === "AstStatFor") {
      let a = this.eval(st.from, scp);
      let b = this.eval(st.to, scp);
      let c = st.step ? this.eval(st.step, scp) : 1n;
      if (a == null || b == null || c == null) throw new Unsup("numeric for with unknown bounds");
      if (issym(a) || issym(b) || issym(c)) throw new Unsup("numeric for with symbolic bounds");
      if (!([a, b, c].every((x) => isnum(x)))) throw new Unsup("numeric for with non-numeric bounds");
      if (eqzero(c)) throw new Unsup("numeric for with zero step");
      let i = a; let n = 0;
      const cpos = numcmp(c, 0n) > 0;
      while ((cpos && numcmp(i, b) <= 0) || (!cpos && numcmp(i, b) >= 0)) {
        n += 1; if (n > 1000000) throw new Unsup("for loop limit");
        const inr = new Scp(scp);
        inr.vars.set(st.var.location, i);
        try { this.execblk(st.body.body, inr); }
        catch (ex) { if (ex instanceof BrkSig) break; else if (ex instanceof ContSig) { } else throw ex; }
        i = fixint(isint(i) && isint(c) ? (i + c) : (num(i) + num(c)));
      }
    } else if (t === "AstStatForIn") {
      const vals = this.evallst(st.values, scp, 3);
      let f = vals[0], s = vals[1], ctl = vals[2];
      let n = 0;
      while (true) {
        n += 1; if (n > 1000000) throw new Unsup("for-in limit");
        let r = this.call(f, [s, ctl]);
        r = this.adjust(r, st.vars.length);
        if (r[0] === null || r[0] === undefined) break;
        if (issym(r[0])) throw new Unsup("symbolic generic for");
        ctl = r[0];
        const inr = new Scp(scp);
        for (let i = 0; i < st.vars.length; i++) inr.vars.set(st.vars[i].location, r[i]);
        try { this.execblk(st.body.body, inr); }
        catch (ex) { if (ex instanceof BrkSig) break; else if (ex instanceof ContSig) { } else throw ex; }
      }
    } else if (t === "AstStatReturn") {
      throw new RetSig(this.evalmlst(st.list, scp));
    } else if (t === "AstStatBreak") {
      throw new BrkSig();
    } else if (t === "AstStatContinue") {
      throw new ContSig();
    } else if (t === "AstStatExpr") {
      const e = st.expr;
      if (e.type !== "AstExprCall") throw new Unsup("expression statement " + e.type);
      this.evalcall(e, scp);
    } else if (t === "AstStatLocalFunction") {
      scp.vars.set(st.name.location, new LFn(st.func, scp));
    } else if (t === "AstStatFunction") {
      throw new Unsup("function statement");
    } else {
      throw new Unsup("statement " + t);
    }
  }

  lvalue(node, scp) {
    const t = node.type;
    if (t === "AstExprLocal") return ["local", node.local];
    if (t === "AstExprIndexExpr") return ["index", this.eval(node.expr, scp), this.eval(node.index, scp)];
    if (t === "AstExprIndexName") return ["index", this.eval(node.expr, scp), Buffer.from(node.index, "latin1")];
    if (t === "AstExprGlobal") return ["global", node.global];
    throw new Unsup("lvalue " + t);
  }
  rdlval(tg, scp) {
    if (tg[0] === "local") return this.getvar(scp, tg[1]);
    if (tg[0] === "index") return this.index(tg[1], tg[2]);
    throw new Unsup("read global lvalue");
  }
  assign(tg, v, scp) {
    if (tg[0] === "local") this.setvar(scp, tg[1], v);
    else if (tg[0] === "index") this.newindex(tg[1], tg[2], v);
    else if (this.lft.setglob) this.lft.setglob(tg[1], v);
    else throw new Unsup("assignment to global " + tg[1] + " in VM code");
  }

  evallst(nds, scp, want) { return this.adjust(this.evalmlst(nds, scp), want); }
  adjust(m, want) {
    if (!(m !== null && typeof m === "object" && m.k === "Multi")) m = Multi([m]);
    const out = m.items.slice(0, want);
    let i = 1;
    while (out.length < want) {
      if (m.tail != null) { out.push(tailat(m.tail, i)); i += 1; }
      else out.push(null);
    }
    return out;
  }
  evalmlst(nds, scp) {
    const itms = []; let tail = null;
    for (let i = 0; i < nds.length; i++) {
      const n = nds[i];
      if (i === nds.length - 1 && (n.type === "AstExprCall" || n.type === "AstExprVarargs")) {
        const m = this.evalmulti(n, scp);
        for (const x of m.items) itms.push(x);
        tail = m.tail;
      } else itms.push(this.eval(n, scp));
    }
    return Multi(itms, tail);
  }
  evalmulti(node, scp) {
    const t = node.type;
    if (t === "AstExprCall") { const r = this.evalcall(node, scp); return (r !== null && typeof r === "object" && r.k === "Multi") ? r : Multi([r]); }
    if (t === "AstExprVarargs") return this.lft.varargs(scp);
    return Multi([this.eval(node, scp)]);
  }

  eval(node, scp) {
    const t = node.type;
    if (t === "AstExprConstantNumber") return fixint(node.value);
    if (t === "AstExprConstantString") return Buffer.from(node.value, "latin1");
    if (t === "AstExprConstantBool") return node.value;
    if (t === "AstExprConstantNil") return null;
    if (t === "AstExprLocal") return this.getvar(scp, node.local);
    if (t === "AstExprGlobal") return this.lft.globval(node.global);
    if (t === "AstExprGroup") return this.eval(node.expr, scp);
    if (t === "AstExprIndexExpr") {
      const obj = this.eval(node.expr, scp);
      if (obj === null || obj === undefined) throw new Unsup("index nil @" + node.location);
      return this.index(obj, this.eval(node.index, scp));
    }
    if (t === "AstExprIndexName") {
      const obj = this.eval(node.expr, scp);
      if (obj === null || obj === undefined) throw new Unsup("index nil @" + node.location);
      return this.index(obj, Buffer.from(node.index, "latin1"));
    }
    if (t === "AstExprCall") { const r = this.evalcall(node, scp); return (r !== null && typeof r === "object" && r.k === "Multi") ? multifst(r) : r; }
    if (t === "AstExprVarargs") return multifst(this.lft.varargs(scp));
    if (t === "AstExprBinary") {
      const op = node.op;
      if (op === "And") { const a = this.eval(node.left, scp); return this.condtru(a) ? this.eval(node.right, scp) : a; }
      if (op === "Or") { const a = this.eval(node.left, scp); return this.condtru(a) ? a : this.eval(node.right, scp); }
      return this.binop(op, this.eval(node.left, scp), this.eval(node.right, scp));
    }
    if (t === "AstExprUnary") return this.unop(node.op, this.eval(node.expr, scp));
    if (t === "AstExprIfElse") { const c = this.eval(node.condition, scp); return this.eval(this.condtru(c) ? node.trueExpr : node.falseExpr, scp); }
    if (t === "AstExprTable") return this.tblctor(node, scp);
    if (t === "AstExprFunction") return new LFn(node, scp);
    if (t === "AstExprTypeAssertion") return this.eval(node.expr, scp);
    throw new Unsup("expression " + t);
  }

  tblctor(node, scp) {
    const itms = node.items;
    const tb = new LTbl();
    let pos = 1; let sym = false;
    for (let i = 0; i < itms.length; i++) {
      const it = itms[i];
      if (it.kind === "item") {
        const last = i === itms.length - 1;
        if (last && (it.value.type === "AstExprCall" || it.value.type === "AstExprVarargs")) {
          const m = this.evalmulti(it.value, scp);
          if (m.tail != null) {
            const pfx = [];
            for (let kk = 1; kk < pos; kk++) pfx.push(tb.get(BigInt(kk)));
            return SymLst(pfx.concat(m.items), m.tail, null);
          }
          for (const v of m.items) { tb.set(BigInt(pos), v); pos += 1; }
        } else { tb.set(BigInt(pos), this.eval(it.value, scp)); pos += 1; }
      } else {
        const k = it.kind === "record" ? Buffer.from(it.key.value, "latin1") : this.eval(it.key, scp);
        const v = this.eval(it.value, scp);
        if (issym(k)) sym = true;
        tb.set(k, v);
      }
    }
    if (sym) throw new Unsup("symbolic key in table constructor");
    return tb;
  }

  binop(op, a, b) {
    if (issym(a) || issym(b) || issymlr(a) || issymlr(b)) return this.lft.symbinop(op, a, b);
    if (["Add", "Sub", "Mul", "Div", "FloorDiv", "Mod", "Pow"].includes(op)) {
      const x = lnum(a), y = lnum(b);
      if (x === null || y === null) throw new Unsup("arith on " + repr(a) + " " + repr(b));
      return arith(op, x, y);
    }
    if (op === "Concat") {
      const s = (v) => {
        if (isby(v)) return v;
        if (typeof v === "boolean") return Buffer.from(v ? "True" : "False", "latin1");
        if (isnum(v)) return Buffer.from(fmtnum(v), "latin1");
        throw new Unsup("concat");
      };
      return Buffer.concat([s(a), s(b)]);
    }
    if (op === "CompareEq") return leq(a, b);
    if (op === "CompareNe") return !leq(a, b);
    if (["CompareLt", "CompareLe", "CompareGt", "CompareGe"].includes(op)) {
      const oknum = isnum(a) && isnum(b) && typeof a !== "boolean" && typeof b !== "boolean";
      const okstr = isby(a) && isby(b);
      if (!(oknum || okstr)) throw new Unsup("compare " + repr(a) + " " + repr(b));
      let c;
      if (okstr) c = Buffer.compare(a, b);
      else c = numcmp(a, b);
      return { CompareLt: c < 0, CompareLe: c <= 0, CompareGt: c > 0, CompareGe: c >= 0 }[op];
    }
    throw new Unsup("binop " + op);
  }
  unop(op, a) {
    if (issym(a) || (a !== null && typeof a === "object" && a.k === "SymList")) return this.lft.symunop(op, a);
    if (op === "Not") return !tru(a);
    if (op === "Minus") { const x = lnum(a); if (x === null) throw new Unsup("unm"); return fixint(typeof x === "bigint" ? -x : -x); }
    if (op === "Len") { if (isby(a)) return BigInt(a.length); if (islt(a)) return a.length(); throw new Unsup("len of " + repr(a)); }
    throw new Unsup("unop " + op);
  }

  index(obj, key) { return this.lft.index(obj, key, this); }
  newindex(obj, key, v) { this.lft.newindex(obj, key, v, this); }

  evalcall(node, scp) {
    const fnode = node.func;
    let fn, args;
    if (node.self) {
      const obj = this.eval(fnode.expr, scp);
      fn = this.index(obj, Buffer.from(fnode.index, "latin1"));
      const a = this.evalmlst(node.args, scp);
      args = Multi([obj].concat(a.items), a.tail);
    } else {
      fn = this.eval(fnode, scp);
      args = this.evalmlst(node.args, scp);
    }
    return this.call(fn, args);
  }
  call(fn, args) {
    if (!(args !== null && typeof args === "object" && args.k === "Multi")) args = Multi(Array.from(args));
    if (fn instanceof LFn) return this.calllua(fn, args);
    if (fn instanceof Bltn) return this.lft.callbltn(fn, args, this);
    return this.lft.callsym(fn, args, this);
  }
  calllua(fn, args) {
    const node = fn.node;
    const scp = new Scp(fn.env);
    const vals = this.adjust(args, node.args.length);
    for (let i = 0; i < node.args.length; i++) scp.vars.set(node.args[i].location, vals[i]);
    if (node.vararg) {
      const rest = Multi(args.items.slice(node.args.length), args.tail != null ? taildrop(args.tail, Math.max(0, node.args.length - args.items.length)) : null);
      scp.vars.set("...", rest);
    }
    try { this.execblk(node.body.body, scp); }
    catch (ex) { if (ex instanceof RetSig) return ex.values; throw ex; }
    return Multi([]);
  }
}
function issymlr(v) { return v instanceof RegF || (v !== null && typeof v === "object" && v.k === "SymList"); }

module.exports = {
  Unsup, ValErr, OvfErr, ZeroDivErr, BrkSig, ContSig, RetSig,
  LTbl, Buf, Bltn, LFn, RegF, EnvTbl, UpCtnr, Scp,
  Const, Reg, Psd, Glob, Upv, Idx, Bin, Un, TmpVal,
  NewTbl, ClsExpr, TailCnt, Multi, TmpTail, VargTail, SymLst,
  multifst, tailat, taildrop,
  issym, isby, nmkey, kstr,
  tru, lnum, fixint, arith, conc, leq, fmtnum,
  numcmp, Itp,
};

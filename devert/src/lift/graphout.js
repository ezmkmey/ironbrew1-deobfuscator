"use strict";
const sym = require("./sym.js");
const ir = require("./ir.js");
const dvl = require("./dval.js");
const { StubProto } = require("./exec.js");
const { Spr, BoxRef, MbBox, ChkRes, GtrProto, KGlob,
  repr, frepr } = dvl;
const { LTbl, Bltn, LFn, isby } = sym;

function sproto(p) {
  if (p instanceof StubProto) return { t: "stub", where: p.where };
  if (p instanceof GtrProto) return { t: "getter", n: p.n };
  return { t: "ci", ci: p };
}

function skind(v) {
  if (Array.isArray(v)) return (v.length === 2 && v[0] === "const") ? { const: sx(v[1]) } : { tuple: v.map(sx) };
  return { v: v };
}

function sx(x) {
  if (x === null || x === undefined) return null;
  const t = typeof x;
  if (t === "boolean") return { k: "bool", v: x };
  if (t === "bigint") return { k: "int", v: Number(x) };
  if (t === "number") return { k: "float", v: frepr(x) };
  if (isby(x)) return { k: "bytes", v: Array.from(x) };
  if (t === "string") return { k: "str", v: x };

  if (x.s === "Assign") return { s: "Assign", target: sx(x.target), value: sx(x.value) };
  if (x.s === "CallStmt") return { s: "CallStmt", t: String(x.t), fn: sx(x.fn), args: sx(x.args) };
  if (x.s === "SetList") return { s: "SetList", tbl: sx(x.tbl), start: x.start, values: sx(x.values) };
  if (x.s === "Close") return { s: "Close", reg: (typeof x.reg === "number" || typeof x.reg === "bigint") ? x.reg : sx(x.reg) };

  switch (x.k) {
    case "Const": return { k: "Const", v: sx(x.v) };
    case "Reg": return { k: "Reg", n: x.n };
    case "Pseudo": return { k: "Pseudo", name: x.name, depth: x.depth };
    case "Global": return (x instanceof KGlob || x.known) ? { k: "KnownGlobal", name: x.name } : { k: "Global", name: x.name };
    case "Upval": return { k: "Upval", idx: x.idx };
    case "Index": return { k: "Index", obj: sx(x.obj), key: sx(x.key) };
    case "Bin": return { k: "Bin", op: x.op, a: sx(x.a), b: sx(x.b) };
    case "Un": return { k: "Un", op: x.op, a: sx(x.a) };
    case "TempVal": return { k: "TempVal", t: String(x.t), i: x.i };
    case "Vararg": return { k: "Vararg", i: x.i };
    case "TailCount": return { k: "TailCount", tail: sx(x.tail) };
    case "NewTable": return { k: "NewTable", items: x.items.map(([k, v]) => [sx(k), sx(v)]) };
    case "GenIter": return { k: "GenIter", args: sx(x.args) };
    case "Opaque": return { k: "Opaque", kind: x.kind, src: x.src };
    case "Vec": return { k: "Vec", xyz: x.xyz.map((v) => frepr(v)) };
    case "ClosureExpr": return {
      k: "ClosureExpr", proto: sproto(x.proto), upvals: x.upvals.map(sx),
      kinds: mapsk(x.kinds || {}, skind), capnames: mapsk(x.capnames || {}, (v) => v),
    };
    case "Multi": return { k: "Multi", items: x.items.map(sx), tail: sx(x.tail) };
    case "TempTail": return { k: "TempTail", t: String(x.t), start: x.start };
    case "VarargTail": return { k: "VarargTail", start: x.start };
    case "SymList": return { k: "SymList", items: x.items.map(sx), tail: sx(x.tail) };
    case "Lin": return { k: "Lin", tail: sx(x.tail), base: x.base === undefined ? null : x.base };
    case "SpreadIdx": return { k: "SpreadIdx", m: x.m === undefined ? null : sx(x.m), i: x.i === undefined ? null : sx(x.i) };
  }

  if (x instanceof Spr) return { k: "Spread", m: sx(x.m) };
  if (x instanceof BoxRef) return { k: "BoxRef", target: sx(x.target) };
  if (x instanceof MbBox) return { k: "MaybeBox", reg: x.reg };
  if (x instanceof ChkRes) return { k: "CheckResult" };
  if (x instanceof LTbl) return { k: "LTable", tid: x.tid !== null && x.tid !== undefined ? String(x.tid) : null };
  if (x instanceof Bltn) return { k: "Builtin", name: x.name };
  if (x instanceof LFn) return { k: "LuaFunc" };
  if (x && x.o === "Next") return soutc(x);
  if (Array.isArray(x)) return x.map(sx);
  if (x instanceof ir.Node || (x && Array.isArray(x.stmts))) return snode(x);
  return { k: "repr", v: repr(x) };
}

function mapsk(obj, fn) {
  const out = {};
  if (obj instanceof Map) { for (const [k, v] of obj) out[String(k)] = fn(v); return out; }
  for (const k of Object.keys(obj)) out[String(k)] = fn(obj[k]);
  return out;
}

function soutc(o) {
  if (o === null || o === undefined) return null;
  if (o.o === "Next") return { o: "Next", key: o.state.key() };
  if (o.o === "Ret") return { o: "Ret", values: sx(o.values) };
  return { o: "repr", v: repr(o) };
}

function snode(n) {
  const d = { stmts: n.stmts.map(sx) };
  if (n.error) d.error = n.error;
  if (n.cond !== null && n.cond !== undefined) {
    d.cond = sx(n.cond);
    d.then = n.then ? snode(n.then) : null;
    d.els = n.els ? snode(n.els) : null;
  } else {
    d.outcome = soutc(n.outcome);
  }
  return d;
}

function serord(ordr) {
  return ordr.map(([k, n]) => ({ key: k, node: snode(n) }));
}

module.exports = { serord };

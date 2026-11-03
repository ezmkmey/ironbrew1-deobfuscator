"use strict";
const sym = require("./sym.js");

const Asgn = (tgt, val) => ({ s: "Assign", target: tgt, value: val });
const CallStmt = (t, fn, args) => ({ s: "CallStmt", t, fn, args });
const SetLst = (tbl, strt, vals) => ({ s: "SetList", tbl, start: strt, values: vals });
const Close = (reg) => ({ s: "Close", reg });

const GenIter = (args) => ({ k: "GenIter", args });
const Opq = (kind, src) => ({ k: "Opaque", kind, src: src === undefined ? "" : src });
const Vec = (xyz) => ({ k: "Vec", xyz });

const Next = (st) => ({ o: "Next", state: st });
const Ret = (vals) => ({ o: "Ret", values: vals });

function Node(stmts, cond, then, els, outc) {
  return { stmts, cond: cond === undefined ? null : cond, then: then === undefined ? null : then,
    els: els === undefined ? null : els, outcome: outc === undefined ? null : outc };
}

function fmtexpr(e) {
  if (e === null || e === undefined) return "nil";
  switch (e.k) {
    case "Const": return fmtconst(e.v);
    case "Reg": return "r" + e.n;
    case "Pseudo": return e.name + "_" + e.depth;
    case "Global": return e.name;
    case "Upval": return "up" + e.idx;
    case "Index": return fmtexpr(e.obj) + "[" + fmtexpr(e.key) + "]";
    case "Bin": return "(" + fmtexpr(e.a) + " " + e.op + " " + fmtexpr(e.b) + ")";
    case "Un": return "(" + e.op + " " + fmtexpr(e.a) + ")";
    case "TempVal": return "T" + e.t + "[" + e.i + "]";
    case "Vararg": return "vararg[" + e.i + "]";
    case "TailCount": return "#(" + fmttail(e.tail) + ")";
    case "ClosureExpr": return "closure(" + irrepr(e.proto) + ", ups=[" + e.upvals.map(fmtany).join(", ") + "])";
    case "GenIter": return "geniter(" + fmtmulti(e.args) + ")";
    case "NewTable": return "{}";
    case "Opaque": return e.src || ("<" + e.kind + ">");
    case "Vec": return "vector(" + e.xyz.map((x) => sym.fmtnum(x)).join(", ") + ")";
    case "SymList": return "pack(" + fmtmulti(sym.Multi(e.items, e.tail)) + ")";
    default: return irrepr(e);
  }
}
function fmtany(v) {
  if (v === null || v === undefined) return fmtexpr(v);
  if (sym.issym(v) || (typeof v === "object" && v.k === "SymList")) return fmtexpr(v);
  if (v instanceof sym.LTbl) return "{" + Array.from(v.h.values()).map((e) => irrepr(e.kk) + "=" + fmtany(e.v)).join(", ") + "}";
  if (v instanceof sym.RegF) return "REGS";
  if (v instanceof sym.UpCtnr) return "UPC" + v.idx;
  if (typeof v === "boolean" || typeof v === "bigint" || typeof v === "number" || sym.isby(v)) return fmtconst(v);
  return irrepr(v);
}
function fmttail(t) {
  if (t === null || t === undefined) return "None";
  if (t.k === "TempTail") return "T" + t.t + "[" + t.start + "...]";
  if (t.k === "VarargTail") return "vararg[" + t.start + "...]";
  return irrepr(t);
}
function fmtmulti(m) {
  const prts = m.items.map(fmtany);
  if (m.tail != null) prts.push(fmttail(m.tail));
  return prts.join(", ");
}
function fmtconst(v) {
  if (v === null || v === undefined) return "nil";
  if (v === true) return "true";
  if (v === false) return "false";
  if (sym.isby(v)) {
    let out = "";
    for (const c of v) out += (c >= 32 && c < 127 && c !== 34 && c !== 92) ? String.fromCharCode(c) : ("\\" + c);
    return '"' + out + '"';
  }
  if (typeof v === "bigint" || typeof v === "number") return sym.fmtnum(v);
  return irrepr(v);
}
function fmtstmt(s) {
  if (s.s === "SetList") return fmtexpr(s.tbl) + "[" + s.start + "...] = " + fmtmulti(s.values);
  if (s.s === "Assign") return fmtexpr(s.target) + " = " + fmtexpr(s.value);
  if (s.s === "CallStmt") return "T" + s.t + " = " + fmtexpr(s.fn) + "(" + fmtmulti(s.args) + ")";
  return irrepr(s);
}

function irrepr(v) {
  if (v === null || v === undefined) return "None";
  if (typeof v === "bigint") return v.toString();
  if (typeof v === "number") return sym.fmtnum(v);
  if (typeof v === "boolean") return v ? "True" : "False";
  if (sym.isby(v)) return "b'" + v.toString("latin1") + "'";
  if (v && typeof v === "object" && typeof v.k === "string") return "<" + v.k + ">";
  return "<obj>";
}

module.exports = {
  Asgn, CallStmt, SetLst, Close, GenIter, Opq, Vec,
  Next, Ret, Node,
  fmtexpr, fmttail, fmtmulti, fmtstmt,
};

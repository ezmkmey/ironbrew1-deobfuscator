// usage: const { splice } = require("./natp.js"); splice(<emitted luau text>, <natives.json object>) returns the text with every __devert_native_<id> marker closure replaced by the native function's own code
"use strict";
const kw = new Set("and break do else elseif end false for function if in local nil not or repeat return then true until while continue".split(" "));
const binop = { Add: "+", Sub: "-", Mul: "*", Div: "/", FloorDiv: "//", Mod: "%", Pow: "^", Concat: "..", CompareNe: "~=", CompareEq: "==",
  CompareLt: "<", CompareLe: "<=", CompareGt: ">", CompareGe: ">=", And: "and", Or: "or" };
const unop = { Not: "not ", Minus: "-", Len: "#" };
const isid = (s) => typeof s === "string" && /^[A-Za-z_][A-Za-z0-9_]*$/.test(s) && !kw.has(s);

function qstr(s) {
  let o = "\"";
  for (let i = 0; i < s.length; i++) {
    const c = s.charCodeAt(i);
    if (c === 34) o += "\\\"";
    else if (c === 92) o += "\\\\";
    else if (c === 10) o += "\\n";
    else if (c === 13) o += "\\r";
    else if (c === 9) o += "\\t";
    else if (c < 32 || c === 127 || c > 255) o += "\\" + String(c & 255).padStart(3, "0");
    else o += s[i];
  }
  return o + "\"";
}
function num(v) {
  if (typeof v !== "number") throw new Error("native number " + v);
  if (Number.isNaN(v)) return "0 / 0";
  if (v === Infinity) return "math.huge";
  if (v === -Infinity) return "-math.huge";
  return String(v);
}

function ex(n, cx) {
  switch (n.type) {
    case "AstExprConstantNil": return "nil";
    case "AstExprConstantBool": return n.value ? "true" : "false";
    case "AstExprConstantNumber": return num(n.value);
    case "AstExprConstantString": return qstr(n.value);
    case "AstExprVarargs": return "...";
    case "AstExprLocal": return cx.use(n.local);
    case "AstExprGlobal": return n.global;
    case "AstExprGroup": return "(" + ex(n.expr, cx) + ")";
    case "AstExprIndexName": return ex(n.expr, cx) + (n.op === ":" ? ":" : ".") + n.index;
    case "AstExprIndexExpr": {
      const s = cx.sub(n); if (s !== null) return s;
      if (!cx.raw && n.index.type === "AstExprConstantString" && isid(n.index.value)) return ex(n.expr, cx) + "." + n.index.value;
      return ex(n.expr, cx) + "[" + ex(n.index, cx) + "]";
    }
    case "AstExprCall": return ex(n.func, cx) + "(" + n.args.map((a) => ex(a, cx)).join(", ") + ")";
    case "AstExprBinary": if (!binop[n.op]) break; return ex(n.left, cx) + " " + binop[n.op] + " " + ex(n.right, cx);
    case "AstExprUnary": { if (!unop[n.op]) break; const a = ex(n.expr, cx); return (n.op === "Minus" && a.startsWith("-")) ? "- " + a : unop[n.op] + a; }
    case "AstExprIfElse": return "if " + ex(n.condition, cx) + " then " + ex(n.trueExpr, cx) + " else " + ex(n.falseExpr, cx);
    case "AstExprFunction": return "function" + fnbody(n, cx);
    case "AstExprTable": {
      if (!n.items.length) return "{}";
      const its = n.items.map((it) => {
        if (it.kind === "item") return ex(it.value, cx);
        if (it.kind === "record" && it.key && it.key.type === "AstExprConstantString" && isid(it.key.value)) return it.key.value + " = " + ex(it.value, cx);
        if (it.key) return "[" + ex(it.key, cx) + "] = " + ex(it.value, cx);
        throw new Error("native table item " + it.kind);
      });
      return "{ " + its.join(", ") + " }";
    }
  }
  throw new Error("native node " + n.type + (n.op ? " " + n.op : ""));
}

function fnbody(f, cx) {
  const ps = f.args.map((a) => cx.def(a));
  if (f.vararg) ps.push("...");
  const ind = cx.ind, out = [];
  blk(f.body, cx, ind + "\t", out);
  cx.ind = ind;
  return "(" + ps.join(", ") + ")\n" + out.map((l) => l + "\n").join("") + ind + "end";
}
function blk(b, cx, ind, out) { for (const s of b.body) st(s, cx, ind, out); }
function st(n, cx, ind, out) {
  cx.ind = ind;
  const xs = (l) => l.map((e) => ex(e, cx)).join(", ");
  switch (n.type) {
    case "AstStatLocal": { const v = n.values.length ? " = " + xs(n.values) : ""; out.push(ind + "local " + n.vars.map((x) => cx.def(x)).join(", ") + v); return; }
    case "AstStatAssign": out.push(ind + xs(n.vars) + " = " + xs(n.values)); return;
    case "AstStatCompoundAssign": out.push(ind + ex(n.var, cx) + " " + binop[n.op] + "= " + ex(n.value, cx)); return;
    case "AstStatExpr": out.push(ind + ex(n.expr, cx)); return;
    case "AstStatReturn": out.push(ind + "return" + (n.list.length ? " " + xs(n.list) : "")); return;
    case "AstStatBreak": out.push(ind + "break"); return;
    case "AstStatContinue": out.push(ind + "continue"); return;
    case "AstStatBlock": out.push(ind + "do"); blk(n, cx, ind + "\t", out); out.push(ind + "end"); return;
    case "AstStatIf": {
      out.push(ind + "if " + ex(n.condition, cx) + " then");
      blk(n.thenbody, cx, ind + "\t", out);
      let e = n.elsebody;
      while (e) {
        cx.ind = ind;
        if (e.type === "AstStatIf") { out.push(ind + "elseif " + ex(e.condition, cx) + " then"); blk(e.thenbody, cx, ind + "\t", out); e = e.elsebody; }
        else { out.push(ind + "else"); blk(e, cx, ind + "\t", out); e = null; }
      }
      out.push(ind + "end");
      return;
    }
    case "AstStatWhile": out.push(ind + "while " + ex(n.condition, cx) + " do"); blk(n.body, cx, ind + "\t", out); out.push(ind + "end"); return;
    case "AstStatRepeat": out.push(ind + "repeat"); blk(n.body, cx, ind + "\t", out); cx.ind = ind; out.push(ind + "until " + ex(n.condition, cx)); return;
    case "AstStatFor": {
      const h = ex(n.from, cx) + ", " + ex(n.to, cx) + (n.step ? ", " + ex(n.step, cx) : "");
      out.push(ind + "for " + cx.def(n.var) + " = " + h + " do"); blk(n.body, cx, ind + "\t", out); out.push(ind + "end"); return;
    }
    case "AstStatForIn": {
      const v = xs(n.values);
      out.push(ind + "for " + n.vars.map((x) => cx.def(x)).join(", ") + " in " + v + " do"); blk(n.body, cx, ind + "\t", out); out.push(ind + "end"); return;
    }
    case "AstStatLocalFunction": { const nm = cx.def(n.name); out.push(ind + "local function " + nm + fnbody(n.func, cx)); return; }
    case "AstStatFunction": out.push(ind + "function " + ex(n.name, cx) + fnbody(n.func, cx)); return;
  }
  throw new Error("native statement " + n.type);
}

let seq = 90000;
function natsrc(nat, items, ind, name, raw) {
  const names = new Map(), boxes = new Set(nat.boxes);
  const cx = {
    ind, raw: !!raw,
    def(l) { const nm = "r" + (++seq); names.set(l.location, nm); return nm; },
    use(l) {
      if (l.location === nat.param) throw new Error("native upvalue table used directly");
      const nm = names.get(l.location); if (nm === undefined) throw new Error("native local " + l.name + " not bound");
      return nm;
    },
    sub(n) {
      const isup = (e) => e.type === "AstExprLocal" && e.local.location === nat.param;
      const idx = (e) => (e.type === "AstExprConstantNumber" && Number.isInteger(e.value) && e.value >= 1 && e.value <= items.length) ? e.value : 0;
      if (n.expr.type === "AstExprIndexExpr" && isup(n.expr.expr) && idx(n.expr.index) && boxes.has(idx(n.expr.index)) && n.index.type === "AstExprConstantNumber" && n.index.value === 1) return items[idx(n.expr.index) - 1];
      if (isup(n.expr)) {
        const i = idx(n.index);
        if (!i) throw new Error("native upvalue index " + JSON.stringify(n.index).slice(0, 80));
        if (boxes.has(i)) throw new Error("native box " + i + " used as a value");
        return items[i - 1];
      }
      return null;
    },
  };
  return "function" + (name || "") + fnbody(nat.fn, cx);
}

function item(text, p) {
  const m = /^(?:[A-Za-z_][A-Za-z0-9_]*|-?\d+(?:\.\d+)?(?:e[-+]?\d+)?|"(?:[^"\\\n]|\\.)*")/.exec(text.slice(p, p + 4000));
  return m ? m[0] : null;
}
function splice(text, natives) {
  let out = "", from = 0;
  for (;;) {
    const at = text.indexOf("return __devert_native_", from);
    if (at < 0) break;
    const im = /^return __devert_native_([0-9_]+)/.exec(text.slice(at, at + 80));
    const nat = im && natives[im[1]];
    if (!nat) throw new Error("native marker without a native " + (im ? im[1] : "?"));
    let p = at + im[0].length; const items = [];
    for (;;) {
      const c = /^[ \t]*,[ \t]*/.exec(text.slice(p, p + 200));
      if (!c) break;
      p += c[0].length;
      const it = item(text, p); if (it === null) throw new Error("native marker item at " + p);
      items.push(it); p += it.length;
    }
    const em = /^\s*end/.exec(text.slice(p, p + 400));
    if (!em) throw new Error("native marker closure has more than the marker return");
    const end = p + em[0].length;
    const head = text.slice(Math.max(from, at - 400), at);
    const fm = /function(\s+[A-Za-z_][A-Za-z0-9_.:]*)?\s*\(\s*\)\s*$/.exec(head);
    if (!fm) throw new Error("native marker closure head not found");
    const fstart = at - head.length + fm.index;
    if (items.length !== nat.n) throw new Error("native marker has " + items.length + " upvalues, expected " + nat.n);
    for (const b of nat.boxes) if (!isid(items[b - 1])) throw new Error("native box upvalue " + b + " is not a variable: " + items[b - 1]);
    const ls = text.lastIndexOf("\n", fstart) + 1;
    const ind = /^[ \t]*/.exec(text.slice(ls, fstart))[0];
    out += text.slice(from, fstart) + natsrc(nat, items, ind, fm[1] || "");
    from = end;
  }
  out += text.slice(from);
  if (out.includes("__devert_native_")) throw new Error("native marker left in the output");
  return out;
}

module.exports = { splice, natsrc };

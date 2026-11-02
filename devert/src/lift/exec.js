"use strict";
const sym = require("./sym.js");
const ir = require("./ir.js");
const dvl = require("./dval.js");
const {
  LTbl, Bltn, LFn, RegF, EnvTbl, Scp, Unsup,
  Const, Reg, Psd, Glob, Upv, Idx, Bin, Un, TmpVal, ClsExpr,
  Multi, TmpTail, VargTail, SymLst, TailCnt, NewTbl,
  issym, isby, nmkey, kstr, tru, fixint, lnum, leq, arith, fmtnum,
  BrkSig, ContSig,
} = sym;
const { Asgn, CallStmt, SetLst, Close, GenIter } = ir;
const {
  sbase, obase, lbase, hbase, lvbase, bbase, snbase,
  FnRef, Stor, _unsto, InsPrx, BoxTbl, KGlob, Lin, SprIdx, Spr,
  BoxRef, MbBox, UpLst, VmCls, GtrProto, GiRef, ChkRes,
  _Lost, vglob, nfold, trt, bool, taint, tblid,
  hhas, hget, hsetraw, hdel, hitems, hkeys, hclr,
  _cpfresh, _isphan, _samefact, repr,
} = dvl;
const fmtexpr = ir.fmtexpr;
const { St } = require("./state.js");
const { tkiter, tktop, tktab, tkovl } = dvl;

const { sglobs } = require("./dtables.js");
const _cmp = ["CompareEq", "CompareNe", "CompareLt", "CompareLe", "CompareGt", "CompareGe"];

function _hashl(name) {
  if (!isby(name)) return false;
  return /^_[0-9a-f]{12,}$/.test(name.toString("latin1"));
}
function mainproto() { return 0; }

function _mutrefs(e, lim) {
  lim = lim || 40;
  const out = new Set(); const st = [e]; let n = 0;
  while (st.length) {
    const x = st.pop(); n += 1;
    if (n > lim) return null;
    if (x && x.k === "Reg") out.add("r," + x.n);
    else if (x && x.k === "Upval") out.add("u," + x.idx);
    else if (x && x.k === "Global" && !(x instanceof KGlob)) out.add("g," + x.name);
    else if (x && x.k === "Index") { out.add("idx"); st.push(x.obj, x.key); }
    else if (x && x.k === "Bin") st.push(x.a, x.b);
    else if (x && x.k === "Un") st.push(x.a);
  }
  return out;
}
function _regsin(x) {
  const out = new Set(); const st = [x]; let seen = 0;
  while (st.length) {
    const y = st.pop(); seen += 1; if (seen > 20000) break;
    if (y && y.k === "Reg") { if (hbase <= y.n && y.n < obase) out.add(y.n); }
    else if (Array.isArray(y)) for (const e of y) st.push(e);
    else if (y && y.k === "Multi") for (const e of y.items) st.push(e);
    else if (y && y.s === "Assign") { st.push(y.value); if (!(y.target && y.target.k === "Reg")) st.push(y.target); }
    else if (y && typeof y === "object") {
      for (const kk of Object.keys(y)) { const vv = y[kk]; if (vv && (typeof vv === "object")) st.push(vv); }
    }
  }
  return out;
}
const _hloop = new Map();
function _hldsloop(st, loc) {
  const hit = _hloop.get(st);
  if (hit && hit[0] === loc) return hit[1];
  let fnd = false; const todo = [st.body];
  while (todo.length && !fnd) {
    const x = todo.pop();
    if (x && typeof x === "object" && !Array.isArray(x)) {
      const t = x.type;
      if (t === "AstExprFunction") continue;
      if ((t === "AstStatWhile" || t === "AstStatForIn" || t === "AstStatFor" || t === "AstStatRepeat") && x.location === loc) fnd = true;
      for (const kk of Object.keys(x)) todo.push(x[kk]);
    } else if (Array.isArray(x)) for (const e of x) todo.push(e);
  }
  _hloop.set(st, [loc, fnd]);
  return fnd;
}
function _astkey(e) {
  if (e && typeof e === "object" && !Array.isArray(e)) {
    const prts = [];
    for (const k of Object.keys(e)) if (k !== "location") prts.push([k, _astkey(e[k])]);
    prts.sort((a, b) => (a[0] < b[0] ? -1 : a[0] > b[0] ? 1 : 0));
    return JSON.stringify(prts);
  }
  if (Array.isArray(e)) return JSON.stringify(e.map(_astkey));
  return JSON.stringify(e === undefined ? null : e);
}
const _ttst = new Map();
function _trutest(node) {
  if (_ttst.has(node)) return _ttst.get(node);
  const strp = (e) => { while (e.type === "AstExprGroup") e = e.expr; return e; };
  const side = (e) => {
    e = strp(e);
    if (e.type !== "AstExprBinary" || e.op !== "CompareNe") return null;
    const a = strp(e.left), b = strp(e.right);
    for (const [x, c] of [[a, b], [b, a]]) {
      if (c.type === "AstExprConstantNil") return [x, "nil"];
      if (c.type === "AstExprConstantBool" && c.value === false) return [x, "false"];
    }
    return null;
  };
  let out = null;
  const l = side(node.left), r = side(node.right);
  if (l && r) {
    const set = new Set([l[1], r[1]]);
    if (set.has("nil") && set.has("false") && _astkey(l[0]) === _astkey(r[0])) out = l[0];
  }
  _ttst.set(node, out);
  return out;
}
function _wr(st) {
  if (st && st.s === "Assign") {
    const t = st.target;
    if (t && t.k === "Reg") return new Set(["r," + t.n]);
    if (t && t.k === "Upval") return new Set(["u," + t.idx]);
    if (t && t.k === "Global" && !(t instanceof KGlob)) return new Set(["g," + t.name]);
    if (t && t.k === "Index") return new Set(["idx"]);
    return new Set();
  }
  if (st && st.s === "CallStmt") return new Set(["idx", "g*", "u*"]);
  if (st && st.s === "SetList") return new Set(["idx"]);
  return new Set();
}

function _isresfn(fn) {
  if (!fn.vararg || fn.args.length !== 1) return false;
  const b = fn.body.body;
  if (!b.length || b[0].type !== "AstStatLocal" || b[0].values.length !== 1) return false;
  const v = b[0].values[0];
  if (v.type !== "AstExprCall" || v.args.length !== 2) return false;
  const a0 = v.args[0], a1 = v.args[1];
  return a0.type === "AstExprConstantString" && a0.value === "#" && a1.type === "AstExprVarargs";
}
function _restop(fn) {
  const b = fn.body.body; const n = b[0].vars[0].location;
  for (const st of b) if (st.type === "AstStatAssign" && st.vars.length === 1 && st.vars[0].type === "AstExprLocal" && st.values.length === 1 && st.values[0].type === "AstExprLocal" && st.values[0].local.location === n) return st.vars[0].local.location;
  return null;
}
function _isgifn(fn) {
  if (!fn || typeof fn !== "object" || fn.type !== "AstExprFunction" || (fn.args && fn.args.length)) return false;
  const b = fn.body.body;
  if (b.length !== 1 || b[0].type !== "AstStatForIn" || b[0].values.length !== 3) return false;
  const inr = b[0].body.body;
  return inr.length === 1 && inr[0].type === "AstStatExpr";
}

function boolinteq(a, b) { const v = (x) => x === true ? 1n : x === false ? 0n : x; return v(a) === v(b); }
function keyeq(a, b) { if (a === b) return true; if (isby(a) && isby(b)) return a.equals(b); return a === b; }
function sclsame(a, b) {
  const ty = (x) => (x === null || x === undefined) ? "nil" : typeof x === "boolean" ? "bool" : typeof x === "bigint" ? "int" : typeof x === "number" ? "float" : isby(x) ? "bytes" : "o";
  return ty(a) === ty(b);
}
function scleq(a, b) { if (isby(a) && isby(b)) return a.equals(b); return a === b; }

class ProtoLftr {
  constructor(prog, ci, uplst) {
    this.prog = prog;
    this.dump = prog.dump;
    this.cap = prog.dump.caps[ci];
    this.capidx = ci;
    this.vm = prog.vms.get(this.cap.mk);
    this._lzrslv = false;
    this._lzsnk = new Map();
    this._lzci = null;
    this.curpc = null;
    this.curit = null;
    this.special = {};
    this.out = [];
    this.tcount = 0;
    this.tmppfx = "";
    this.kids = [];
    this.capdregs = new Set();
    this.uplist = uplst;
    const cs = new Scp();
    for (const [k, v] of this.cap.vars) cs.vars.set(k, v);
    const vm = this.vm;
    if (vm.params.length >= 2) cs.vars.set(vm.params[1], uplst);
    this.cscope = cs;
    this.iscope = null;
    this.inprol = false;
    this.carry = prog.crrofget(this.cap.mk);
    this.newcrr = false;
    this.tabcrr = prog.tabcrrofget(this.cap.mk);
    this.stktabs = new Map();
    this.results = new Map();
    this.tsrc = new Map();
    this.boxes = new Map();
    this.top = null;
    this.iters = new Map();
    this.facts = new Map();
    this.ovlslt = new Map();
    this.home = new Map();
    this.lost = new Set();
    this.cons = new Set();
    this.basetabsids = new Set();
    this.tabwrtn = new Map();
    this.nregs = null;
    this.regfill = false;
    this.entwrtn = new Set();
    this.enttop = null;
    this.wrtnnow = new Set();
    this.hloc = new Map();
    this.snap = new Map();
    this.held = [];
    this.hrepl = [];
    this.lvreg = new Map();
    this.boxvars = new Map();
    this.stprds = new Set();
    this.pcuse = new Map();
    this.live = null;
    this.chktmps = new Set();
    this.lvact = new Map();
    this.basevals = new Map();
    this.basetabs = new Map();
  }

  _fk(slot) {
    if (typeof slot === "number") return "R" + slot;
    if (Array.isArray(slot)) {
      if (slot[0] === "ovl") return "ovl|" + slot[1] + "|" + kstr(nmkey(slot[2]));
      return slot[0] + "|" + slot[1];
    }
    return "?" + String(slot);
  }
  fhas(slot) { return this.facts.has(this._fk(slot)); }
  fget(slot) { const r = this.facts.get(this._fk(slot)); return r === undefined ? undefined : r.v; }
  fset(slot, v) { this.facts.set(this._fk(slot), { slot, v }); }
  fdel(slot) { this.facts.delete(this._fk(slot)); }
  fpop(slot) { this.facts.delete(this._fk(slot)); }
  *fent() { for (const e of this.facts.values()) yield [e.slot, e.v]; }

  noterd(key) {
    if (this.inprol) return;
    if (!this.wrtnnow.has("L:" + key)) this.stprds.add("L:" + key);
    if (!this.wrtnnow.has("L:" + key) && !this.carry.has(key) && key !== this.vm.pcdecl) {
      this.carry.add(key); this.newcrr = true;
    }
  }
  notewr(key) { this.wrtnnow.add("L:" + key); }
  recuse(pc, rds, wr) {
    const u = this.pcuse.get(pc);
    if (u === undefined) this.pcuse.set(pc, [new Set(rds), new Set(wr)]);
    else { for (const r of rds) u[0].add(r); for (const w of [...u[1]]) if (!wr.has(w)) u[1].delete(w); }
  }
  lvns(nds, stts) {
    const succ = new Map();
    for (const [k, n] of nds) {
      const out = []; _nextst(n, out);
      const pc = stts.get(k).pc;
      if (!succ.has(pc)) succ.set(pc, new Set());
      for (const ns of out) succ.get(pc).add(ns.pc);
    }
    const live = new Map();
    for (const [pc, u] of this.pcuse) live.set(pc, new Set(u[0]));
    let chg = true;
    while (chg) {
      chg = false;
      for (const [pc, ss] of succ) {
        const u = this.pcuse.get(pc); if (u === undefined) continue;
        if (!live.has(pc)) live.set(pc, new Set());
        const cur = live.get(pc); const add = new Set();
        for (const x of ss) { const lx = live.get(x); if (lx) for (const e of lx) add.add(e); }
        for (const w of u[1]) add.delete(w);
        let grew = false; for (const a of add) if (!cur.has(a)) { cur.add(a); grew = true; }
        if (grew) chg = true;
      }
    }
    const pcd = this.vm.pcdecl; const out = new Map();
    for (const [pc, v] of live) { const s = new Set(v); s.add(pcd); out.set(pc, s); }

    for (const [pc, u] of this.pcuse) if (!out.has(pc)) { const s = new Set(u[0]); s.add(pcd); out.set(pc, s); }
    return out;
  }

  lclval(key, v) {
    if (v && v.k === "Multi") v = sym.multifst(v);
    if (issym(v) && !(v instanceof Lin) && !(v instanceof SprIdx)) {
      if (key === this.vm.pcdecl) {
        const c = this.fval(v);
        if (typeof c === "bigint") return c;
      }
      const r = Reg(lbase + (this.vm.ilocidx.get(key) || 0));
      if (!(v.k === "Reg" && v.n === r.n)) {
        this.emit(Asgn(r, this.valof(v)));
        if (this.isbool(v)) this.fset(r.n, bool); else this.fpop(r.n);
      }
      return r;
    }
    return v;
  }

  hold(key, v, scp) {
    if (this.inprol || !issym(v) || v instanceof Lin || v instanceof SprIdx ||
      (v.k === "Const") || (v.k === "TempVal") || (v.k === "Vararg") || (v.k === "ClosureExpr") || (v instanceof KGlob)) return v;
    const refs = _mutrefs(v);
    if (refs === null) {
      const n = this._hloc(key); const r = Reg(hbase + n);
      const c = this.fval(v);
      this.emit(Asgn(r, v)); this.fpop(r.n);
      if (c !== nfold) this.fset(r.n, c); else if (this.isbool(v)) this.fset(r.n, bool);
      return r;
    }
    if (refs.size) this.held.push([scp, key, v, refs]);
    return v;
  }
  _hloc(key) { if (!this.hloc.has(key)) this.hloc.set(key, this.hloc.size + 1); return this.hloc.get(key); }

  _mtrl(st) {
    const w = _wr(st);
    if (!w.size) return;
    const keep = [];
    for (const ent of this.held) {
      const [sc, key, v, refs] = ent;
      if (sc.vars.get(key) !== v) continue;
      const hitg = w.has("g*") && [...refs].some((x) => typeof x === "string" && x.startsWith("g,"));
      const hitu = w.has("u*") && [...refs].some((x) => typeof x === "string" && x.startsWith("u,"));
      const hit = [...refs].some((r) => w.has(r)) || hitg || hitu;
      if (!hit) { keep.push(ent); continue; }
      const n = this._hloc(key); const r = Reg(hbase + n);
      const c = this.fval(v); const cp = Asgn(r, v); cp.hcopy = true;
      this.out.push(cp); this.fpop(r.n);
      if (c !== nfold) this.fset(r.n, c); else if (this.isbool(v)) this.fset(r.n, bool);
      sc.vars.set(key, r);
      if (st.s === "Assign" && st.value === v) { st.value = r; this.hrepl.push([st, r.n, v]); }
    }
    this.held = keep;
  }

  *parvals(vals) {
    if (this.inprol) { yield* vals; return; }
    const sc = new Scp(null); const keys = [];
    for (let i = 0; i < vals.length; i++) {
      const key = "parallel," + i;
      sc.vars.set(key, i === 0 ? vals[0] : this.hold(key, vals[i], sc));
      keys.push(key);
    }
    for (const key of keys) {
      this.held = this.held.filter((e) => !(e[0] === sc && e[1] === key));
      yield sc.vars.get(key);
    }
  }

  prncps(it, retvals) {
    if (!this.out.some((x) => x.hcopy)) return;
    const live = new Set();
    for (const d of it.dlog) for (const r of _regsin(d[2])) live.add(r);
    if (retvals !== undefined && retvals !== null) for (const r of _regsin(retvals)) live.add(r);
    const drop = new Set();
    for (let i = this.out.length - 1; i >= 0; i--) {
      const st = this.out[i];
      if (st.hcopy && !live.has(st.target.n)) { drop.add(i); continue; }
      for (const r of _regsin(st)) live.add(r);
    }
    if (!drop.size) return;
    const gone = new Set([...drop].map((i) => this.out[i].target.n));
    for (const [st, rn, v] of this.hrepl) if (gone.has(rn) && st.value && st.value.k === "Reg" && st.value.n === rn) st.value = v;
    const npos = []; let k = 0;
    for (let i = 0; i <= this.out.length; i++) { npos.push(k); if (i < this.out.length && !drop.has(i)) k += 1; }
    this.out = this.out.filter((_, i) => !drop.has(i));
    it.dlog = it.dlog.map(([a, b, c, d]) => [a, npos[b], c, d]);
  }

  initst() {
    const vm = this.vm; const sc = new Scp(this.cscope);
    sc.vars.set("...", Multi([], VargTail(1)));
    this.iscope = sc; this.wrtnnow = new Set(); this.out = []; this.held = [];
    this.inprol = true;
    const it = new LiftItp(this);
    it.execblk(vm.prol, sc);
    this.inprol = false;
    this.entwrtn = new Set();
    for (const x of this.wrtnnow) if (x.startsWith("iter:")) this.entwrtn.add(parseInt(x.slice(5), 10));
    this.enttop = this.top;
    this.entout = this.out.filter((x) => x.s === "Assign" && x.target && x.target.k === "Reg");
    this.out = [];
    this.basevals = new Map(sc.vars);
    this.basetabs = new Map();
    let np = 0;
    for (const [, v] of sc.vars) {
      if (v instanceof LTbl && v.tid === null) {
        v.tid = "P" + np; np += 1;
        this.basetabs.set(v.tid, [v, new Map(v.h)]);
      }
    }
    return this.snps(sc);
  }

  entfcts() {
    if (this.nregs === null || this.regfill) return new Map();
    const top = this.enttop !== null ? this.enttop[0] : null;
    const out = new Map();
    for (let r = 0; r <= this.nregs; r++) {
      if (!this.entwrtn.has(r) && !this.boxes.has(r) && (top === null || BigInt(r) < top)) out.set("R" + r, { slot: r, v: null });
    }
    return out;
  }

  snps(sc, sub) {
    const vals = [];
    const crrkeys = [...new Set([...this.carry, this.vm.pcdecl])].sort(cmpstr);
    for (const k of crrkeys) vals.push([k, sc.vars.has(k) ? sc.vars.get(k) : null]);
    const pc = sc.vars.get(this.vm.pcdecl);
    const tabs = [];
    const tids = [...this.basetabs.keys()].sort(cmpstr);
    for (const tid of tids) {
      const [t] = this.basetabs.get(tid);
      if (this.tabcrr.has(tid)) tabs.push([tid, new Map(t.h)]);
    }
    return new St(pc === undefined ? null : pc, vals, tabs, new Map(this.boxes), this.top, new Map(this.iters),
      new Map(this.facts), new Set(this.lost), sub === undefined ? null : sub, this.live);
  }

  restore(st, fcts, lost) {
    const sc = new Scp(this.cscope);
    sc.vars = new Map(this.basevals);
    const memo = new Map();
    for (const [k, v] of st.vals) sc.vars.set(k, _cpfresh(v, memo));
    for (const [, [t, h]] of this.basetabs) t.h = new Map(h);
    for (const [tid, h] of st.tabs) {
      const nh = new Map();
      for (const e of h.values()) { const nk = _cpfresh(e.kk, memo); nh.set(kstr(nmkey(nk)), { kk: nmkey(nk), v: _cpfresh(e.v, memo) }); }
      this.basetabs.get(tid)[0].h = nh;
    }
    this.boxes = new Map(st.boxes);
    this.top = st.top;
    this.iters = new Map(); for (const [r, v] of st.iters) this.iters.set(r, _cpfresh(v, memo));
    const srcfcts = fcts === undefined || fcts === null ? st.facts : fcts;
    this.facts = new Map(); for (const e of srcfcts.values()) this.facts.set(this._fk(e.slot), { slot: e.slot, v: _cpfresh(e.v, memo) });
    this.lost = lost === undefined || lost === null ? new Set(st.lost) : new Set(lost);
    this.home = new Map();
    const intslt = [...this.facts.values()].filter((e) => typeof e.slot === "number").map((e) => e.slot).sort((a, b) => a - b);
    for (const r of intslt) {
      const f = this.fget(r);
      if (f instanceof LTbl && f.tid === null && !this.home.has(f) && !this.isscr(r)) this.home.set(f, r);
    }
    this.results = new Map(); this.tsrc = new Map(); this.cons = new Set(); this.held = []; this.hrepl = [];
    this.lvact = new Map(); this.iscope = sc; this.wrtnnow = new Set(); this.stprds = new Set();
    return sc;
  }

  scrub(sc) {
    for (const [slot] of [...this.fent()]) if (typeof slot === "number" && hbase <= slot && slot < obase) this.fdel(slot);
    if (this.top !== null && this.cons.has(this.top[1])) this.top = null;
    const live = new Set();
    if (this.top !== null) live.add(this.top[1].tail);
    for (const [, [t]] of this.basetabs) {
      for (const [k, v] of hitems(t)) {
        if (v instanceof Spr && this.cons.has(v.m)) hdel(t, k);
        else if (v instanceof Spr && v.m.tail !== null) live.add(v.m.tail);
      }
    }
    for (const [k, v] of [...sc.vars]) {
      if (v instanceof Lin && v.tail && v.tail.k === "TempTail" && !live.has(v.tail)) sc.vars.set(k, this.basevals.has(k) ? this.basevals.get(k) : null);
    }
  }

  isdisp(node) { return node === this.vm.loop; }
  emit(st) { if (this.held.length) this._mtrl(st); this.out.push(st); }
  newtmp() { this.tcount += 1; return this.tmppfx + this.tcount; }
  specget(sp) { throw new Unsup(String(sp)); }
  specset(sp) { throw new Unsup(String(sp)); }
  globval(name) {
    const g = this.prog.globals; const v = hget(g, Buffer.from(name, "latin1"));
    return v !== null ? v : Glob(name);
  }
  varargs(scp) {
    let s = scp;
    while (s !== null) { if (s.vars.has("...")) return s.vars.get("..."); s = s.parent; }
    throw new Unsup("varargs outside vararg function");
  }
  setglob() { throw new Unsup("assignment to global in VM code"); }

  asexpr(v) {
    if (v instanceof _Lost) v.fail();
    if (v instanceof Stor) {
      const c = v.const;
      if (c === null || typeof c === "boolean" || typeof c === "bigint" || typeof c === "number" || isby(c)) return Const(c);
      return this.asexpr(v.expr);
    }
    if (v instanceof Lin) return v.asexpr();
    if (v instanceof BoxRef) return v.target;
    if (v instanceof SprIdx) return v;
    if (issym(v)) return v;
    if (v && v.k === "Vec") return v;
    if (v === null || v === undefined || typeof v === "boolean" || typeof v === "bigint" || typeof v === "number" || isby(v)) return Const(v === undefined ? null : v);
    if (v && v.k === "Multi") return this.asexpr(sym.multifst(v));
    if (v instanceof EnvTbl) return Glob("_ENV");
    if (v instanceof Bltn) return Glob(v.name);
    if (v instanceof Spr) return this.asexpr(sym.multifst(v.m));
    if (v instanceof LTbl && v.tid === null) return this.tblexpr(v);
    if (v instanceof LFn) {
      const ci = this._capfrmwrp(v);
      if (ci !== null && ci !== undefined) { const ups = this._upsfrmwrp(v); if (ups !== null) return this._bldcls(ci, ups); }
      const g = this._smpgtr(v); if (g !== null) return g;
      if ((ci === null || ci === undefined) && this._lzmkrfn(v) !== null) {
        const it = this.curit;
        if (it === null || _capfork(it)) throw new _DeadFork();
        return this._stubcls();
      }
    }
    throw new Unsup("value " + repr(v) + " in an expression");
  }
  tblexpr(v) {
    const r = this.escape(v); if (r !== null) return r;
    return NewTbl(this.ctoritms(v));
  }
  ctoritms(t) {
    const h = new Map();
    for (const [k, x] of hitems(t)) if (k !== tblid && k !== taint) h.set(k, x);
    const get = (i) => { for (const [k, x] of h) if (typeof k === "bigint" && k === i) return x; return undefined; };
    const has = (i) => { for (const k of h.keys()) if (typeof k === "bigint" && k === i) return true; return false; };
    let n = 0n; while (has(n + 1n)) n += 1n;
    const itms = [];
    for (let i = 1n; i <= n; i++) itms.push([null, this.valof(get(i))]);
    for (const [k, x] of h) {
      if (typeof k === "bigint" && 1n <= k && k <= n) continue;
      itms.push([issym(k) ? k : Const(k), this.valof(x)]);
    }
    return itms;
  }
  valof(v) {
    if (v && v.k === "Multi") v = sym.multifst(v);
    if (v && (v.k === "ClosureExpr" || v.k === "GenIter" || v.k === "SymList")) return v;
    if (v instanceof LTbl) {
      if (v.tid === null) return this.tblexpr(v);
      throw new Unsup("storing a VM table into a register (table " + v.tid + ")");
    }
    return this.asexpr(v);
  }

  symbinop(op, a, b) {
    if (a instanceof Lin || a instanceof SprIdx || b instanceof Lin || b instanceof SprIdx) return this.linbinop(op, a, b);
    if (["Add", "Sub", "Mul", "Div", "FloorDiv", "Mod", "Pow"].includes(op)) {
      const isinj = (x) => (x && (x.k === "ClosureExpr")) || x instanceof FnRef || x instanceof VmCls || x instanceof LFn || x instanceof ChkRes;
      const inj = (x) => { if (isinj(x)) return true; if (x && x.k === "Reg") return isinj(this.fget(x.n)) || isinj(this.fget(["clo", x.n])); return false; };
      if (inj(a) || inj(b)) return 0n;
    }
    if (op === "CompareEq" || op === "CompareNe") {
      for (const [x, y] of [[a, b], [b, a]]) {
        if (typeof x === "boolean" || !this.isbool(x)) continue;
        let c;
        if (y === null || typeof y === "boolean") c = y;
        else c = issym(y) ? this.fval(y) : nfold;
        if (c === null) return op === "CompareNe";
        if (typeof c === "boolean") { const xe = this.asexpr(x); return (c === true) === (op === "CompareEq") ? xe : Un("Not", xe); }
      }
    }
    if (op === "CompareEq" || op === "CompareNe") {
      const vm = (x) => x instanceof RegF || x instanceof UpLst || x instanceof LTbl || x instanceof FnRef || x instanceof VmCls;
      if (vm(a) || vm(b)) return op === "CompareNe";
    }
    if ((a && a.k === "SymList") || a instanceof RegF || (b && b.k === "SymList") || b instanceof RegF) throw new Unsup("arith on VM object");
    return Bin(op, this.asexpr(a), this.asexpr(b));
  }
  linbinop(op, a, b) {
    const num = (x) => typeof x === "bigint";
    if (op === "Add" && a instanceof Lin && num(b)) return new Lin(a.c + b, a.tail);
    if (op === "Add" && b instanceof Lin && num(a)) return new Lin(b.c + a, b.tail);
    if (op === "Sub" && a instanceof Lin && num(b)) return new Lin(a.c - b, a.tail);
    if (op === "Add" && a instanceof SprIdx && num(b)) return new SprIdx(a.start + b);
    if (op === "Add" && b instanceof SprIdx && num(a)) return new SprIdx(b.start + a);
    if (op === "Sub" && a instanceof SprIdx && num(b)) return new SprIdx(a.start - b);
    if (op === "Sub" && a instanceof Lin && b instanceof Lin && a.tail === b.tail) return a.c - b.c;
    if (["CompareLt", "CompareLe", "CompareGt", "CompareGe", "CompareEq", "CompareNe"].includes(op)) {
      if (a instanceof Lin && num(b)) {
        const lo = a.c;
        if ((op === "CompareGt" || op === "CompareGe") && b >= lo + 200n) return false;
        if ((op === "CompareLt" || op === "CompareLe") && b >= lo + 200n) return true;
        if (op === "CompareGe" && b <= lo) return true;
        if (op === "CompareLt" && b <= lo) return false;
        if (b <= 0n && (op === "CompareLt" || op === "CompareGe")) return op === "CompareGe";
      }
      if (b instanceof Lin && num(a)) {
        const flip = { CompareLt: "CompareGt", CompareLe: "CompareGe", CompareGt: "CompareLt", CompareGe: "CompareLe", CompareEq: "CompareEq", CompareNe: "CompareNe" }[op];
        return this.linbinop(flip, b, a);
      }
      return Bin(op, this.asexpr(a), this.asexpr(b));
    }
    if (op === "Sub" && a instanceof Lin && typeof b === "bigint") return new Lin(a.c - b, a.tail);
    return Bin(op, this.asexpr(a), this.asexpr(b));
  }
  symunop(op, a) {
    if (a && a.k === "SymList") { if (op === "Len") return TailCnt(a.tail); throw new Unsup("unop on packed list"); }
    return Un(op, this.asexpr(a));
  }

  regrd(k) {
    if (k instanceof SprIdx) {
      if (this.top === null) throw new Unsup("register spread without a multiple result");
      const [base, m] = this.top;
      if (!this.wrtnnow.has("top")) this.stprds.add("top");
      let m2;
      if (k.start < base) { const pre = []; for (let r = k.start; r < base; r++) pre.push(this.regrd(r)); m2 = Multi(pre.map((x) => this.asexpr(x)).concat(m.items), m.tail); }
      else if (k.start === base) m2 = m;
      else throw new Unsup("register spread above the multiple result");
      this.cons.add(m); return new Spr(m2);
    }
    if (issym(k)) { const c = this.fval(k); if (c === nfold) throw new Unsup("symbolic register index " + fmtexpr(k)); k = c; }
    k = nmkey(k);
    if (typeof k !== "bigint") throw new Unsup("register index " + repr(k));
    const kn = Number(k);
    if (this.boxes.has(kn)) return new BoxRef(this.boxes.get(kn));
    if (this.iters.has(kn)) { if (!this.wrtnnow.has(tkiter(kn))) this.stprds.add(tkiter(kn)); return this.iters.get(kn); }
    if (this.fhas(kn)) {
      const f = this.fget(kn);
      if (f instanceof Bltn) return new KGlob(f.name);
      if (_isphan(f) || f instanceof LTbl || f === vglob) return f;
      return Reg(kn);
    }
    if (this.lost.has(kn)) return new _Lost(kn);
    if (this.top !== null && BigInt(kn) === this.top[0]) return this.asexpr(sym.multifst(this.top[1]));
    return Reg(kn);
  }
  fgtfrm(base) {
    if (this.nregs === null || typeof base !== "bigint" && typeof base !== "number") return;
    const b = Number(base);
    for (const [slot] of [...this.fent()]) if (typeof slot === "number" && b <= slot && slot <= this.nregs) this.fdel(slot);
  }
  regwr(k, v) {
    if (k instanceof SprIdx) {
      if (!(v instanceof Spr)) throw new Unsup("register spread store of " + repr(v));
      this.fgtfrm(k.start); this.top = [k.start, v.m]; this.wrtnnow.add("top"); return;
    }
    if (issym(k)) { const c = this.fval(k); if (c === nfold) throw new Unsup("symbolic register store " + fmtexpr(k)); k = c; }
    k = nmkey(k);
    if (typeof k !== "bigint") throw new Unsup("register store at " + repr(k));
    const kn = Number(k);
    if (v && v.k === "Multi") v = sym.multifst(v);
    if (v && v.k === "Reg" && v.n === kn && !this.boxes.has(kn) && !this.iters.has(kn)) return;
    if (v instanceof _Lost) {
      if (this.top !== null && BigInt(kn) <= this.top[0]) this.top = null;
      this.fpop(kn); this.fpop(["clo", kn]); this.fpop(["glob", kn]); this.iters.delete(kn); this.boxes.delete(kn);
      this.lost.add(kn); return;
    }
    const nfact = (issym(v) && !(v instanceof Lin) && !(v instanceof SprIdx)) ? this.fval(v) : nfold;
    if (this.top !== null && BigInt(kn) <= this.top[0]) this.top = null;
    this.iters.delete(kn); this.wrtnnow.add(tkiter(kn));
    const ofact = this.fhas(kn) ? this.fget(kn) : nfold; this.fpop(kn);
    this.fpop(["clo", kn]); this.fpop(["glob", kn]);
    if (this.lost.has(kn)) this.lost.delete(kn);
    if (v instanceof Spr) { this.fgtfrm(k); this.top = [k, v.m]; this.wrtnnow.add("top"); return; }
    if (v && v.k === "TempVal" && this.chktmps.has(v.t)) { this.fset(kn, new ChkRes(v.i)); return; }
    if (v instanceof BoxTbl && hkeys(v).length === 1 && hkeys(v)[0] === 1n) {
      let inr = hget(v, 1n);
      const pc = this.iscope !== null ? this.iscope.vars.get(this.vm.pcdecl) : null;
      const bkey = repr(pc) + "|" + kn;
      if (!this.boxvars.has(bkey)) this.boxvars.set(bkey, this.boxvars.size + 1);
      const bv = Reg(bbase + this.boxvars.get(bkey));
      this.emit(Close(bv.n));
      if (inr instanceof LTbl && inr.tid === null) { this.regwr(k, inr); this.escape(inr); inr = Reg(kn); }
      if (inr !== null && inr !== undefined) this.emit(Asgn(bv, this.valof(inr)));
      this.boxes.set(kn, bv.n === undefined ? bv : bv); this.boxes.set(kn, bv); return;
    }
    if (v instanceof BoxRef) { this.boxes.set(kn, v.target); return; }
    this.boxes.delete(kn);
    if (v instanceof GiRef) {
      const pv = Psd("a", kn);
      this.emit(Asgn(pv, GenIter(Multi([null].concat(v.args.map((x) => this.asexpr(x)))))));
      this.iters.set(kn, pv); return;
    }
    if (_isphan(v) || v === vglob) { this.fset(kn, v); return; }
    if (v instanceof LTbl) {
      const h = this.homeof(v); this.fset(kn, v);
      if (!this.isscr(kn) && (h !== null || hhas(v, taint))) {
        if (h !== null) { const st = Asgn(Reg(kn), Reg(h)); this.emit(st); if (hhas(v, tblid)) this.prog.tblstmtsadd(hget(v, tblid), st); }
        return;
      }
      if (!this.isscr(kn)) {
        const src = this.tsrc.get(v);
        if (src !== undefined && hhas(v, tblid)) {
          const [o, key] = src; const ho = this.homeof(o);
          if (ho !== null && o.get(key) === v) {
            this.home.set(v, kn); this.prog.usedtbl(o);
            const st = Asgn(Reg(kn), Idx(Reg(ho), this.asexpr(key))); this.emit(st);
            this.prog.tblstmtsadd(hget(v, tblid), st); return;
          }
        }
        this.home.set(v, kn);
        const st = Asgn(Reg(kn), NewTbl(this.ctoritms(v))); this.emit(st);
        const n = this.prog.newtblid(); hsetraw(v, tblid, n); this.prog.tblstmtsadd(n, st);
      }
      return;
    }
    if (v === null || v === undefined || typeof v === "boolean" || typeof v === "bigint" || typeof v === "number" || isby(v)) {
      if (this.held.length && ofact !== nfold) this.fset(kn, ofact);
      this.emit(Asgn(Reg(kn), Const(v === undefined ? null : v))); this.fset(kn, v === undefined ? null : v); return;
    }
    const val = this.valof(v); const c = nfact;
    this.emit(Asgn(Reg(kn), val));
    if (c !== nfold) this.fset(kn, c); else if (this.isbool(val)) this.fset(kn, bool);
    if (val && val.k === "ClosureExpr") this.fset(["clo", kn], val);
    else if (val && val.k === "Global") this.fset(["glob", kn], val.name);
  }
  isscr(k) { return this.nregs !== null && typeof k === "number" && k > this.nregs; }

  isbool(e) {
    if (typeof e === "boolean") return true;
    if (e && e.k === "Const") return typeof e.v === "boolean";
    if (e && e.k === "Bin") { if (_cmp.includes(e.op)) return true; return (e.op === "And" || e.op === "Or") && this.isbool(e.a) && this.isbool(e.b); }
    if (e && e.k === "Un") return e.op === "Not";
    if (e && e.k === "Reg") { const f = this.fget(e.n); return f === bool || typeof f === "boolean"; }
    return false;
  }

  fval(e) {
    if (e === null || e === undefined || typeof e === "boolean" || typeof e === "bigint" || typeof e === "number" || isby(e)) return e === undefined ? null : e;
    if (e.k === "Const") return e.v;
    if (e.k === "Reg") {
      if (this.fhas(e.n)) {
        const f = this.fget(e.n);
        if (f === null || f === trt || typeof f === "boolean" || typeof f === "bigint" || typeof f === "number" || isby(f)) return f;
        if (f instanceof ChkRes) return f.i === 1 ? true : f;
      }
      return nfold;
    }
    if (e.k === "TempVal" && this.chktmps.has(e.t)) return e.i === 1 ? true : new ChkRes(e.i);
    if (e.k === "Global") return (e instanceof KGlob || (e.k === "Global" && !(e instanceof KGlob) && sglobs.has(e.name))) ? trt : nfold;
    if (e.k === "Bin") {
      if (e.op === "CompareEq" || e.op === "CompareNe") {
        for (const [x, y] of [[e.a, e.b], [e.b, e.a]]) if (this.fval(y) === null && this.isbool(x)) return e.op === "CompareNe";
      }
      const a = this.fval(e.a); if (a === nfold) return nfold;
      if (e.op === "And") return tru(a) ? this.fval(e.b) : a;
      if (e.op === "Or") return tru(a) ? a : this.fval(e.b);
      const b = this.fval(e.b);
      if ((a instanceof ChkRes || b instanceof ChkRes) && b !== nfold) { if (e.op === "CompareEq" || e.op === "CompareNe") return e.op === "CompareEq"; return nfold; }
      if (a instanceof ChkRes) return nfold;
      if ((a === trt || b === trt) && (e.op === "CompareEq" || e.op === "CompareNe") && b !== nfold) {
        const oth = a === trt ? b : a; if (oth === null || oth === false) return e.op === "CompareNe";
      }
      if (b === nfold || a === trt || b === trt) return nfold;
      try {
        if (e.op === "CompareEq") return leq(a, b);
        if (e.op === "CompareNe") return !leq(a, b);
        if (["CompareLt", "CompareLe", "CompareGt", "CompareGe"].includes(e.op)) {
          const numok = (typeof a === "bigint" || typeof a === "number") && (typeof b === "bigint" || typeof b === "number");
          const strok = isby(a) && isby(b);
          if (!(numok || strok)) return nfold;
          const c = strok ? Buffer.compare(a, b) : sym.numcmp(a, b);
          return { CompareLt: c < 0, CompareLe: c <= 0, CompareGt: c > 0, CompareGe: c >= 0 }[e.op];
        }
        if (e.op === "Concat") {
          const ok = (x) => (isby(x) || typeof x === "bigint" || typeof x === "number") && typeof x !== "boolean";
          if (ok(a) && ok(b)) { const f = (x) => isby(x) ? x : Buffer.from(fmtnum(x), "latin1"); return Buffer.concat([f(a), f(b)]); }
          return nfold;
        }
        const x = lnum(a), y = lnum(b);
        if (x === null || y === null || typeof a === "boolean" || typeof b === "boolean") return nfold;
        return arith(e.op, x, y);
      } catch (ex) { if (ex instanceof sym.ZeroDivErr || ex instanceof sym.OvfErr || ex instanceof sym.ValErr || ex instanceof Unsup) return nfold; throw ex; }
    }
    if (e.k === "Un") {
      const a = this.fval(e.a); if (a === nfold) return nfold;
      if (e.op === "Not") return !tru(a);
      if (a === trt) return nfold;
      if (e.op === "Minus" && (typeof a === "bigint" || typeof a === "number") && typeof a !== "boolean") return fixint(typeof a === "bigint" ? -a : -a);
      if (e.op === "Len" && isby(a)) return BigInt(a.length);
      return nfold;
    }
    return nfold;
  }
  conckey(key) { if (issym(key)) return this.fval(key); return key; }
  homeof(t) {
    if (hhas(t, taint)) return null;
    const h = this.home.get(t);
    if (h !== undefined && this.fget(h) === t) return h;
    for (const [slot, f] of this.fent()) if (f === t && typeof slot === "number" && !this.isscr(slot)) { this.home.set(t, slot); return slot; }
    return null;
  }
  irref(v, into) {
    if (v instanceof LTbl && v.tid === null) {
      const h = this.homeof(v);
      if (h !== null) { if (into !== undefined && into !== null && hhas(v, tblid) && hhas(into, tblid)) this.prog.tbldepsadd(hget(into, tblid), hget(v, tblid)); return Reg(h); }
    }
    if (v === null || v === undefined) return Const(null);
    return this.valof(v);
  }
  escape(t) {
    const h = this.homeof(t); if (h === null) return null;
    this.prog.usedtbl(t);
    for (const [slot, f] of [...this.fent()]) if (f === t) this.fdel(slot);
    return Reg(h);
  }

  index(obj, key, it) {
    if (obj && obj.k === "Multi") obj = sym.multifst(obj);
    if (key && key.k === "Multi") key = sym.multifst(key);
    for (const x of [obj, key]) if (x instanceof _Lost) x.fail();
    if (obj instanceof RegF) return this.regrd(key);
    if (obj === vglob) return vglob;
    if (obj instanceof BoxRef) { if (key === 1n || key === 1) return obj.target; return null; }
    if (obj instanceof UpLst) {
      if (typeof key !== "bigint") throw new Unsup("upvalue index " + repr(key));
      const kind = this.uplist.kinds[Number(key)];
      if (kind === "box") return new BoxRef(Upv(Number(key)));
      if (Array.isArray(kind) && kind[0] === "const") return kind[1];
      return Upv(Number(key));
    }
    if (obj instanceof EnvTbl) {
      if (issym(key) && this.fval(key) !== nfold) key = this.conckey(key);
      if (isby(key)) {
        if (_hashl(key)) { const v = this.dump.envvals.get(kstr(nmkey(key))); return v instanceof LTbl ? v : vglob; }
        return Glob(key.toString("latin1"));
      }
      return Idx(Glob("_ENV"), this.asexpr(key));
    }
    if (obj instanceof InsPrx) {
      const k = this.conckey(key); const t = k !== nfold ? obj.fields.get(kstr(nmkey(k))) : undefined;
      if (t === undefined) throw new Unsup("instruction proxy field " + repr(key));
      return this.index(t, obj.pc, it);
    }
    if (obj instanceof LTbl && this.dump.prxflds.has(obj)) {
      const k = this.conckey(key); if (typeof k === "bigint") return new InsPrx(this.dump.prxflds.get(obj), k);
    }
    if (obj instanceof LTbl) {
      const lst = this.results.get(obj); if (lst !== undefined) return this.symlstget(lst, key);
      if (key instanceof SprIdx) {
        if (this.basetabsids.has(obj)) {
          const tw = this.tabwrtn.get(obj) || new Set();
          for (let j = key.start; j < key.start + 64n; j++) if (!tw.has(kstr(nmkey(j)))) this.stprds.add(tktab(obj.tid, j));
          if (!this.tabcrr.has(obj.tid)) { this.tabcrr.add(obj.tid); this.newcrr = true; }
        }
        const vals = []; let n = key.start;
        while (n <= key.start + 256n) { const x = _unsto(obj.get(n)); if (x instanceof Spr) return new Spr(Multi(vals.map((v) => this.asexpr(v)).concat(x.m.items), x.m.tail)); vals.push(x); n += 1n; }
        throw new Unsup("spread read of a VM table");
      }
      if (issym(key)) {
        const c = this.fval(key);
        if (c === nfold) {
          if (obj.tid === null) { let r = this.boolidx(obj, key); if (r !== nfold) return r; r = this.escape(obj); if (r !== null) return Idx(r, this.asexpr(key)); }
          throw new Unsup("symbolic index into a concrete VM table (key " + fmtexpr(key) + ")");
        }
        key = c;
      }
      if (this.basetabsids.has(obj) && !(this.tabwrtn.get(obj) || new Set()).has(kstr(nmkey(key)))) {
        this.stprds.add(tktab(obj.tid, key)); if (!this.tabcrr.has(obj.tid)) { this.tabcrr.add(obj.tid); this.newcrr = true; }
      }
      if (typeof obj.tid === "number") {
        const slot = ["ovl", obj.tid, nmkey(key)];
        if (this.fhas(slot) && !this.wrtnnow.has(tkovl(obj.tid, key))) this.stprds.add(tkovl(obj.tid, key));
        if (this.fhas(slot)) { const v = this.fget(slot); if (v instanceof Stor) { const c = v.const; return (c === null || typeof c === "boolean" || typeof c === "bigint" || typeof c === "number" || isby(c)) ? c : v.expr; } return v; }
      }
      const v = obj.get(key);
      if (v instanceof Stor) return v.const;
      if (obj.tid === null && v && v.k === "Reg" && snbase <= v.n && v.n < bbase && hhas(obj, tblid) && this.fget(["snap", v.n]) === hget(obj, tblid)) return v;
      if (obj.tid === null && issym(v)) { const h = this.homeof(obj); if (h !== null) { this.prog.usedtbl(obj); return Idx(Reg(h), this.asexpr(key)); } }
      if (obj.tid === null && v instanceof LTbl && v.tid === null && hhas(v, tblid)) this.tsrc.set(v, [obj, key]);
      return v;
    }
    if (obj && obj.k === "SymList") return this.symlstget(obj, key);
    if (issym(obj)) return Idx(obj, this.asexpr(key));
    if (obj === null || obj === undefined) throw new Unsup("index nil");
    throw new Unsup("index " + repr(obj));
  }

  symlstget(lst, key) {
    if (key instanceof SprIdx) {
      const s = Number(key.start); let m;
      if (s <= lst.items.length) m = Multi(lst.items.slice(s - 1).map((x) => this.asexpr(x)), lst.tail);
      else if (lst.tail !== null && lst.tail !== undefined) m = Multi([], sym.taildrop(lst.tail, s - lst.items.length - 1));
      else m = Multi([]);
      return new Spr(m);
    }
    const isn = (isby(key) && key.length === 1 && key[0] === 0x6e);
    if ((lst.nkey !== null && keyeq(key, lst.nkey)) || (lst.nkey === null && isn)) return this.cntof(lst);
    if (typeof key === "bigint" && key >= 1n) { const ki = Number(key); if (ki <= lst.items.length) return lst.items[ki - 1]; if (lst.tail !== null && lst.tail !== undefined) return sym.tailat(lst.tail, ki - lst.items.length); return null; }
    const ek = kstr(nmkey(key)); if (Object.prototype.hasOwnProperty.call(lst.extra, ek)) return lst.extra[ek];
    throw new Unsup("packed list index " + repr(key));
  }
  cntof(lst) { if (lst.tail === null || lst.tail === undefined) return BigInt(lst.items.length); return new Lin(BigInt(lst.items.length), lst.tail); }

  boolidx(t, key) {
    if (!this.isbool(key) || hhas(t, taint) || !hhas(t, tblid) || this.prog.boolamb.has(hget(t, tblid))) return nfold;
    for (const x of hkeys(t)) if (typeof x === "bigint" && (x === 0n || x === 1n)) return nfold;
    const vt = _unsto(hget(t, true)), vf = _unsto(hget(t, false));
    if (vt === true && vf === false) return this.asexpr(key);
    if (vt === false && vf === true) return Un("Not", this.asexpr(key));
    if ((vt === null || typeof vt === "boolean" || typeof vt === "bigint" || typeof vt === "number" || isby(vt)) && sclsame(vt, vf) && scleq(vt, vf)) return vt;
    if (vt instanceof LTbl && vt === vf) return vt;
    return nfold;
  }

  newindex(obj, key, v, it) {
    if (key && key.k === "Multi") key = sym.multifst(key);
    if (v && v.k === "Multi") v = sym.multifst(v);
    for (const x of [obj, key]) if (x instanceof _Lost) x.fail();
    if (this._lzrslv && this._lzci === null && obj instanceof LTbl && obj.tid !== null) {
      let k = key; if (issym(k)) k = this.fval(k);
      if (k !== nfold && !issym(k)) { const ci = this._mkrproto(hget(obj, nmkey(k))); if (ci !== null && ci !== undefined) this._lzci = ci; }
    }
    if (obj instanceof RegF) { this.regwr(key, v); return; }
    if (obj instanceof InsPrx) { const k = this.conckey(key); const t = k !== nfold ? obj.fields.get(kstr(nmkey(k))) : undefined; if (t === undefined) throw new Unsup("instruction proxy field " + repr(key)); return this.newindex(t, obj.pc, v, it); }
    if (obj instanceof BoxRef) { if (!(key === 1n || key === 1)) throw new Unsup("box store at " + repr(key)); this.emit(Asgn(obj.target, this.valof(v))); return; }
    if (obj instanceof EnvTbl) {
      if (issym(key) && this.fval(key) !== nfold) key = this.fval(key);
      if (isby(key) && _hashl(key)) return;
      const tgt = isby(key) ? Glob(key.toString("latin1")) : Idx(Glob("_ENV"), this.asexpr(key));
      this.emit(Asgn(tgt, this.valof(v))); return;
    }
    if (obj === vglob) return;
    if (obj instanceof LTbl) {
      if (typeof obj.tid === "number") {
        if (issym(key)) { key = this.fval(key); if (key === nfold) return; }
        const k = nmkey(key); const slot = ["ovl", obj.tid, k]; this.wrtnnow.add(tkovl(obj.tid, k));
        if (v instanceof _Lost) { this.fpop(slot); return; }
        if (v && v.k === "Reg") { const cl = this.fget(["clo", v.n]); if (cl && cl.k === "ClosureExpr") cl.runtime = true; }
        if (issym(v) && !(v instanceof Lin) && !(v instanceof SprIdx)) {
          const key2 = obj.tid + "|" + kstr(k); if (!this.ovlslt.has(key2)) this.ovlslt.set(key2, this.ovlslt.size + 1);
          const r = Reg(obase + this.ovlslt.get(key2)); this.emit(Asgn(r, this.valof(v)));
          const c = this.fval(v); this.fpop(r.n); if (c !== nfold) this.fset(r.n, c); else if (this.isbool(v)) this.fset(r.n, bool);
          v = c !== nfold ? new Stor(r, c) : r;
        }
        this.fset(slot, v); return;
      }
      if (key instanceof SprIdx && obj.tid === null && v instanceof Spr) {
        const r = this.escape(obj); if (r !== null) { this.emit(SetLst(r, key.start, Multi(v.m.items.map((x) => this.asexpr(x)), v.m.tail))); return; }
      }
      if (issym(key)) {
        const c = this.fval(key);
        if (c === nfold) { if (obj.tid === null) { const r = this.escape(obj); if (r !== null) { const val = v === obj ? r : this.valof(v); this.emit(Asgn(Idx(r, this.asexpr(key)), val)); return; } } throw new Unsup("symbolic key store into a concrete VM table"); }
        key = c;
      }
      const k = nmkey(key);
      if (this.basetabsids.has(obj)) {
        if (!this.tabwrtn.has(obj)) this.tabwrtn.set(obj, new Set());
        this.tabwrtn.get(obj).add(kstr(k)); this.wrtnnow.add(tktab(obj.tid, k));
        if (v instanceof LTbl && v.tid === null) v = this.tblexpr(v);
        if (v instanceof Spr) v = new Spr(Multi(Array.from(v.m.items), v.m.tail));
        if (issym(v) && !(v instanceof Lin) && !(v instanceof SprIdx)) {
          if (!this.stktabs.has(obj.tid)) this.stktabs.set(obj.tid, this.stktabs.size + 1);
          const n = this.stktabs.get(obj.tid); const r = Reg(sbase * n + Number(k));
          if (!(v.k === "Reg" && v.n === r.n)) this.emit(Asgn(r, this.valof(v)));
          v = r;
        }
        obj.set(k, v); return;
      }
      if (obj.tid === null) {
        let h = this.homeof(obj);
        if (h !== null && (_isphan(k) || _isphan(v) || v === vglob || (v instanceof LTbl && this.homeof(v) === null))) { hsetraw(obj, taint, true); h = null; }
        if (h !== null && hhas(obj, tblid) && issym(v) && !(v.k === "Const") && this.fval(v) === nfold && this.isbool(v)) {
          const skey = repr(this.curpc) + "|" + repr(k); if (!this.snap.has(skey)) this.snap.set(skey, this.snap.size + 1);
          const rs = Reg(snbase + this.snap.get(skey)); this.emit(Asgn(rs, this.valof(v)));
          this.fset(rs.n, bool); this.fset(["snap", rs.n], hget(obj, tblid)); v = rs;
        }
        if (h !== null) { const st = Asgn(Idx(Reg(h), this.irref(k, obj)), this.irref(v, obj)); this.emit(st); if (hhas(obj, tblid)) this.prog.tblstmtsadd(hget(obj, tblid), st); }
        if (issym(v)) { const c = this.fval(v); if (c !== nfold) v = new Stor(v, c); }
        if ((typeof k === "boolean" || typeof k === "bigint") && hhas(obj, tblid)) {
          for (const ek of hkeys(obj)) if ((typeof ek === "boolean" || typeof ek === "bigint") && typeof ek !== typeof k && boolinteq(ek, k)) { if (!_samefact(_unsto(hget(obj, ek)), _unsto(v))) this.prog.boolamb.add(hget(obj, tblid)); break; }
        }
        obj.set(k, v); return;
      }
      obj.set(k, v); return;
    }
    if (issym(obj)) {
      if (key instanceof SprIdx) { if (!(v instanceof Spr)) throw new Unsup("spread store of " + repr(v)); this.emit(SetLst(obj, key.start, Multi(v.m.items.map((x) => this.asexpr(x)), v.m.tail))); return; }
      this.emit(Asgn(Idx(obj, this.asexpr(key)), this.valof(v))); return;
    }
    if (obj && obj.k === "SymList") { obj.extra[kstr(nmkey(key))] = v; return; }
    throw new Unsup("newindex " + repr(obj));
  }

  callsym(fn, args, it) {
    if (fn && fn.k === "Multi") fn = sym.multifst(fn);
    if (fn instanceof FnRef) {
      if (this.prog.vms.has(fn.loc)) return this.mkcls(args);
      if (fn.node === null || fn.node === undefined) throw new Unsup("call of an unknown VM function " + fn.loc);
      return it.calllua(new LFn(fn.node, _fnrefenv(fn, this.cscope)), args);
    }
    if (fn instanceof LFn) return it.calllua(fn, args);
    if (fn instanceof BoxRef) fn = fn.target;
    if (fn instanceof VmCls || args.items.some((x) => _isphan(x) || x === vglob)) return Multi([]);
    if (fn instanceof UpLst || fn instanceof LTbl || fn instanceof RegF) throw new Unsup("call of a VM object " + repr(fn));
    const fe = this.asexpr(fn);
    const gnm = (fe.k === "Global") ? fe.name : (fe.k === "Reg" ? this.fget(["glob", fe.n]) : null);
    if (gnm === "pcall" && args.items.length === 1 && (args.tail === null || args.tail === undefined)) {
      let c = args.items[0]; if (c && c.k === "Reg") c = this.fget(["clo", c.n]);
      if (c && c.k === "ClosureExpr" && (this.prog.chkprts.has(c.proto) || (this.prog.mbchkprts.has(c.proto) && this._envchksite(c)))) {
        c.runtime = true; const t = this.newtmp(); this.chktmps.add(t); return Multi([], TmpTail(t));
      }
    }
    const t = this.newtmp(); const itms = []; let tail = args.tail;
    for (let i = 0; i < args.items.length; i++) {
      const x = args.items[i];
      if (x instanceof Spr) { if (i !== args.items.length - 1 || (tail !== null && tail !== undefined)) throw new Unsup("spread in the middle of an argument list"); for (const y of x.m.items) itms.push(this.asexpr(y)); tail = x.m.tail; this.cons.add(x.m); }
      else itms.push((x && x.k === "SymList") ? x : this.valof(x));
    }
    this.emit(CallStmt(t, fe, Multi(itms, tail))); return Multi([], TmpTail(t));
  }

  callbltn(fn, args, it) {
    const name = fn.name; const a = args;
    if (name === "table.create") { if (this.inprol) { const n = a.items.length ? a.items[0] : null; this.nregs = (typeof n === "bigint") ? Number(n) : null; this.regfill = a.items.length > 1 || (a.tail !== null && a.tail !== undefined); return new RegF(); } return new LTbl(); }
    if (name === "coroutine.wrap") { const f = a.items.length ? a.items[0] : null; if (f instanceof LFn && _isgifn(f.node)) { const vals = it.evallst(f.node.body.body[0].values, new Scp(f.env), 3); return new GiRef(vals); } throw new Unsup("coroutine.wrap of a VM function"); }
    if (name === "select") {
      const n = a.items.length ? a.items[0] : null; const rest = Multi(a.items.slice(1), a.tail);
      if (isby(n) && n.length === 1 && n[0] === 0x23) { if (rest.tail === null || rest.tail === undefined) return BigInt(rest.items.length); return new Lin(BigInt(rest.items.length), rest.tail); }
      if (n instanceof SprIdx) { const k = Number(n.start) - 1; if (k <= rest.items.length) return new Spr(Multi(rest.items.slice(k), rest.tail)); return new Spr(Multi([], rest.tail ? sym.taildrop(rest.tail, k - rest.items.length) : null)); }
      if (typeof n === "bigint") { const k = Number(n) - 1; if (k <= rest.items.length) return Multi(rest.items.slice(k), rest.tail); return Multi([], rest.tail ? sym.taildrop(rest.tail, k - rest.items.length) : null); }
      throw new Unsup("select with " + repr(n));
    }
    if (name === "unpack" || name === "table.unpack") return this.unpack(a);
    if (name === "math.min" && a.items.length === 2 && a.items.some((x) => x instanceof Lin)) { const oth = a.items.filter((x) => !(x instanceof Lin)); if (oth.length && typeof oth[0] === "bigint") return oth[0]; }
    if (name === "setmetatable") return Multi(a.items.slice(0, 1));
    if (name === "rawequal") { const x = a.items.length > 0 ? a.items[0] : null, y = a.items.length > 1 ? a.items[1] : null; if (issym(x) || issym(y) || (x && (x.k === "SymList" || x.k === "Multi")) || (y && (y.k === "SymList" || y.k === "Multi"))) return true; if (x instanceof LTbl || y instanceof LTbl) return x === y; return leq(x, y); }
    if (name === "rawget") { const t = a.items.length > 0 ? a.items[0] : null, k = a.items.length > 1 ? a.items[1] : null; if (t instanceof LTbl && !(issym(k) || (k && (k.k === "SymList" || k.k === "Multi")))) return hget(t, nmkey(k)); throw new Unsup("rawget of " + repr(t)); }
    if (name === "rawset") { const t = a.items.length > 0 ? a.items[0] : null, k = a.items.length > 1 ? a.items[1] : null, v = a.items.length > 2 ? a.items[2] : null; if (t instanceof LTbl && !(issym(k) || (k && (k.k === "SymList" || k.k === "Multi")))) { hsetraw(t, nmkey(k), v); return t; } throw new Unsup("rawset of " + repr(t)); }
    if (sym.conc[name] !== undefined) {
      const vals = a.items;
      if ((a.tail !== null && a.tail !== undefined) || vals.some((x) => issym(x) || (x && (x.k === "SymList" || x.k === "Multi")))) {
        if (name.startsWith("bit32.")) return this._embltncall(name, a);
        throw new Unsup("builtin " + name + " on symbolic values");
      }
      try { return sym.conc[name].apply(null, vals); } catch (ex) { if (ex instanceof Unsup) throw ex; throw new Unsup(name + " failed: " + (ex && ex.message)); }
    }
    throw new Unsup("builtin " + name);
  }

  _embltncall(name, a) {
    const dot = name.indexOf("."); const lib = name.slice(0, dot), op = name.slice(dot + 1);
    const fe = Idx(Glob(lib), Const(Buffer.from(op, "latin1")));
    const itms = []; let tail = a.tail;
    for (let i = 0; i < a.items.length; i++) { const x = a.items[i]; if (x instanceof Spr) { if (i !== a.items.length - 1 || (tail !== null && tail !== undefined)) throw new Unsup("spread in the middle of a " + name + " argument list"); for (const y of x.m.items) itms.push(this.asexpr(y)); tail = x.m.tail; this.cons.add(x.m); } else itms.push((x && x.k === "SymList") ? x : this.valof(x)); }
    const t = this.newtmp(); this.emit(CallStmt(t, fe, Multi(itms, tail))); return Multi([], TmpTail(t));
  }

  unpack(a) {
    const t = a.items.length ? a.items[0] : null; const i = a.items.length > 1 ? a.items[1] : 1n; let j = a.items.length > 2 ? a.items[2] : null;
    if (t instanceof RegF) {
      if (j instanceof Lin) { if (this.top === null) throw new Unsup("unpack registers to a missing top"); const [base, m] = this.top; if (!this.wrtnnow.has(tktop)) this.stprds.add(tktop); const vals = []; for (let n = i; n < base; n++) vals.push(this.regrd(n)); this.cons.add(m); return Multi(vals.map((v) => this.asexpr(v)).concat(m.items), m.tail); }
      if (!(typeof i === "bigint") || !(typeof j === "bigint")) throw new Unsup("unpack registers with symbolic range");
      const vals = []; for (let n = i; n <= j; n++) vals.push(this.regrd(n)); return this._sprmulti(vals);
    }
    if (t && t.k === "SymList") { if (i !== 1n && i !== 1) throw new Unsup("unpack packed list from " + repr(i)); return Multi(t.items, t.tail); }
    if (t instanceof LTbl) {
      const lst = this.results.get(t); if (lst !== undefined) return Multi(lst.items, lst.tail);
      if (j === null) j = t.length();
      if (j instanceof Lin && typeof i === "bigint") {
        if (this.basetabsids.has(t)) { const tw = this.tabwrtn.get(t) || new Set(); for (let n = i; n < i + 64n; n++) if (!tw.has(kstr(nmkey(n)))) this.stprds.add(tktab(t.tid, n)); }
        const vals = []; let n = i;
        while (true) { const x = _unsto(t.get(n)); vals.push(x); if (x instanceof Spr || n > j.c + 1n) break; n += 1n; }
        if (!(vals[vals.length - 1] instanceof Spr)) throw new Unsup("unpack up to a count with a tail, without the tail");
        return this._sprmulti(vals);
      }
      if (!(typeof i === "bigint") || !(typeof j === "bigint")) throw new Unsup("unpack of a VM table with symbolic range");
      if (this.basetabsids.has(t)) { const tw = this.tabwrtn.get(t) || new Set(); for (let n = i; n <= j; n++) { if (!tw.has(kstr(nmkey(n)))) this.stprds.add(tktab(t.tid, n)); if (!tw.has(kstr(nmkey(n))) && !this.tabcrr.has(t.tid)) { this.tabcrr.add(t.tid); this.newcrr = true; } } }
      const out = []; for (let n = i; n <= j; n++) out.push(_unsto(t.get(n))); return this._sprmulti(out);
    }
    throw new Unsup("unpack " + repr(t));
  }
  _sprmulti(vals) {
    if (vals.length && vals[vals.length - 1] instanceof Spr) { const sp = vals[vals.length - 1]; this.cons.add(sp.m); return Multi(vals.slice(0, -1).concat(sp.m.items), sp.m.tail); }
    return Multi(vals);
  }
  callluahk(fn, args) {
    const t = args.items.length ? args.items[0] : null; const m = Multi(args.items.slice(1), args.tail);
    if (!(t instanceof LTbl)) throw new Unsup("results helper on " + repr(t));
    const lst = SymLst(m.items, m.tail); this.results.set(t, lst);
    hclr(t);
    for (let i = 0; i < m.items.length; i++) t.set(BigInt(i + 1), m.items[i]);
    if (m.tail !== null && m.tail !== undefined) hsetraw(t, BigInt(m.items.length + 1), new Spr(Multi([], m.tail)));
    if (this.basetabsids.has(t)) { if (!this.tabwrtn.has(t)) this.tabwrtn.set(t, new Set()); for (let j = 1; j <= m.items.length + 1; j++) this.tabwrtn.get(t).add(kstr(nmkey(BigInt(j)))); for (let j = 1; j <= m.items.length + 1; j++) this.wrtnnow.add(tktab(t.tid, BigInt(j))); }
    const n = this.cntof(lst);
    const top = this.vm.restop.get(fn.node);
    if (top !== undefined && this.iscope !== null) { const sc = this.iscope.lookup(top); if (sc !== null) { if (sc === this.iscope) this.notewr(top); sc.vars.set(top, n); } }
    return n;
  }

  _envchksite(c) {
    if (this.capidx !== mainproto(this.prog)) return false;
    const kinds = c.kinds || {};
    for (let i = 1; i <= c.upvals.length; i++) if (!Array.isArray(kinds[i])) return false;
    return true;
  }
  _sitecap(fn) {
    if (fn instanceof FnRef && fn.up) {
      const loc = this.prog.iats.get(fn.loc);
      const p = loc !== undefined && loc !== null ? fn.up.get(loc) : undefined;
      if (p instanceof LTbl) { const ci = this.dump.capof.get(p); return ci === undefined ? null : ci; }
    }
    return null;
  }
  _capfrmcch(zc) {
    if (!(zc instanceof FnRef) || !zc.up) return null;
    const fnd = new Set();
    for (const cij of zc.up.values()) {
      if (!(cij instanceof FnRef) || !cij.up) continue;
      const ints = [...cij.up.values()].filter((v) => typeof v === "bigint");
      const tabs = [...cij.up.values()].filter((v) => v instanceof LTbl);
      for (const t of tabs) { const slot = hget(t, 2n); if (!(slot instanceof LTbl)) continue; for (const gy of ints) { const ci = this._mkrproto(hget(slot, gy)); if (ci !== null && ci !== undefined) fnd.add(ci); } }
    }
    return fnd.size === 1 ? [...fnd][0] : null;
  }
  _mkrproto(f) {
    let vals = null;
    if (f instanceof FnRef && f.up) vals = [...f.up.values()];
    else if (f instanceof LFn) vals = ProtoLftr._envvals(f.env);
    if (vals === null) return null;
    const fnd = new Set();
    for (const v of vals) if (v instanceof LTbl && this.dump.capof.has(v)) fnd.add(this.dump.capof.get(v));
    return fnd.size === 1 ? [...fnd][0] : null;
  }
  static _envvals(env, lim) {
    lim = lim || 12; const out = []; let seen = 0;
    while (env !== null && env !== undefined && seen < lim) { for (const v of env.vars.values()) out.push(v); env = env.parent; seen += 1; }
    return out;
  }
  _capfrmwrp(w) {
    const m = this._lzmkrfn(w); if (m === null) return null;
    const fnd = new Set();
    for (const dec of ProtoLftr._envvals(m.env)) {
      if (!(dec instanceof LFn)) continue;
      const vals = ProtoLftr._envvals(dec.env);
      const ints = vals.filter((v) => typeof v === "bigint"); const tabs = vals.filter((v) => v instanceof LTbl);
      for (const t of tabs) { const slot = hget(t, 2n); if (!(slot instanceof LTbl)) continue; for (const gy of ints) { const ci = this._mkrproto(hget(slot, gy)); if (ci !== null && ci !== undefined) fnd.add(ci); } }
    }
    return fnd.size === 1 ? [...fnd][0] : null;
  }
  _upsfrmwrp(w) {
    const m = this._lzmkrfn(w); if (m === null) return null;
    let call = null;
    for (const st of m.node.body.body) {
      if (st.type === "AstStatLocal" && st.values && st.values.length && st.values[0].type === "AstExprCall" &&
        (st.values[0].func.type === "AstExprIndexExpr" || st.values[0].func.type === "AstExprIndexName")) { call = st.values[0]; break; }
    }
    if (call === null) return null;
    const h = new LTbl();
    for (let i = 1; i < call.args.length; i++) {
      const arg = call.args[i]; if (arg.type !== "AstExprLocal") return null;
      const loc = arg.local.location; const s = m.env.lookup(loc); if (s === null) return null;
      hsetraw(h, BigInt(i), s.vars.get(loc));
    }
    return h;
  }
  _smpgtr(w) {
    const node = w.node;
    if (!node || typeof node !== "object" || node.type !== "AstExprFunction") return null;
    const body = (node.body && node.body.body) || [];
    if (body.length !== 1 || body[0].type !== "AstStatReturn") return null;
    const lst = body[0].list || []; if (!lst.length) return null;
    const h = new LTbl();
    for (let i = 0; i < lst.length; i++) { const e = lst[i]; if (e.type !== "AstExprLocal") return null; const loc = e.local.location; const s = w.env.lookup(loc); if (s === null) return null; hsetraw(h, BigInt(i + 1), s.vars.get(loc)); }
    const [ent, kinds] = this._clsent(h);
    const c = ClsExpr(new GtrProto(lst.length), ent); c.kinds = kinds; this.kids.push(c); return c;
  }
  mkcls(args) {
    const vals = args.items; const proto = vals.length ? vals[0] : null; const ups = vals.length > 1 ? vals[1] : null;
    if (!(proto instanceof LTbl)) throw new Unsup("closure of a non-proto " + repr(proto));
    let ci = this.dump.capof.get(proto);
    if (ci === undefined && this._lzrslv) ci = this._lzci;
    if (ci === undefined || ci === null) throw new Unsup("closure of a proto that was never captured (table " + proto.tid + ")");
    return this._bldcls(ci, ups);
  }
  _clsent(ups) {
    const ent = []; const kinds = {};
    if (ups instanceof LTbl) {
      let n = 0n; for (const k of hkeys(ups)) if (typeof k === "bigint" && k > n) n = k;
      for (let i = 1n; i <= n; i++) {
        let e = hget(ups, i); if (e instanceof Stor) e = e.expr;
        if (e instanceof BoxRef) { kinds[Number(i)] = "box"; const t = e.target; if (t && t.k === "Reg") { ent.push(new MbBox(t.n)); this.capdregs.add(t.n); } else ent.push(t); }
        else { const x = (e !== null && e !== undefined) ? this.asexpr(e) : Const(null); const c = this.fval(x); if (c === null || ((typeof c === "boolean" || typeof c === "bigint" || typeof c === "number" || isby(c)) && c !== trt)) kinds[Number(i)] = ["const", c]; ent.push(x); }
      }
    }
    return [ent, kinds];
  }
  _bldcls(ci, ups) { const [ent, kinds] = this._clsent(ups); const c = ClsExpr(ci, ent); c.kinds = kinds; this.kids.push(c); return c; }
  _stubcls() { const whr = "function " + this.capidx + " at 0:" + this.curpc; const c = ClsExpr(new StubProto(whr), []); c.kinds = {}; this.kids.push(c); return c; }
  _lzmkrfn(w) {
    if (!(w instanceof LFn)) return null;
    const node = w.node;
    if (node.type !== "AstExprFunction" || (node.args && node.args.length) || !node.vararg) return null;
    const body = node.body.body;
    if (body.length !== 1 || body[0].type !== "AstStatReturn" || body[0].list.length !== 1) return null;
    const call = body[0].list[0];
    if (call.type !== "AstExprCall" || call.args.length !== 1) return null;
    if (call.func.type !== "AstExprLocal" || call.args[0].type !== "AstExprVarargs") return null;
    const s = w.env.lookup(call.func.local.location);
    const m = s !== null ? s.vars.get(call.func.local.location) : null;
    return m instanceof LFn ? m : null;
  }
  instd(loc, res) {
    if (this._lzrslv) return res;
    const v = (res && res.k === "Multi") ? sym.multifst(res) : res;
    if ((v && v.k === "ClosureExpr") || this._lzmkrfn(v) !== null) return res;
    const it = this.curit;
    if (it === null || _capfork(it)) throw new Unsup("closure site never instantiated in the recorded run (instantiator " + loc + ")");
    return Multi([this._stubcls()]);
  }
  rslvlzcls(res, fn, args) {
    if (this._lzrslv) return res;
    const v = (res && res.k === "Multi") ? sym.multifst(res) : res;
    if (this._lzmkrfn(v) === null) return res;
    const ups = args.items.length ? args.items[0] : null;
    let ci = this._sitecap(fn);
    if (ci === null) ci = this._capfrmcch(fn);
    if (ci === null || ci === undefined) return res;
    return Multi([this._bldcls(ci, ups)]);
  }
}
function cmpstr(a, b) { const x = String(a), y = String(b); return x < y ? -1 : x > y ? 1 : 0; }

class StubProto { constructor(whr) { this.where = whr; } }

class _DeadFork extends Error {}
const blibs = new Set(["bit32", "bit"]);
function _bitmbr(e, fcts, dep) {
  dep = dep || 0;
  if (dep > 8 || e === null || e === undefined) return false;
  if (e.k === "Un") return _bitmbr(e.a, fcts, dep + 1);
  if (e.k === "Bin") return _bitmbr(e.a, fcts, dep + 1) || _bitmbr(e.b, fcts, dep + 1);
  if (e.k === "Index") {
    const o = e.obj;
    if (o && o.k === "Global" && blibs.has(o.name)) return true;
    if (o && o.k === "Reg") { const g = fctsglob(fcts, o.n); if (blibs.has(g)) return true; }
    if (o && o.k === "Bin" && o.op === "Or" && [o.a, o.b].some((x) => x && x.k === "Global" && blibs.has(x.name))) return true;
    return false;
  }
  if (e.k === "Reg") { const f = fctsreg(fcts, e.n); return f !== undefined && issym(f) && f.k !== "Reg" && _bitmbr(f, fcts, dep + 1); }
  return false;
}

function fctsreg(fcts, n) { const r = fcts.get("R" + n); return r === undefined ? undefined : r.v; }
function fctsglob(fcts, n) { const r = fcts.get("glob|" + n); return r === undefined ? undefined : r.v; }
function _capfork(it) {
  const fcts = it.lft.facts;
  return it.dlog.some((d) => _bitmbr(d[2], fcts));
}
function _nextst(node, out) {
  if (node === null || node === undefined) return;
  if (node.cond !== null && node.cond !== undefined) { _nextst(node.then, out); _nextst(node.els, out); }
  else if (node.outcome && node.outcome.o === "Next") out.push(node.outcome.state);
}

class LiftItp extends sym.Itp {
  constructor(lftr) { super(lftr); this.lpsub = null; }

  getvar(scp, lcl) {
    const key = lcl.location; const s = scp.lookup(key);
    if (s === null) { if (this.lft._lzrslv) return this.lft._lzsnk.get(key); throw new Unsup("unbound local " + lcl.name + "@" + key); }
    if (s === this.lft.iscope) this.lft.noterd(key);
    return s.vars.get(key);
  }
  setvar(scp, lcl, v) {
    const key = lcl.location; const s = scp.lookup(key);
    if (s === null) { if (this.lft._lzrslv) { this.lft._lzsnk.set(key, v); return; } throw new Unsup("assign to unbound local " + lcl.name); }
    if (this.lft.lvact.has(key) && s !== this.lft.iscope) { const r = Reg(lvbase + this.lft.lvact.get(key)); this.lft.emit(Asgn(r, this.lft.valof(v))); s.vars.set(key, r); return; }
    if (s === this.lft.iscope) { this.lft.notewr(key); v = this.lft.lclval(key, v); }
    else if (s !== this.lft.cscope) v = this.lft.hold(key, v, s);
    s.vars.set(key, v);
  }
  tblctor(node, scp) {
    const itms = node.items;
    if (itms.length === 1 && itms[0].kind === "item" && itms[0].value.type === "AstExprIndexExpr") {
      const ix = itms[0].value;
      if (this.eval(ix.expr, scp) instanceof RegF) { const tb = new BoxTbl(); const v = this.eval(ix, scp); hsetraw(tb, 1n, (v && v.k === "Multi") ? sym.multifst(v) : v); return tb; }
    }
    return super.tblctor(node, scp);
  }
  binop(op, a, b) { for (const x of [a, b]) if (x instanceof _Lost) x.fail(); return super.binop(op, a, b); }
  eval(node, scp) {
    if (node.type === "AstExprBinary" && node.op === "And") {
      const e = _trutest(node);
      if (e !== null) {
        let v = this.eval(e, scp); if (v && v.k === "Multi") v = sym.multifst(v);
        if (issym(v) && !(v instanceof Lin) && !(v instanceof SprIdx)) return Un("Not", Un("Not", v));
        if (v instanceof _Lost) v.fail();
        return v !== null && v !== undefined && v !== false;
      }
    }
    return super.eval(node, scp);
  }
  unop(op, a) {
    if (a instanceof _Lost) a.fail();
    if (op === "Len" && a instanceof LTbl && a.tid === null && !(a instanceof BoxTbl) && !this.lft.results.has(a)) {
      const h = this.lft.homeof(a); if (h !== null) { this.lft.prog.usedtbl(a); return Un("Len", Reg(h)); }
    }
    return super.unop(op, a);
  }
  execstmt(st, scp) {
    const t = st.type;
    if ((t === "AstStatWhile" || t === "AstStatForIn" || t === "AstStatFor") && !this.lft.inprol) {
      if (this.lpsub !== null && this.lpsub === st.location) return this.lphd(st, scp);
      if (this.lpsub !== null && _hldsloop(st, this.lpsub)) return this.lprsm(st, scp);
      const kind = this.fuslp(st, scp);
      if (kind !== null) return this.lpent(st, scp, kind);
    }
    if (t === "AstStatLocal" && !this.lft.inprol) {
      this.steps += 1;
      const vals = this.evallst(st.values, scp, st.vars.length);
      for (let i = 0; i < st.vars.length; i++) scp.vars.set(st.vars[i].location, this.lft.hold(st.vars[i].location, vals[i], scp));
      return;
    }
    if (t !== "AstStatFor") return super.execstmt(st, scp);
    this.steps += 1;
    let a = this.eval(st.from, scp), b = this.eval(st.to, scp), c = st.step ? this.eval(st.step, scp) : 1n;
    if (b instanceof Lin || a instanceof Lin) return this.linfor(st, scp, a, b, c);
    if (issym(a) || issym(b) || issym(c)) throw new Unsup("numeric for with symbolic bounds");
    let i = a; let n = 0;
    const cpos = sym.numcmp(c, 0n) > 0;
    while ((cpos && sym.numcmp(i, b) <= 0) || (!cpos && sym.numcmp(i, b) >= 0)) {
      n += 1; if (n > 1000000) throw new Unsup("for loop limit");
      const inr = new Scp(scp); inr.vars.set(st.var.location, i);
      try { this.execblk(st.body.body, inr); } catch (ex) { if (ex instanceof BrkSig) break; else if (ex instanceof ContSig) {} else throw ex; }
      i = fixint((typeof i === "bigint" && typeof c === "bigint") ? (i + c) : (Number(i) + Number(c)));
    }
  }

  fuslp(st, scp) {
    const scrval = (x) => issym(x) && !(x instanceof Lin) && !(x instanceof SprIdx) && !(x && x.k === "Const");
    const t = st.type;
    if (t === "AstStatWhile") return scrval(this.eval(st.condition, scp)) ? "while" : null;
    if (t === "AstStatFor") {
      const vals = [this.eval(st.from, scp), this.eval(st.to, scp)]; if (st.step) vals.push(this.eval(st.step, scp));
      if (vals.some((x) => x instanceof Lin || x instanceof SprIdx)) return null;
      return vals.some(scrval) ? "for" : null;
    }
    const vals = this.evallst(st.values, scp, 3);
    return scrval(vals[0]) ? "forin" : null;
  }
  _lplcls(scp) {
    const out = []; let s = scp;
    while (s !== null && s !== this.lft.iscope && s !== this.lft.cscope) {
      for (const [k, v] of s.vars) if (k !== "..." && issym(v) && !(v instanceof Lin) && !(v instanceof SprIdx) && !(v && v.k === "Const") && !(v && v.k === "ClosureExpr")) out.push([s, k, v]);
      s = s.parent;
    }
    return out;
  }
  _lv(key) { if (!this.lft.lvreg.has(key)) this.lft.lvreg.set(key, this.lft.lvreg.size + 1); return this.lft.lvreg.get(key); }
  lpent(st, scp, kind) {
    const lft = this.lft;
    for (const [, k, v] of this._lplcls(scp)) lft.emit(Asgn(Reg(lvbase + this._lv(k)), lft.valof(v)));
    const loc = st.location;
    if (kind === "forin") { const vals = this.evallst(st.values, scp, 3); lft.emit(Asgn(Psd("ga", lvbase + this._lv("forin|" + loc)), GenIter(Multi([null].concat(vals.map((x) => lft.valof(x))))))); }
    else if (kind === "for") { const step = st.step ? this.eval(st.step, scp) : 1n; for (const [part, x] of [["i", this.eval(st.from, scp)], ["lim", this.eval(st.to, scp)], ["step", step]]) lft.emit(Asgn(Reg(lvbase + this._lv("for|" + loc + "|" + part)), lft.valof(x))); }
    throw new LoopSig(loc);
  }
  lphd(st, scp) {
    const lft = this.lft;
    if (this.dlog.length) throw new Unsup("a decision on script values before a fused loop");
    lft.out.length = 0;
    for (const [s, k] of this._lplcls(scp)) { const n = this._lv(k); s.vars.set(k, Reg(lvbase + n)); lft.lvact.set(k, n); }
    const loc = st.location; const t = st.type; const inr = new Scp(scp);
    if (t === "AstStatForIn") { const tmp = lft.newtmp(); lft.emit(CallStmt(tmp, Psd("ga", lvbase + this._lv("forin|" + loc)), Multi([]))); if (!this.condtru(TmpVal(tmp, 1))) return; for (let i = 0; i < st.vars.length; i++) inr.vars.set(st.vars[i].location, TmpVal(tmp, i + 2)); }
    else if (t === "AstStatFor") { const i = Reg(lvbase + this._lv("for|" + loc + "|i")), lim = Reg(lvbase + this._lv("for|" + loc + "|lim")), step = Reg(lvbase + this._lv("for|" + loc + "|step")); const sv = lft.fval(step); if (!(typeof sv === "bigint" || (typeof sv === "number")) || typeof sv === "boolean" || sv === 0n || sv === 0) throw new Unsup("fused numeric loop with an unknown step"); const pos = (typeof sv === "bigint" ? sv > 0n : sv > 0); if (!this.condtru(Bin(pos ? "CompareLe" : "CompareGe", i, lim))) return; inr.vars.set(st.var.location, i); this._fusfori = i; this._fusforstp = step; }
    else { if (!this.condtru(this.eval(st.condition, scp))) return; }
    try { this.execblk(st.body.body, inr); } catch (ex) { if (ex instanceof BrkSig) return; else if (ex instanceof ContSig) {} else throw ex; }
    if (t === "AstStatFor") lft.emit(Asgn(this._fusfori, Bin("Add", this._fusfori, this._fusforstp)));
    throw new LoopSig(loc);
  }
  lprsm(st, scp) {
    const lft = this.lft;
    for (const [s, k] of this._lplcls(scp)) { const n = this._lv(k); s.vars.set(k, Reg(lvbase + n)); lft.lvact.set(k, n); }
    const loc = st.location; const t = st.type; const inr = new Scp(scp);
    if (t === "AstStatForIn") { for (const v of st.vars) inr.vars.set(v.location, Reg(lvbase + this._lv(v.location))); }
    else if (t === "AstStatFor") { const i = Reg(lvbase + this._lv("for|" + loc + "|i")); inr.vars.set(st.var.location, i); this._fusfori = i; }
    try { this.execblk(st.body.body, inr); } catch (ex) { if (ex instanceof BrkSig) return; else if (ex instanceof ContSig) {} else throw ex; }
    if (t === "AstStatFor") { const i = Reg(lvbase + this._lv("for|" + loc + "|i")); lft.emit(Asgn(i, Bin("Add", i, Reg(lvbase + this._lv("for|" + loc + "|step"))))); }
    throw new LoopSig(loc);
  }
  linfor(st, scp, a, b, c) {
    if (c !== 1n && c !== 1 || !(typeof a === "bigint") || !(b instanceof Lin)) throw new Unsup("loop over a multiple result");
    let i = a;
    while (true) {
      const inr = new Scp(scp);
      if (i <= b.c) inr.vars.set(st.var.location, i); else inr.vars.set(st.var.location, new SprIdx(i));
      try { this.execblk(st.body.body, inr); } catch (ex) { if (ex instanceof BrkSig) return; else if (ex instanceof ContSig) {} else throw ex; }
      if (i > b.c) return;
      i += 1n;
    }
  }

  condtru(v) {
    if (v instanceof _Lost) v.fail();
    if (v instanceof KGlob || (v && v.k === "Global" && !(v instanceof KGlob) && sglobs.has(v.name))) return true;
    if (v instanceof Lin || v instanceof SprIdx) return true;
    while (v && v.k === "Un" && v.op === "Not" && v.a && v.a.k === "Un" && v.a.op === "Not") v = v.a.a;
    if (issym(v) && !(v instanceof Lin) && !(v instanceof SprIdx)) { const c = this.lft.fval(v); if (c !== nfold) return tru(c); }
    return super.condtru(v);
  }
  call(fn, args) {
    if (!(args && args.k === "Multi")) args = Multi(Array.from(args));
    if (fn instanceof LFn && this.lft.vm.resfns.has(fn.node)) return this.lft.callluahk(fn, args);
    if (fn instanceof FnRef && fn.node !== null && fn.node !== undefined && !this.lft.prog.vms.has(fn.loc)) {
      if (!this.lft._lzrslv && this.lft.prog.iats.has(fn.loc)) {
        const ups = args.items.length ? args.items[0] : null;
        if (ups instanceof LTbl) { const ci = this.lft._sitecap(fn); if (ci !== null && ci !== undefined) return Multi([this.lft._bldcls(ci, ups)]); }
      }
      let res = this.calllua(new LFn(fn.node, _fnrefenv(fn, this.lft.cscope)), args);
      res = this.lft.rslvlzcls(res, fn, args);
      if (this.lft.prog.iats.has(fn.loc)) return this.lft.instd(fn.loc, res);
      return res;
    }
    if (fn instanceof LFn && fn.node.location !== undefined && this.lft.prog.iats.has(fn.node.location)) {
      return this.lft.instd(fn.node.location, super.call(fn, args));
    }
    return super.call(fn, args);
  }
}

function _fnrefenv(fn, base) {
  if (!fn.up) return base;
  const extr = new Map();
  for (const [k, v] of fn.up) if (base.lookup(k) === null) extr.set(k, v);
  if (!extr.size) return base;
  const env = new Scp(base); for (const [k, v] of extr) env.vars.set(k, v); return env;
}

class LoopSig extends Error { constructor(sub) { super("loop"); this.sub = sub; } }

module.exports = {
  ProtoLftr, LiftItp, LoopSig, StubProto,
  _capfork, _DeadFork, _nextst, _isresfn, _restop,
};

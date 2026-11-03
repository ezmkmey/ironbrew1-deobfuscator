"use strict";
const sym = require("./sym.js");
const ir = require("./ir.js");
const dvl = require("./dval.js");
const exe = require("./exec.js");
const { Dump } = require("./dump.js");
const { serord } = require("./graphout.js");

const { Scp, Multi, BrkSig, ContSig, RetSig, Unsup, LTbl, Bltn } = sym;
const { Node, Next, Ret } = ir;
const {
  _samefact, _isphan, vglob, Stor, UpLst, GtrProto, MbBox, Spr,
  hget, hhas, hsetraw, tblid, cmod, mst, mrst, pslk, repr, Fcts,
} = dvl;
const { ProtoLftr, LiftItp, StubProto, NatProto, _nextst, _capfork, _DeadFork, LoopSig,
  _isresfn, _restop } = exe;

const dsnt = { _dead: true };

function* iternds(n) {
  const st = [n];
  while (st.length) {
    const x = st.pop();
    if (Array.isArray(x)) { for (let i = x.length - 1; i >= 0; i--) st.push(x[i]); }
    else if (x && typeof x === "object") {
      yield x;
      const ks = Object.keys(x);
      for (let i = ks.length - 1; i >= 0; i--) { const k = ks[i]; if (k !== "local" && k !== "location") { const v = x[k]; if (v && typeof v === "object") st.push(v); } }
    }
  }
}
function disploop(fn) {
  for (const s of fn.body.body) {
    if (s.type !== "AstStatWhile") continue;
    const c = s.condition;
    if (!(c.type === "AstExprConstantBool" && c.value)) continue;
    const body = s.body.body;
    if (body.length && body[0].type === "AstStatAssign" && body[0].values[0].type === "AstExprIndexExpr") return s;
  }
  return null;
}
function findvms(root) {
  const out = [];
  for (const x of iternds(root)) {
    if (x.type !== "AstExprFunction") continue;
    const body = x.body.body;
    if (!body.length || body[body.length - 1].type !== "AstStatReturn" || !body[body.length - 1].list.length) continue;
    const inr = body[body.length - 1].list[0];
    if (inr.type === "AstExprFunction" && inr.vararg && disploop(inr) !== null) out.push([x, inr]);
  }
  return out;
}
function lclref(x) {
  if (x && typeof x === "object" && x.type === "AstExprLocal") return [x.local.name, x.local.location];
  return null;
}
function prmown(root) {
  const out = new Map();
  for (const n of iternds(root)) if (n.type === "AstExprFunction") (n.args || []).forEach((a, i) => out.set(a.location, [n, i]));
  return out;
}
function iatcalls(root) {
  const out = []; const own = prmown(root); const seen = new Set();
  for (const n of iternds(root)) {
    if (n.type !== "AstExprCall") continue;
    const crgs = n.args || [];
    if (crgs.length < 2) continue;
    const fwd = crgs.slice(1).map(lclref);
    if (fwd.some((f) => f === null)) continue;
    const first = own.get(fwd[0][1]);
    if (first === undefined || first[1] !== 0) continue;
    const fn = first[0];
    let ok = true;
    for (let i = 0; i < fwd.length; i++) { const o = own.get(fwd[i][1]); if (o === undefined || o[0] !== fn || o[1] !== i) { ok = false; break; } }
    if (!ok || !(fn.args && fn.args.length)) continue;
    const key = fn.body.location;
    if (seen.has(key)) continue;
    seen.add(key);
    out.push([fn, n]);
  }
  return out;
}
function astfns(root) {
  const out = {};
  for (const n of iternds(root)) if (n.type === "AstExprFunction") out[n.location] = n;
  return out;
}

class VmMdl {
  constructor(mkr, itp) {
    this.loop = disploop(itp);
    const body = itp.body.body;
    const i = body.indexOf(this.loop);
    this.prol = body.slice(0, i);
    this.after = body.slice(i + 1);
    this.lpbody = this.loop.body.body;
    const first = this.lpbody[0].values[0];
    if (first.index.type !== "AstExprLocal") throw new Unsup("dispatch loop does not index by a local pc");
    this.pcdecl = first.index.local.location;
    this.params = mkr.args.map((a) => a.location);
    this.ilocals = [];
    for (const s of this.prol) {
      if (s.type === "AstStatLocal") for (const v of s.vars) this.ilocals.push(v.location);
      else if (s.type === "AstStatLocalFunction") this.ilocals.push(s.name.location);
    }
    this.ilocidx = new Map(); this.ilocals.forEach((k, idx) => this.ilocidx.set(k, idx));
    this.resfns = new Set();
    this.restop = new Map();
    for (const s of this.prol) {
      if (s.type === "AstStatLocalFunction" && _isresfn(s.func)) {
        this.resfns.add(s.func);
        const top = _restop(s.func);
        if (top !== null) this.restop.set(s.func, top);
      }
    }
  }
}

function alstbls(prog, x, y) {
  if (!(x instanceof LTbl && y instanceof LTbl) || x.tid !== null || y.tid !== null) return;
  const i = hget(x, tblid), j = hget(y, tblid);
  if (i !== null && j !== null && i !== j) { prog.tbldepsadd(i, j); prog.tbldepsadd(j, i); }
}
function meetfacts(a, b, la, lb, nregs, prog) {
  const out = a.child();
  for (let i = 0; i < b.gone.length; i++) { const x = b.gone[i] & ~a.gone[i]; if (x) for (let j = 0; j < 8; j++) if ((x >> j) & 1) out.mkgone(i * 8 + j); }
  const lost = new Set();
  for (const e of la) lost.add(e);
  for (const e of lb) lost.add(e);
  const keys = new Set([...a.keys(), ...b.keys()]);
  for (const fk of keys) {
    const ea = a.get(fk), eb = b.get(fk);
    const ina = ea !== undefined, inb = eb !== undefined;
    const slot = ina ? ea.slot : eb.slot;
    if (ina && inb && _samefact(ea.v, eb.v)) { out.set(fk, ea); if (prog) alstbls(prog, ea.v, eb.v); continue; }
    if (ina && inb) {
      const va = ea.v instanceof Stor ? ea.v.expr : ea.v;
      const vb = eb.v instanceof Stor ? eb.v.expr : eb.v;
      if (va && va.k === "Reg" && vb && vb.k === "Reg" && va.n === vb.n) { out.set(fk, { slot, v: va }); continue; }
    }
    if (ina) out.delete(fk);
    const isint = (typeof slot === "number");
    for (const x of [ina ? ea.v : undefined, inb ? eb.v : undefined]) {
      if (prog && x instanceof LTbl && x.tid === null) prog.usedtbl(x);
      if (ina || inb) {
        if (_isphan(x) || x === vglob || !isint || (x instanceof LTbl && nregs !== null && slot > nregs)) lost.add(isint ? slot : fk);
      }
    }
  }
  const finlost = new Set();
  for (const e of lost) { const fk = (typeof e === "number") ? ("R" + e) : e; if (!out.has(fk)) finlost.add(e); }
  return [out, finlost];
}
function seteq(a, b) { if (a.size !== b.size) return false; for (const x of a) if (!b.has(x)) return false; return true; }

const pbud = Number(process.env.DEVERT_PASSBUDGET) || 50000;
const pmax = 12;
function mergelive(acc, lv) {
  let grew = false, nw = 0;
  for (const [pc, s] of lv) {
    const a = acc.get(pc);
    if (a === undefined) { acc.set(pc, new Set(s)); nw += 1; continue; }
    for (const t of s) if (!a.has(t)) { a.add(t); grew = true; }
  }
  return [grew, nw];
}
function passlog(ci, pass, bud, stp, stts, first, acc, hit, grew, nw) {
  if (!process.env.DEVERT_PASSLOG) return;
  process.stderr.write("PASS ci=" + ci + " pass=" + pass + " budget=" + bud + " steps=" + stp + " stts=" + stts + " resteps=" + (stp - first) + " live=" + (acc === null ? 0 : acc.size) + " hit=" + hit + " grew=" + grew + " newpcs=" + nw + " heapMB=" + (process.memoryUsage().heapUsed / 1048576).toFixed(0) + " t=" + process.uptime().toFixed(0) + "\n");
}
function pcof(s) { const p = s.pc; return typeof p === "bigint" ? Number(p) : typeof p === "number" ? p : 0; }
function pclt(a, b) { return a[0] !== b[0] ? a[0] < b[0] : a[1] < b[1]; }
class Pcq {
  constructor() { this.h = []; this.n = 0; }
  get length() { return this.h.length; }
  push(k, pc) {
    const h = this.h; let i = h.length; h.push([pc, this.n++, k]);
    while (i > 0) { const p = (i - 1) >> 1; if (!pclt(h[i], h[p])) break; const t = h[i]; h[i] = h[p]; h[p] = t; i = p; }
  }
  pop() {
    const h = this.h; const top = h[0]; const last = h.pop();
    if (h.length) {
      h[0] = last; let i = 0;
      for (;;) {
        const l = 2 * i + 1, r = l + 1; let m = i;
        if (l < h.length && pclt(h[l], h[m])) m = l;
        if (r < h.length && pclt(h[r], h[m])) m = r;
        if (m === i) break;
        const t = h[i]; h[i] = h[m]; h[m] = t; i = m;
      }
    }
    return top[2];
  }
}

function nodetext(n) {
  const out = n.stmts.map(ir.fmtstmt);
  if (n.cond !== null && n.cond !== undefined) {
    out.push("if " + ir.fmtexpr(n.cond));
    out.push(n.then ? nodetext(n.then) : "-");
    out.push(n.els ? nodetext(n.els) : "-");
  } else if (n.outcome && n.outcome.o === "Next") out.push("-> " + n.outcome.state.key());
  else if (n.outcome && n.outcome.o === "Ret") out.push("ret " + ir.fmtmulti(n.outcome.values));
  return out.join("\n");
}
function bldptree(pths, d, strt) {
  if (pths.length === 1 && pths[0][0].length <= d) { const p = pths[0]; return Node(p[2].slice(strt), undefined, undefined, undefined, p[3]); }
  const p0 = pths[0];
  if (p0[0].length <= d) return Node(p0[2].slice(strt), undefined, undefined, undefined, p0[3]);
  const cond = p0[1][d][2];
  const at = p0[1][d][1];
  const stmt = p0[2].slice(strt, at);
  const tp = pths.filter((p) => p[0][d]);
  const fp = pths.filter((p) => !p[0][d]);
  const then = tp.length ? bldptree(tp, d + 1, at) : null;
  const els = fp.length ? bldptree(fp, d + 1, at) : null;
  if (then !== null && els !== null && nodetext(then) === nodetext(els)) { then.stmts = stmt.concat(then.stmts); return then; }
  return Node(stmt, cond, then, els);
}
function pthressig(p) {
  const outsig = p[2].map(ir.fmtstmt).join("\u0001");
  const oc = p[3];
  let ocsig;
  if (oc && oc.o === "Next") ocsig = "next\u0000" + oc.state.key();
  else if (oc && oc.o === "Ret") ocsig = "ret\u0000" + ir.fmtmulti(oc.values);
  else ocsig = "?\u0000" + repr(oc);
  return outsig + "\u0002" + ocsig;
}
function allrcnv(pths) {
  const s0 = pthressig(pths[0]);
  return pths.every((p) => pthressig(p) === s0);
}
function isdead(node, dead) {
  if (!node) return false;
  if (node.dead) return true;
  if (node.cond !== null && node.cond !== undefined) { if (!node.then || !node.els) return false; return isdead(node.then, dead) && isdead(node.els, dead); }
  if (node.outcome && node.outcome.o === "Next") return dead.has(node.outcome.state.key());
  return false;
}
function deadstts(nds) {
  const dead = new Set();
  for (const [k, nd] of nds) if (nd.dead) dead.add(k);
  let chg = dead.size > 0;
  while (chg) { chg = false; for (const [k, nd] of nds) if (!dead.has(k) && isdead(nd, dead)) { dead.add(k); chg = true; } }
  return dead;
}
function prndead(node, dead) {
  if (node === null || node === undefined || node.dead) return null;
  if (node.cond === null || node.cond === undefined) {
    if (node.outcome && node.outcome.o === "Next" && dead.has(node.outcome.state.key())) return null;
    return node;
  }
  const then2 = prndead(node.then, dead);
  const els2 = prndead(node.els, dead);
  if (node.then !== null && node.then !== undefined && node.els !== null && node.els !== undefined) {
    if (then2 === null && els2 === null) return null;
    if (then2 === null) { els2.stmts = node.stmts.concat(els2.stmts); return els2; }
    if (els2 === null) { then2.stmts = node.stmts.concat(then2.stmts); return then2; }
    node.then = then2; node.els = els2; return node;
  }
  node.then = (node.then !== null && node.then !== undefined) ? then2 : null;
  node.els = (node.els !== null && node.els !== undefined) ? els2 : null;
  if (node.then === null && node.els === null) return null;
  return node;
}

class Stpr {
  constructor(lf) { this.lf = lf; }
  runonce(st, fcts, lost, dec, tpfx) {
    const lf = this.lf;
    lf.out = []; lf.tcount = 0; lf.curpc = st.pc; lf.tmppfx = tpfx; lf.tabwrtn = new Map();
    const sc = lf.restore(st, fcts, lost);
    const it = new LiftItp(lf);
    lf.curit = it;
    it.dec = dec.slice();
    it.lpsub = st.sub;
    const inr = new Scp(sc);
    let sub = null; let oc;
    try {
      try {
        try { it.execblk(lf.vm.lpbody, inr); oc = "next"; }
        catch (e) {
          if (e instanceof ContSig) oc = "next";
          else if (e instanceof BrkSig) { it.execblk(lf.vm.after, sc); oc = ["ret", Multi([])]; }
          else throw e;
        }
      } catch (e) {
        if (e instanceof RetSig) oc = ["ret", e.values];
        else if (e instanceof LoopSig) { oc = "next"; sub = e.sub; }
        else throw e;
      }
      if (oc === "next") { lf.prncps(it); lf.scrub(sc); return [it, Next(lf.snps(sc, sub))]; }
      let m = (oc[1] && oc[1].k === "Multi") ? oc[1] : Multi([oc[1]]);
      const itms = []; let tail = m.tail;
      for (let i = 0; i < m.items.length; i++) {
        const x = m.items[i];
        if (x instanceof Spr && i === m.items.length - 1 && (tail === null || tail === undefined)) { for (const y of x.m.items) itms.push(lf.asexpr(y)); tail = x.m.tail; }
        else itms.push((x && x.k === "SymList") ? x : lf.valof(x));
      }
      lf.prncps(it, itms);
      return [it, Ret(Multi(itms, tail))];
    } catch (e) {
      if (e instanceof _DeadFork) { if (_capfork(it)) return [it, dsnt]; throw new Unsup("a closure the recorded run never created (its proto was never decoded)"); }
      throw e;
    }
  }
  step(st, fcts, lost, tpfx) {
    const pths = []; const todo = [[]];
    let rds = new Set(); let wr = null;
    while (todo.length) {
      const dec = todo.pop();
      const [it, oc] = this.runonce(st, fcts, lost, dec, tpfx);
      const tkn = it.dlog.map((d) => d[3]);
      for (let j = dec.length; j < tkn.length; j++) todo.push(tkn.slice(0, j).concat([!tkn[j]]));
      if (oc === dsnt) continue;
      for (const r of this.lf.stprds) rds.add(r);
      if (wr === null) wr = new Set(this.lf.wrtnnow);
      else { const nw = this.lf.wrtnnow; for (const w of [...wr]) if (!nw.has(w)) wr.delete(w); }
      if (pths.length > 128) {
        if (this._alldecdead(st, fcts, lost, tpfx, pths[0])) { this.lf.recuse(st.pc, rds, wr || new Set()); return bldptree([[[], [], pths[0][2], pths[0][3]]], 0, 0); }
        if (allrcnv(pths)) { this.lf.recuse(st.pc, rds, wr || new Set()); return Node(pths[0][2].slice(), undefined, undefined, undefined, pths[0][3]); }
        throw new Unsup("too many paths in one instruction");
      }
      pths.push([tkn, it.dlog, this.lf.out.slice(), oc]);
    }
    this.lf.recuse(st.pc, rds, wr || new Set());
    if (!pths.length) { const n = Node([], undefined, undefined, undefined, null); n.dead = true; return n; }
    return bldptree(pths, 0, 0);
  }
  _alldecdead(st, fcts, lost, tpfx, base) {
    const tkn0 = base[0]; const n = tkn0.length;
    if (!n) return false;
    const sig = (out, oc) => nodetext(bldptree([[[], [], out, oc]], 0, 0));
    const basesig = sig(base[2], base[3]);
    for (let j = 0; j < n; j++) {
      const decj = tkn0.slice(); decj[j] = !decj[j];
      const [itj, ocj] = this.runonce(st, fcts, lost, decj, tpfx);
      if (ocj === dsnt) return false;
      const tknj = itj.dlog.map((d) => d[3]);
      if (tknj.length !== n || tknj[j] === tkn0[j]) return false;
      for (let k = 0; k < n; k++) if (k !== j && tknj[k] !== tkn0[k]) return false;
      if (sig(this.lf.out.slice(), ocj) !== basesig) return false;
    }
    return true;
  }
}

class Prog {
  constructor(root, dumpjson) {
    this.root = root;
    this.funcs = astfns(root);
    this.vms = new Map();
    for (const [mk, itp] of findvms(root)) this.vms.set(mk.location, new VmMdl(mk, itp));
    this.iats = new Map();
    for (const [fn, call] of iatcalls(root)) { const p = lclref(call.args[0]); this.iats.set(fn.location, p ? p[1] : null); }
    this.dump = new Dump(dumpjson, this.funcs);
    const g = new LTbl();
    const nms = Object.keys(sym.conc).concat(["table.pack", "table.unpack", "table.move", "table.create"]);
    for (const lib of ["bit32", "string", "table", "math", "buffer"]) {
      const t = new LTbl();
      for (const nm of nms) if (nm.startsWith(lib + ".")) hsetraw(t, Buffer.from(nm.slice(nm.indexOf(".") + 1), "latin1"), new Bltn(nm));
      hsetraw(g, Buffer.from(lib, "latin1"), t);
    }
    for (const nm of ["select", "unpack", "getfenv", "setfenv", "tonumber", "setmetatable"]) hsetraw(g, Buffer.from(nm, "latin1"), new Bltn(nm));
    this.globals = g;
    this.stats = { functions: 0, errors: 0, fallbacks: 0, stubs: 0 };
    this.stubsts = new Set();
    this.tblcnt = 0;
    this.tblstmts = new Map();
    this.tbldeps = new Map();
    this.tblused = new Set();
    this.boolamb = new Set();
    this.crrof = new Map();
    this.tabcrrof = new Map();
    this.chkprts = new Set();
    this.mbchkprts = new Set();
    for (let i = 0; i < this.dump.caps.length; i++) {
      const vars = this.dump.caps[i].vars;
      let ischck = false, ismb = false;
      for (const val of vars.values()) {
        if (!(val instanceof LTbl)) continue;
        for (const e of val.h.values()) {
          const hv = e.v;
          if (hv === cmod) ischck = true;
          if (typeof hv === "bigint" && hv > 100000000n && hv < 2147483648n) ismb = true;
        }
      }
      if (ischck) this.chkprts.add(i);
      if (ismb) this.mbchkprts.add(i);
    }
  }
  crrofget(mk) { let s = this.crrof.get(mk); if (s === undefined) { s = new Set(); this.crrof.set(mk, s); } return s; }
  tabcrrofget(mk) { let s = this.tabcrrof.get(mk); if (s === undefined) { s = new Set(); this.tabcrrof.set(mk, s); } return s; }
  newtblid() { this.tblcnt += 1; return this.tblcnt; }
  usedtbl(t) { if (hhas(t, tblid)) this.tblused.add(hget(t, tblid)); }
  tblstmtsadd(id, st) { let a = this.tblstmts.get(id); if (a === undefined) { a = []; this.tblstmts.set(id, a); } a.push(st); }
  tbldepsadd(a, b) { let s = this.tbldeps.get(a); if (s === undefined) { s = new Set(); this.tbldeps.set(a, s); } s.add(b); }
  deadstmts() {
    const used = new Set(this.tblused);
    const todo = [...used];
    while (todo.length) { const n = todo.pop(); const deps = this.tbldeps.get(n); if (deps) for (const d of deps) if (!used.has(d)) { used.add(d); todo.push(d); } }
    const dead = new Set();
    for (const [n, sts] of this.tblstmts) if (!used.has(n)) for (const x of sts) dead.add(x);
    return dead;
  }
  walk(ci, uplst, lim) {
    if (lim === undefined) lim = mst;
    const lf = new ProtoLftr(this, ci, uplst);
    let pass = 0;
    let acc = null;
    let bud = pbud;
    let fin = false;
    let xcd = false;
    for (let rstai = 0; rstai < mrst;) {
      lf.newcrr = false;
      lf.pcuse = new Map();
      lf.boxes = new Map(); lf.top = null; lf.iters = new Map(); lf.facts = new Fcts(); lf.lost = new Set();
      const s0 = lf.initst();
      lf.basetabsids = new Set(); for (const [t] of lf.basetabs.values()) lf.basetabsids.add(t);
      const st = new Stpr(lf);
      const k0 = s0.key();
      const stts = new Map([[k0, s0]]);
      const fctsin = new Map([[k0, [lf.entfcts(), new Set()]]]);
      const nds = new Map();
      const sid = new Map();
      const first = [];
      const po = !fin || xcd;
      const work = po ? new Pcq() : [k0];
      if (po) work.push(k0, pcof(s0));
      const inwk = new Set([k0]);
      let stp = 0;
      let rsta = false;
      let hit = false;
      while (work.length) {
        if (po && stp >= bud) { hit = true; break; }
        const k = work.pop();
        inwk.delete(k);
        const s = stts.get(k);
        const [fa, lo] = fctsin.get(k);
        stp += 1;
        const eff = fin ? lim : lim * pslk;
        if (first.length > eff || stp > eff * 4 + first.length * 8) throw new Unsup("state limit (" + lim + " instruction states)");
        let sidk = sid.get(k); if (sidk === undefined) { sidk = sid.size + 1; sid.set(k, sidk); }
        let node;
        try {
          node = st.step(s, fa, lo, s.pc + "_" + sidk + "_");
        } catch (e) {
          if (e instanceof Unsup) { node = Node([], undefined, undefined, undefined, null); node.error = e.message + ", function " + ci; if (process.env.DEVERT_PASSLOG) process.stderr.write("UNSUP ci=" + ci + " pass=" + (fin ? "final" : pass) + " pc=" + String(s.pc) + " " + e.message + "\n"); }
          else throw e;
        }
        if (lf.newcrr) { rsta = true; break; }
        if (!nds.has(k)) first.push(k);
        nds.set(k, node);
        const nxt = []; _nextst(node, nxt);
        for (let i = nxt.length - 1; i >= 0; i--) {
          const ns = nxt[i];
          const nk = ns.key();
          if (!fctsin.has(nk)) { stts.set(nk, ns); fctsin.set(nk, [ns.facts, ns.lost]); }
          else {
            const [of, ol] = fctsin.get(nk);
            const [mf, ml] = meetfacts(of, ns.facts, ol, ns.lost, lf.nregs, this);
            if (mf.size === of.size && seteq(ml, ol)) continue;
            fctsin.set(nk, [mf, ml]);
          }
          if (!inwk.has(nk)) { if (po) work.push(nk, pcof(ns)); else work.push(nk); inwk.add(nk); }
        }
      }
      if (rsta) { rstai += 1; continue; }
      if (!fin) {
        if (acc === null) acc = new Map();
        const [grew, nw] = mergelive(acc, lf.lvns(nds, stts));
        passlog(ci, pass, bud, stp, stts.size, first.length, acc, hit, grew, nw);
        pass += 1;
        if (hit) xcd = true;
        if ((!hit && !grew) || pass >= pmax) fin = true; else bud = Math.ceil(bud * 1.5);
        lf.live = acc;
        continue;
      }
      passlog(ci, xcd ? "final-po" : "final", 0, stp, stts.size, first.length, acc, false, false, 0);
      if (fin) {
        let dead = deadstts(nds);
        if (dead.has(k0)) dead = new Set();
        let ordr;
        if (dead.size) {
          ordr = [];
          for (const k of first) { if (dead.has(k)) continue; const pn = prndead(nds.get(k), dead); if (pn !== null) ordr.push([k, pn]); }
        } else {
          ordr = first.map((k) => [k, nds.get(k)]);
        }
        if (lf.entout && lf.entout.length) {
          const ek = "('E', 0)";
          ordr.unshift([ek, Node(lf.entout.slice(), undefined, undefined, undefined, Next(s0))]);
          return [ek, ordr, lf];
        }
        return [k0, ordr, lf];
      }
    }
    throw new Unsup("the interpreter state kept growing (restarts)");
  }
}

function prn(ordr, dead) {
  const drop = (st) => dead.has(st) || (st.s === "Assign" && st.value && st.value.k === "ClosureExpr" && st.value.runtime);
  const walkn = (n) => { if (!n) return; n.stmts = n.stmts.filter((x) => !drop(x)); walkn(n.then); walkn(n.els); };
  for (const [, node] of ordr) walkn(node);
}

function cnterr(n) { if (!n) return 0; let c = n.error ? 1 : 0; if (n.cond !== null && n.cond !== undefined) c += cnterr(n.then) + cnterr(n.els); return c; }
function collcls(node, out, seen) {
  if (node === null || node === undefined) return;
  for (const s of node.stmts) scanval(s, out, seen);
  if (node.cond !== null && node.cond !== undefined) { scanval(node.cond, out, seen); collcls(node.then, out, seen); collcls(node.els, out, seen); }
  else if (node.outcome && node.outcome.o === "Ret") scanval(node.outcome.values, out, seen);
}
function scanval(x, out, seen) {
  if (x === null || x === undefined || typeof x !== "object") return;
  if (x.k === "ClosureExpr") { if (!seen.has(x)) { seen.add(x); out.push(x); } for (const u of x.upvals) scanval(u, out, seen); return; }
  if (Array.isArray(x)) { for (const e of x) scanval(e, out, seen); return; }
  if (Buffer.isBuffer(x)) return;
  for (const k of Object.keys(x)) scanval(x[k], out, seen);
}

function capnm(caps, reg, dep) { const v = (caps instanceof Map) ? caps.get(reg) : caps[reg]; return v !== undefined ? v : ((dep === 0 ? "r" : "r" + dep + "_") + reg); }
function upnmobj(upnm) { const o = {}; for (const i of Object.keys(upnm)) o[String(i)] = upnm[i]; return o; }
function memokey(ci, dep, upnm, kinds) {
  const cis = (ci instanceof StubProto) ? ("stub:" + ci.where) : (ci instanceof GtrProto) ? ("getter:" + ci.n) : String(ci);
  const up = Object.keys(upnm).map(Number).sort((a, b) => a - b).map((i) => i + "=" + upnm[i]).join(",");
  const kin = Object.keys(kinds).map(Number).sort((a, b) => a - b).map((i) => i + "=" + kindstr(kinds[i])).join(",");
  return cis + "|" + dep + "|" + up + "|" + kin;
}
function kindstr(v) { if (Array.isArray(v)) return "(" + v.map((x) => (typeof x === "bigint" ? x + "n" : sym.isby(x) ? "b" + x.toString("hex") : String(x))).join(",") + ")"; return String(v); }

const psreg = 500000;
function _eachreg(x, cb) {
  if (x === null || x === undefined || typeof x !== "object") return;
  if (Array.isArray(x)) { for (const e of x) _eachreg(e, cb); return; }
  if (x.k === "Reg") { cb(x.n); return; }
  if (x.k === "MaybeBox") { cb(x.reg); return; }
  for (const k of Object.keys(x)) { if (k === "k") continue; _eachreg(x[k], cb); }
}
function _eachcls(x, cb) {
  if (x === null || x === undefined || typeof x !== "object") return;
  if (Array.isArray(x)) { for (const e of x) _eachcls(e, cb); return; }
  if (x.k === "ClosureExpr") cb(x);
  for (const k of Object.keys(x)) { if (k === "k") continue; _eachcls(x[k], cb); }
}
function _eachstmt(n, cb) {
  if (!n) return;
  for (const s of (n.stmts || [])) cb(s);
  if (n.cond !== null && n.cond !== undefined) { cb({ _cond: n.cond }); _eachstmt(n.then, cb); _eachstmt(n.els, cb); }
  else if (n.outcome && n.outcome.o === "Ret") cb({ _ret: n.outcome.values });
}
function drvprms(sord, dep) {
  try {
    if (!sord.length) return [];
    const pfx = dep === 0 ? "r" : "r" + dep + "_";
    const ent = sord[0];

    const bykey = new Map(); for (const b of sord) bykey.set(b.key, b);
    const prol = new Set();
    { let cur = ent, grd = 0; while (cur && grd++ < sord.length + 2) { prol.add(cur); const n = cur.node; if (n.cond !== null && n.cond !== undefined) break; if (!n.outcome || n.outcome.o !== "Next") break; const nb = bykey.get(n.outcome.key); if (!nb || prol.has(nb)) break; cur = nb; } }

    const leadpairs = []; const leadseen = new Set();
    for (const s of (ent.node.stmts || [])) {
      if (s.s === "Assign" && s.target && s.target.k === "Reg" && s.value && s.value.k === "Vararg") { if (!leadseen.has(s.value.i)) { leadseen.add(s.value.i); leadpairs.push([s.value.i, s.target.n]); } }
      else break;
    }

    const rds = new Map(), readprol = new Map(), copyprol = new Map(), capd = new Set();
    let maxidx = 0; const tls = [];
    const addread = (r, p) => { rds.set(r, (rds.get(r) || 0) + 1); if (p) readprol.set(r, (readprol.get(r) || 0) + 1); };
    for (const b of sord) {
      const p = prol.has(b);
      _eachstmt(b.node, (s) => {
        if (s.s === "Assign" && s.target && s.target.k === "Reg" && s.value && s.value.k === "Reg") {
          addread(s.value.n, p);
          if (p && s.target.n < psreg) { if (!copyprol.has(s.value.n)) copyprol.set(s.value.n, []); copyprol.get(s.value.n).push(s.target.n); }
        } else if (s.s === "Assign") { _eachreg(s.value, (r) => addread(r, p)); if (s.target && s.target.k !== "Reg") _eachreg(s.target, (r) => addread(r, p)); }
        else if (s.s === "CallStmt") { _eachreg(s.fn, (r) => addread(r, p)); _eachreg(s.args, (r) => addread(r, p)); }
        else if (s.s === "SetList") { _eachreg(s.tbl, (r) => addread(r, p)); _eachreg(s.values, (r) => addread(r, p)); }
        else if (s.s === "Close") _eachreg(s.reg, (r) => addread(r, p));
        else if (s._cond) _eachreg(s._cond, (r) => addread(r, p));
        else if (s._ret) _eachreg(s._ret, (r) => addread(r, p));
        const v = s.s === "Assign" ? s.value : s._ret ? s._ret : s.s === "SetList" ? s.values : s.s === "CallStmt" ? s.args : null;
        if (v) _eachcls(v, (ce) => { for (const u of (ce.upvals || [])) { if (u && u.k === "Reg") capd.add(u.n); if (u && u.k === "MaybeBox") capd.add(u.reg); } });
        const cnss = (x) => { if (!x || typeof x !== "object") return; if (Array.isArray(x)) { x.forEach(cnss); return; } if (x.k === "Vararg") { if (x.i > maxidx) maxidx = x.i; return; } if (x.k === "VarargTail") { tls.push(x.start); return; } for (const k of Object.keys(x)) { if (k === "k") continue; cnss(x[k]); } };
        if (s.s) cnss(s); else if (s._cond) cnss(s._cond); else if (s._ret) cnss(s._ret);
      });
    }

    let top = Math.max(0, ...leadpairs.map((q) => q[0]), maxidx);
    if (tls.length) top = Math.min(top, Math.min(...tls) - 1);

    const rslv = (r) => { const seen = new Set(); while (!seen.has(r)) { seen.add(r); const rc = rds.get(r) || 0; const cp = copyprol.get(r) || []; if (rc === 1 && cp.length === 1 && !capd.has(r)) { r = cp[0]; continue; } break; } return r; };

    const nmd = (rf) => { if (capd.has(rf)) return true; const rc = rds.get(rf) || 0; if (rc === 0) return false; if (rc >= 2) return true; return (readprol.get(rf) || 0) === 0; };
    const lead = new Map();
    for (const [i, r] of leadpairs) { if (i > top) continue; const rf = rslv(r); if (rf < psreg && nmd(rf)) lead.set(i, pfx + rf); }
    const nms = []; const used = new Set([...lead.values()]);
    for (let j = 1; j <= top; j++) { let nm = lead.get(j); if (nm === undefined) { nm = "arg" + j; while (used.has(nm)) nm += "_"; used.add(nm); } nms.push(nm); }
    if (tls.length > 0 || maxidx > top) nms.push("...");
    return nms;
  } catch (e) { return []; }
}

class FnLftr {
  constructor(prog) { this.prog = prog; this.lifting = new Set(); this.memo = new Set(); this.records = []; }
  lift(ci, uplst, upnm, dep) {
    if (dep === undefined) dep = 0;
    const prog = this.prog;
    prog.stats.functions += 1;
    this.lifting.add(ci);
    try {
      const [k0, ordr] = prog.walk(ci, uplst);
      let nerr = 0; for (const [, n] of ordr) nerr += cnterr(n);
      prog.stats.errors += nerr;
      const sord = serord(ordr);
      this.records.push({ ci, entry_key: k0, params: drvprms(sord, dep), upnames: upnmobj(upnm), order: sord });
      prn(ordr, prog.deadstmts());
      const kids = []; const seen = new Set();
      for (const [, n] of ordr) collcls(n, kids, seen);

      const pnm = {}; for (const i of Object.keys(upnm)) pnm["up," + i] = upnm[i];
      for (const c of kids) this.closure(c, pnm, dep);
    } finally { this.lifting.delete(ci); }
  }
  closure(c, parnms, dep) {
    const ci = c.proto;
    if (ci instanceof StubProto) { this.prog.stubsts.add(ci.where); this.prog.stats.stubs = this.prog.stubsts.size; return; }
    if (ci instanceof NatProto) return;
    if (!(ci instanceof GtrProto) && this.lifting.has(ci)) return;
    const caps = c.capnames || {};
    const kinds = c.kinds || {};
    const upnm = {};
    for (let i = 1; i <= c.upvals.length; i++) {
      if (Array.isArray(kinds[i])) continue;
      const e = c.upvals[i - 1];
      if (e instanceof MbBox) upnm[i] = capnm(caps, e.reg, dep);
      else if (e && e.k === "Reg") upnm[i] = capnm(caps, e.n, dep);
      else if (e && e.k === "Upval") upnm[i] = (parnms && parnms["up," + e.idx]) || ("upv" + e.idx);
      else upnm[i] = "nil";
    }
    if (ci instanceof GtrProto) return;
    const key = memokey(ci, dep, upnm, kinds);
    if (this.memo.has(key)) return;
    this.memo.add(key);
    try { this.lift(ci, new UpLst(kinds), upnm, dep + 1); }
    catch (ex) { if (ex instanceof Unsup) this.prog.stats.fallbacks += 1; else throw ex; }
  }
}

function liftprog(root, dumpjson) {
  const prog = new Prog(root, dumpjson);
  const fl = new FnLftr(prog);
  fl.lift(0, new UpLst(), {}, 0);
  const out = { stats: prog.stats, ncaps: prog.dump.caps.length, funcs: fl.records };
  if (prog.natives) Object.defineProperty(out, "natives", { value: prog.natives, enumerable: false });
  return out;
}

module.exports = { liftprog };

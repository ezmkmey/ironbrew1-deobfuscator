"use strict";
const fs = require("fs");
const spin = "__SPIN.n=__SPIN.n+1;if __SPIN.n>=__SPIN.step then __SPIN.f()end;";

const spos = (loc) => loc.split(" - ")[0].split(",").map(Number);
const epos = (loc) => loc.split(" - ")[1].split(",").map(Number);
const le = (a, b) => a[0] < b[0] || (a[0] === b[0] && a[1] <= b[1]);
const lt = (a, b) => a[0] < b[0] || (a[0] === b[0] && a[1] < b[1]);
const isobj = (v) => v && typeof v === "object";
const lref = (x) => (isobj(x) && x.type === "AstExprLocal") ? [x.local.name, x.local.location] : null;

function* iter(n) {
	const st = [n];
	while (st.length) {
		const x = st.pop();
		if (Array.isArray(x)) { for (let i = x.length - 1; i >= 0; i--) st.push(x[i]); }
		else if (isobj(x)) {
			yield x;
			const ks = Object.keys(x);
			for (let i = ks.length - 1; i >= 0; i--) { const k = ks[i]; if (k !== "local" && k !== "location" && isobj(x[k])) st.push(x[k]); }
		}
	}
}

function disploop(fn) {
	for (const s of fn.body.body) {
		if (s.type !== "AstStatWhile") continue;
		const c = s.condition;
		if (!(c.type === "AstExprConstantBool" && c.value)) continue;
		const b = s.body.body;
		if (b.length && b[0].type === "AstStatAssign" && b[0].values[0].type === "AstExprIndexExpr") return s;
	}
	return null;
}

function findvms(root) {
	const out = [];
	for (const x of iter(root)) {
		if (x.type !== "AstExprFunction") continue;
		const b = x.body.body;
		if (!b.length || b[b.length - 1].type !== "AstStatReturn" || !b[b.length - 1].list.length) continue;
		const inr = b[b.length - 1].list[0];
		if (inr.type === "AstExprFunction" && inr.vararg && disploop(inr)) out.push([x, inr]);
	}
	return out;
}

function* exprsof(node) {
	const st = [node];
	while (st.length) {
		const x = st.pop();
		if (Array.isArray(x)) { for (const e of x) st.push(e); }
		else if (isobj(x)) {
			const t = x.type || "";
			if (t === "AstExprFunction") { yield x; continue; }
			if (t.startsWith("AstStat") && x !== node) continue;
			for (const k in x) if (!["local", "location", "body", "thenbody", "elsebody"].includes(k) && isobj(x[k])) st.push(x[k]);
		}
	}
}

function fnscp(fn, scp, tgt) {
	const sc = Object.assign({}, scp);
	if (fn.self) sc["self"] = fn.self.location;
	for (const a of fn.args) sc[a.name] = a.location;
	return blk(fn.body.body, sc, tgt);
}

function blk(stmts, scp, tgt) {
	const sc = Object.assign({}, scp);
	for (const s of stmts) {
		if (s === tgt) return sc;
		const t = s.type;
		let r;
		if (t === "AstStatLocalFunction") { sc[s.name.name] = s.name.location; if ((r = fnscp(s.func, sc, tgt))) return r; continue; }
		if (t === "AstStatFunction") { if ((r = fnscp(s.func, sc, tgt))) return r; continue; }
		for (const f of exprsof(s)) if ((r = fnscp(f, sc, tgt))) return r;
		if (t === "AstStatLocal") { for (const v of s.vars) sc[v.name] = v.location; }
		else if (t === "AstStatBlock") { if ((r = blk(s.body, sc, tgt))) return r; }
		else if (t === "AstStatIf") {
			if ((r = blk(s.thenbody.body, sc, tgt))) return r;
			const e = s.elsebody;
			if (e != null && (r = blk(e.type === "AstStatIf" ? [e] : e.body, sc, tgt))) return r;
		}
		else if (t === "AstStatWhile" || t === "AstStatRepeat") { if ((r = blk(s.body.body, sc, tgt))) return r; }
		else if (t === "AstStatFor") { const ic = Object.assign({}, sc); ic[s.var.name] = s.var.location; if ((r = blk(s.body.body, ic, tgt))) return r; }
		else if (t === "AstStatForIn") { const ic = Object.assign({}, sc); for (const v of s.vars) ic[v.name] = v.location; if ((r = blk(s.body.body, ic, tgt))) return r; }
	}
	return null;
}

const visat = (root, tgt) => blk(root.body, {}, tgt);

function upv(fn) {
	const fstrt = spos(fn.location), fend = epos(fn.location), out = {};
	for (const n of iter(fn)) if (n.type === "AstExprLocal") {
		const loc = n.local.location;
		if (!(le(fstrt, spos(loc)) && lt(spos(loc), fend))) out[loc] = n.local.name;
	}
	return out;
}
const upfld = (up) => Object.keys(up).sort().map((loc) => `["${loc}"]=${up[loc]}`).join(",");

function insd(loc, rng) { const [lo, hi] = rng.split(" - "); return le(spos(lo + " - " + lo), spos(loc)) && le(spos(loc), spos(hi + " - " + hi)); }

function annrds(itp) {
	const rng = itp.location, out = [];
	for (const blk of iter(itp)) {
		if (blk.type !== "AstStatBlock") continue;
		const body = blk.body || [];
		for (let i = 0; i < body.length; i++) {
			const st = body[i];
			if (st.type !== "AstStatAssign" || (st.vars || []).length !== 1 || (st.values || []).length !== 1) continue;
			const t = st.vars[0];
			if (t.type !== "AstExprIndexExpr" || t.index.type !== "AstExprConstantNumber" || t.index.value !== 1) continue;
			const box = lref(t.expr), idx = lref(st.values[0]);
			if (!box || !idx || insd(box[1], rng)) continue;
			for (const st2 of body.slice(i + 1, i + 3)) for (const n of iter(st2)) {
				if (n.type !== "AstExprIndexExpr") continue;
				const k = lref(n.expr), kk = lref(n.index);
				if (k && kk && kk[1] === idx[1] && !insd(k[1], rng) && !out.some((p) => p[0] === k[1] && p[1] === box[1])) out.push([k[1], box[1]]);
			}
		}
	}
	return out;
}

function prmown(root) {
	const out = {};
	for (const n of iter(root)) if (n.type === "AstExprFunction") (n.args || []).forEach((a, i) => { out[a.location] = [n, i]; });
	return out;
}

function iats(root) {
	const out = [], own = prmown(root), seen = new Set();
	for (const n of iter(root)) {
		if (n.type !== "AstExprCall") continue;
		const crgs = n.args || [];
		if (crgs.length < 2) continue;
		const fwd = crgs.slice(1).map(lref);
		if (fwd.some((f) => !f)) continue;
		const first = own[fwd[0][1]];
		if (!first || first[1] !== 0) continue;
		const fn = first[0];
		let ok = true;
		for (let i = 0; i < fwd.length; i++) { const o = own[fwd[i][1]]; if (!o || o[0] !== fn || o[1] !== i) { ok = false; break; } }
		if (!ok || !(fn.args && fn.args.length)) continue;
		const key = fn.body.location;
		if (seen.has(key)) continue;
		seen.add(key);
		out.push(fn);
	}
	return out;
}

function capedits(root) {
	const vms = findvms(root), itps = new Set(vms.map((v) => v[1])), edits = [];
	const st = [root];
	while (st.length) {
		const x = st.pop();
		if (Array.isArray(x)) { for (const e of x) st.push(e); continue; }
		if (!isobj(x)) continue;
		const t = x.type;
		if (t === "AstExprFunction" && itps.has(x)) continue;
		if (t === "AstStatLocalFunction" || t === "AstStatFunction") {
			const fn = x.func;
			if (t === "AstStatLocalFunction") {
				const up = upv(fn), tail = Object.keys(up).length ? `,{${upfld(up)}}` : "";
				edits.push([...epos(x.location), ` __IBF(${x.name.name},"${fn.location}"${tail}) `]);
			}
			st.push(fn.body);
			continue;
		}
		if (t === "AstExprFunction") {
			const up = upv(x), tail = Object.keys(up).length ? `,{${upfld(up)}}` : "";
			edits.push([...spos(x.location), "__IBF("]);
			edits.push([...epos(x.location), `,"${x.location}"${tail})`]);
		}
		for (const k in x) if (k !== "local" && k !== "location" && isobj(x[k])) st.push(x[k]);
	}
	for (const [mk, itp] of vms) {
		const ret = mk.body.body[mk.body.body.length - 1];
		const nms = visat(root, ret);
		if (nms == null) continue;
		const prms = mk.args.map((a) => a.name).join(",");
		const flds = Object.entries(nms).sort((a, b) => (a[1] < b[1] ? -1 : a[1] > b[1] ? 1 : 0)).map(([nm, loc]) => `["${loc}"]=${nm}`).join(",");
		const ann = annrds(itp).map((kb) => `{"${kb[0]}","${kb[1]}"}`).join(",");
		const mkr = marker(mk, itp);
		const text = `__IBC("${mk.location}",{${prms}},{${flds}},{${ann}}${mkr ? "," + mkr[1] : ""}) `;
		edits.push([...spos(ret.location), text]);
	}
	return edits;
}

function marker(mk, itp) {
	const rng = itp.location, prs = new Set();
	for (const n of iter(mk)) {
		if (n.type !== "AstExprIndexExpr" || !isobj(n.index) || n.index.type !== "AstExprIndexExpr") continue;
		const a = lref(n.expr), b = lref(n.index.expr);
		if (a && b && !insd(a[1], rng) && !insd(b[1], rng)) prs.add(a[1] + "|" + b[1]);
	}
	for (const n of iter(itp)) {
		if (n.type !== "AstStatAssign" || (n.vars || []).length !== 1 || (n.values || []).length !== 1) continue;
		const v = n.values[0], t = n.vars[0];
		if (v.type !== "AstExprTable" || (v.items || []).length !== 2 || t.type !== "AstExprIndexExpr") continue;
		const [x, y] = v.items.map((e) => (e.kind === "item" ? lref(e.value) : null));
		const stk = lref(t.expr);
		if (x && y && stk && prs.has(x[1] + "|" + y[1])) return [n, x[0], stk[0]];
	}
	return null;
}

function recedits(root) {
	const edits = [];
	for (const fn of iats(root)) edits.push([...spos(fn.body.location), ` __ZFPC(${fn.args[0].name}) `]);
	for (const [mk, itp] of findvms(root)) {
		const loop = disploop(itp);
		if (!loop) continue;
		const b0 = loop.body.body[0];
		const idxe = (b0.values && b0.values.length) ? b0.values[0].index : null;
		const pc = lref(idxe);
		const mkr = marker(mk, itp);
		if (mkr) edits.push([...spos(mkr[0].location), ` __IBMK(${mkr[1]},${mkr[2]}) `]);
		if (pc) edits.push([...spos(loop.body.location), mkr ? ` __SETPC(${pc[0]},${mkr[1]}) ` : ` __SETPC(${pc[0]}) `]);
	}
	const body = root.body;
	if (body.length && body[body.length - 1].type === "AstStatReturn" && (body[body.length - 1].list || []).length === 1) {
		const e = body[body.length - 1].list[0];
		edits.push([...spos(e.location), " __FORCERET("]);
		edits.push([...epos(e.location), ")"]);
	}
	return edits;
}

function spinedits(root) {
	const edits = [];
	for (const [, itp] of findvms(root)) edits.push([...spos(disploop(itp).body.location), " " + spin + " "]);
	return edits;
}

function insrat(src, edits) {
	const lns = src.split("\n");
	const ordr = edits.map((_, i) => i).sort((a, b) =>
		edits[a][0] !== edits[b][0] ? edits[b][0] - edits[a][0] :
		edits[a][1] !== edits[b][1] ? edits[b][1] - edits[a][1] : a - b);
	for (const i of ordr) { const [ln, col, text] = edits[i]; const s = lns[ln]; lns[ln] = s.slice(0, col) + text + s.slice(col); }
	return lns.join("\n");
}

function inst(root, src) {
	return insrat(src, capedits(root).concat(recedits(root), spinedits(root)));
}

function main() {
	const [astpth, srcpth, outpth] = process.argv.slice(2);
	const root = JSON.parse(fs.readFileSync(astpth, "latin1")).root;
	const src = fs.readFileSync(srcpth, "latin1");
	fs.writeFileSync(outpth, inst(root, src), "latin1");
}
main();

"use strict";
// usage: node main.js <source.luau> <dump.json> <handoff.json>   or   node main.js --retry-stats <source.luau> <dump.json>
const fs = require("fs");
const path = require("path");
const os = require("os");
const { execFileSync: xfs } = require("child_process");
const { liftprog } = require("./walk.js");
const { emhnd } = require("./emit.js");

const clu = process.env.CUSTOM_LUAU || path.resolve(__dirname, "..", "custom-luau.exe");
const tonum = (_, v) => (typeof v === "bigint" ? Number(v) : v);
function hstr(_, v) {
  if (typeof v !== "string" || /[^\x00-\xff]/.test(v)) return v;
  const b = Buffer.from(v, "latin1"), t = b.toString("utf8");
  return b[0] !== 1 && Buffer.from(t, "utf8").equals(b) ? t : { string_bytes: b.toString("hex") };
}
function hjson(o) {
  let nz = false;
  const t = JSON.stringify(o, (k, v) => (Object.is(v, -0) && (nz = true), hstr(k, v)), 1);
  if (!nz) return t;
  let m = "negz";
  for (let i = 0; t.includes(m); i++) m = "negz" + i;
  return JSON.stringify(o, (k, v) => (Object.is(v, -0) ? m : hstr(k, v)), 1).split(`"${m}"`).join("-0.0");
}

function prsluau(srcbts) {
  const tmp = path.join(os.tmpdir(), "ibfe_" + process.pid + "_" + Date.now() + ".lua");
  try {
    fs.writeFileSync(tmp, srcbts);
    const out = xfs(clu, ["--ast", tmp], { maxBuffer: 1024 * 1024 * 1024 });
    return JSON.parse(out.toString("latin1")).root;
  } finally { try { fs.unlinkSync(tmp); } catch {} }
}

function liftgrph(srcpth, dumppth) {
  const root = prsluau(fs.readFileSync(srcpth));
  const dump = JSON.parse(fs.readFileSync(dumppth, "utf8"));
  const out = liftprog(root, dump);
  return { graph: JSON.parse(JSON.stringify(out, tonum)), dump };
}

function eachnode(n, fn) {
  if (!n) return;
  fn(n);
  if (n.cond !== undefined && n.cond !== null) { eachnode(n.then, fn); eachnode(n.els, fn); }
}
function rtrstat(srcpth, dumppth) {
  const { graph: grph, dump } = liftgrph(srcpth, dumppth);
  const caps = dump.caps || [];
  const seen = new Set(), ids = [];
  for (const f of grph.funcs) for (const b of f.order) eachnode(b.node, (nd) => {
    if (!nd.error) return;
    const m = /\bfunction (\d+)\b/.exec(nd.error);
    if (!m) return;
    const ci = Number(m[1]);
    const o = caps[ci] && caps[ci].order;
    if (Number.isInteger(o) && !seen.has(o)) { seen.add(o); ids.push(o); }
  });
  ids.sort((a, b) => a - b);
  const st = grph.stats;
  return { stats: { functions: st.functions, errors: st.errors, stubs: st.stubs, fallbacks: st.fallbacks }, ids };
}

function usg(code) {
  const w = code ? console.error : console.log;
  w("usage: node main.js <source.luau> <dump.json> <handoff.json>");
  w("       node main.js --retry-stats <source.luau> <dump.json>");
  process.exit(code);
}

function main() {
  const args = process.argv.slice(2);
  if (args[0] === "--retry-stats") {
    if (args.length < 3) usg(2);
    const r = rtrstat(args[1], args[2]);
    process.stdout.write("STATS " + JSON.stringify(r.stats) + "\n");
    process.stdout.write("STUB_ORDER_IDS " + JSON.stringify(r.ids) + "\n");
    return;
  }
  if (args.length < 3 || args[0] === "-h" || args[0] === "--help") usg(args[0] === "-h" || args[0] === "--help" ? 0 : 2);
  const { graph: grph } = liftgrph(args[0], args[1]);
  fs.writeFileSync(args[2], hjson(emhnd(grph)));
}
main();

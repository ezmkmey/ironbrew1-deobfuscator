"use strict";
const fs = require("fs");
const path = require("path");
const os = require("os");
const { spawnSync } = require("child_process");

const clu = process.env.CUSTOM_LUAU || path.join(__dirname, "custom-luau.exe");
const bexe = process.env.SL_EXE || path.join(process.env.SL_DIR || path.join(__dirname, "backend"), "semantic-lifter.exe");
const rdir = path.join(__dirname, "recorder");
const lift = path.join(__dirname, "lift", "main.js");
const usg = "usage: node src/devirt.js <obfuscated.luau> <out.luau>";

let work = "";

function fail(msg, log) {
  console.error(`devirt: ${msg}`);
  const lp = log ? path.join(work, log) : "";
  if (lp && fs.existsSync(lp)) console.error(fs.readFileSync(lp, "utf8").trimEnd().split("\n").slice(-3).join("\n"));
  if (work) console.error(`devirt: work files in ${work}`);
  process.exit(1);
}

function wipe(p) {
  const st = fs.lstatSync(p, { throwIfNoEntry: false });
  if (!st) return;
  if (st.isDirectory()) {
    for (const e of fs.readdirSync(p)) wipe(path.join(p, e));
    fs.rmdirSync(p);
  } else fs.unlinkSync(p);
}

const cenv = { ...process.env };
function put(key, val) {
  for (const k of Object.keys(cenv)) if (k.toUpperCase() === key) delete cenv[k];
  cenv[key] = val;
}

function run(tag, exe, args, log, opt = {}) {
  const fd = fs.openSync(path.join(work, log), "a");
  const res = spawnSync(exe, args, { stdio: ["ignore", opt.pipe ? "pipe" : fd, fd], cwd: opt.cwd, env: cenv, windowsHide: true, maxBuffer: 1024 * 1024 * 1024 });
  fs.closeSync(fd);
  if (res.error) fail(`${tag}: ${res.error.message}`, log);
  if (res.status !== 0 && !opt.any) fail(`${tag} failed (exit ${res.status})`, log);
  return res;
}

const [src, dst] = process.argv.slice(2);
if (!src || !dst) { console.error(usg); process.exit(2); }
const st = (f) => fs.statSync(f, { throwIfNoEntry: false });
if (!st(src) || !st(src).isFile()) fail(`no input file ${src}`);
if (st(dst) && st(dst).isDirectory()) fail(`${dst} is a folder; give the output file path`);
for (const f of [clu, bexe]) if (!fs.existsSync(f)) fail(`missing ${f}`);

const name = path.basename(dst).replace(/\.[^.]*$/, "").replace(/[^\w.-]/g, "_") || "module";
const root = process.env.DEVIRT_OUT ? path.resolve(process.env.DEVIRT_OUT) : os.tmpdir();
if (process.env.DEVIRT_OUT) {
  work = path.join(root, name);
  wipe(work);
  fs.mkdirSync(work, { recursive: true });
} else {
  work = fs.mkdtempSync(path.join(root, "devirt-"));
}
const at = (f) => path.join(work, f);
fs.mkdirSync(at("tmp"));
put("TEMP", at("tmp"));
put("TMP", at("tmp"));
const obf = at(name + ".luau");
fs.copyFileSync(src, obf);

const rt = at("rec");
fs.mkdirSync(rt);
fs.writeFileSync(path.join(rt, "in.ast"), run("ast", clu, ["--ast", obf], "rec.log", { pipe: true }).stdout);
run("inst", process.execPath, [path.join(rdir, "inst.js"), path.join(rt, "in.ast"), obf, path.join(rt, "patched.luau")], "rec.log");
const ptc = fs.readFileSync(path.join(rt, "patched.luau"), "latin1");
const host = run("host", clu, ["--devert-text", "host"], "rec.log", { pipe: true }).stdout.toString("latin1").replace(/\r\n/g, "\n");
const rtxt = fs.readFileSync(path.join(rdir, "rec.luau"), "latin1");
let lv = 0;
while (ptc.includes("]" + "=".repeat(lv) + "]")) lv++;
const eq = "=".repeat(lv);
const spin = ptc.includes("__SPIN") ? 24 + Math.floor(fs.statSync(obf).size / 10000) : 0;

function cap(pre) {
  const cfg = [spin && `spin = ${spin}`, `plugin_rt = "${rtxt.replace(/\\/g, "\\\\").replace(/"/g, '\\"').replace(/\n/g, "\\n").replace(/\r/g, "\\r")}"`, pre && `precall = {${pre.join(", ")}}`];
  fs.writeFileSync(path.join(rt, "harness.luau"), `local __SOURCE = [${eq}[\n${ptc}]${eq}]\nlocal __CONFIG = {${cfg.filter(Boolean).join(", ")}}\n${host}`, "latin1");
  const cd = path.join(rt, "cap"), rd = (f) => (fs.existsSync(path.join(cd, f)) ? fs.readFileSync(path.join(cd, f), "latin1") : "");
  wipe(cd);
  fs.mkdirSync(cd);
  const res = run("capture", clu, ["--executor", "-O1", "-g1", "--capture-values", "--capture-dir", cd, "--capture-status", path.join(cd, "status.json"), "--run-seconds", "1800", path.join(rt, "harness.luau")], "rec.log", { cwd: rt, any: true });
  const sm = /"seconds":\s*([\d.]+)/.exec(rd("status.json")), secs = sm ? Number(sm[1]) : NaN;
  if (secs >= 1800) fail(`${clu} ran into the 1800 s crash guard, so its dump is not used`, "rec.log");
  let v, sv;
  for (const ln of rd("dump.jsonl").split("\n")) {
    const m = /^\{"seq":\d+,"tag":"(ibdump|ibstat)","v":"(.*)"\}\s*$/.exec(ln);
    if (m && m[1] === "ibdump") v = m[2]; else if (m) sv = m[2];
  }
  if (v === undefined || Number.isNaN(secs)) fail(`capture failed (exit ${res.status})`, "rec.log");
  fs.appendFileSync(at("rec.log"), `ibrec ${pre ? "precall " : ""}${sv || ""} secs=${secs}\n`);
  return (/\0IBDUMP ([^\n]*)/.exec(JSON.parse(`"${v}"`)) || [])[1];
}

function bad(dump) {
  fs.writeFileSync(path.join(rt, "d.json"), dump, "latin1");
  const o = run("retry-stats", process.execPath, ["--max-old-space-size=8192", lift, "--retry-stats", obf, path.join(rt, "d.json")], "rec.log", { pipe: true }).stdout.toString("latin1");
  const num = (k) => Number((new RegExp(`"${k}":\\s*(\\d+)`).exec(o) || [])[1] || 0);
  const ids = /STUB_ORDER_IDS\s*\[([^\]]*)\]/.exec(o);
  return [num("errors") + num("stubs"), ids ? (ids[1].match(/\d+/g) || []).map(Number) : []];
}

let dump = cap();
if (!dump) fail("no IBDUMP from the capture run", "rec.log");
const [base, ids] = bad(dump);
if (base && ids.length) {
  const d2 = cap(ids);
  if (d2 && bad(d2)[0] < base) dump = d2;
}
fs.writeFileSync(at("dump.json"), dump + "\n", "latin1");
wipe(rt);
run("lift", process.execPath, ["--max-old-space-size=8192", lift, obf, at("dump.json"), at("handoff.json")], "lift.log");
run("frontend", clu, ["--devert", "frontend", "--", at("handoff.json"), at("ir.json"), name], "fe.log", { cwd: work });
if (!fs.existsSync(at("ir.json"))) fail("frontend wrote no ir", "fe.log");
run("emit", bexe, ["emit-luau", at("ir.json"), at("emitted.luau"), "standard-luau", clu], "emit.log");
if (!fs.existsSync(at("emitted.luau"))) fail("emit wrote no output", "emit.log");
if (fs.existsSync(at("natives.json"))) {
  const { splice } = require("./lift/natp.js");
  try {
    const nat = JSON.parse(fs.readFileSync(at("natives.json"), "latin1"));
    fs.writeFileSync(at("emitted.luau"), splice(fs.readFileSync(at("emitted.luau"), "latin1"), nat), "latin1");
  } catch (e) { fail(`native functions: ${e.message}`); }
}

function names() {
  const fd = fs.openSync(at("names.log"), "w");
  const res = spawnSync(clu, ["--devert", "names", "--", at("emitted.luau"), at("named.luau")], { stdio: ["ignore", fd, fd], cwd: work, env: cenv, windowsHide: true, timeout: 1800 * 1000 });
  fs.closeSync(fd);
  if (res.error && res.error.code === "ETIMEDOUT") fail("the names step ran into the 1800 s crash guard", "names.log");
  const m = /^names: (.*)$/m.exec(fs.readFileSync(at("names.log"), "latin1"));
  if (res.error) return res.error.message;
  if (res.status !== 0) return `exit ${res.status}`;
  if (!m) return "no status line";
  if (!m[1].startsWith("ok")) return m[1].replace(/^kept the backend names \((.*)\)$/, "$1").slice(0, 80);
  if (!fs.existsSync(at("named.luau"))) return "no output";
  const same = run("same", clu, ["--same", at("emitted.luau"), at("named.luau")], "names.log", { any: true }).status;
  return same === 0 ? "" : same === 1 ? "the renamed code compiles differently" : `--same exit ${same}`;
}
const why = names();
if (why) console.error(`devirt: names kept (${why})`);

fs.mkdirSync(path.dirname(path.resolve(dst)), { recursive: true });
fs.copyFileSync(at(why ? "emitted.luau" : "named.luau"), dst);
const cnt = fs.readFileSync(dst, "utf8").split("\n").filter((ln) => /\S/.test(ln)).length;
if (!process.env.DEVIRT_OUT) wipe(work);
console.log(`devirt: ok -> ${dst} (${cnt} lines)`);

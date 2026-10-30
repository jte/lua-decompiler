const TIMEOUT_MS = 60_000;
// Above this size, skip syntax highlighting — building that much DOM is slow.
const HIGHLIGHT_LIMIT = 200_000;

const $ = (sel) => document.querySelector(sel);
const meta = (name) => document.querySelector(`meta[name="${name}"]`)?.content.trim() ?? "";

const fileInput = $("#file");
const drop = $("#drop");
const fileInfo = $("#file-info");
const runBtn = $("#run");
const cancelBtn = $("#cancel");
const flattenBox = $("#flatten");
const statusEl = $("#status");
const output = $("#output");
const gutter = $("#gutter");
const copyBtn = $("#copy");
const downloadBtn = $("#download");

let file = null;       // { name, bytes: Uint8Array }
let worker = null;
let job = null;        // { id, timer, mode }
let nextId = 1;
let lastResult = null; // { text, mode }

// --- theme ------------------------------------------------------------------

function currentTheme() {
  const forced = document.documentElement.dataset.theme;
  if (forced) return forced;
  return matchMedia("(prefers-color-scheme: light)").matches ? "light" : "dark";
}

function syncThemeColor() {
  document.querySelector('meta[name="theme-color"]').content = currentTheme() === "light" ? "#f5f6fb" : "#0b0d12";
}

$("#theme-toggle").addEventListener("click", () => {
  const next = currentTheme() === "light" ? "dark" : "light";
  document.documentElement.dataset.theme = next;
  try { localStorage.setItem("theme", next); } catch {}
  syncThemeColor();
});
matchMedia("(prefers-color-scheme: light)").addEventListener("change", syncThemeColor);
syncThemeColor();

// --- analytics & GitHub -----------------------------------------------------

// Cloudflare Web Analytics only records page views; nothing about the file is
// ever sent anywhere.
const cfToken = meta("cf-beacon-token");
if (cfToken) {
  const s = document.createElement("script");
  s.defer = true;
  s.src = "https://static.cloudflareinsights.com/beacon.min.js";
  s.dataset.cfBeacon = JSON.stringify({ token: cfToken });
  document.head.append(s);
}

const repo = meta("github-repo");
if (repo) {
  fetch(`https://api.github.com/repos/${repo}`)
    .then((r) => (r.ok ? r.json() : null))
    .then((info) => {
      if (!info || typeof info.stargazers_count !== "number") return;
      const n = info.stargazers_count;
      $("#gh-star-count").textContent = n >= 1000 ? `${(n / 1000).toFixed(1)}k` : String(n);
      $("#gh-stars").hidden = false;
    })
    .catch(() => {});
}

// --- worker -----------------------------------------------------------------

function spawnWorker() {
  worker = new Worker(new URL("./worker.js", import.meta.url), { type: "module" });
  worker.onmessage = onResult;
  worker.onerror = (e) => {
    e.preventDefault();
    finish({ ok: false, fatal: true, error: e.message || "The worker crashed." });
  };
}

function resetWorker() {
  worker?.terminate();
  spawnWorker();
}

function mode() {
  return document.querySelector('input[name="mode"]:checked').value;
}

function setStatus(text, kind = "") {
  statusEl.textContent = text;
  statusEl.dataset.kind = kind;
}

function setBusy(busy) {
  runBtn.disabled = busy || !file;
  cancelBtn.hidden = !busy;
  document.body.classList.toggle("busy", busy);
}

function describeHeader(bytes) {
  const sig = String.fromCharCode(...bytes.slice(0, 4));
  if (sig === "\x1bLua") {
    const v = bytes[4];
    const name = `Lua ${v >> 4}.${v & 0xf}`;
    if (v < 0x51 || v > 0x55) return { ok: false, text: `${name} bytecode (only 5.1–5.5 are supported)` };
    return { ok: true, text: `${name} bytecode` };
  }
  if (sig.startsWith("\x1bLJ")) {
    return { ok: false, text: "LuaJIT bytecode is not supported" };
  }
  return { ok: false, text: "No Lua bytecode header — is this a compiled chunk?" };
}

function formatSize(n) {
  return n < 1024 ? `${n} B` : n < 1048576 ? `${(n / 1024).toFixed(1)} KB` : `${(n / 1048576).toFixed(1)} MB`;
}

async function loadFile(f) {
  if (!f) return;
  const bytes = new Uint8Array(await f.arrayBuffer());
  file = { name: f.name, bytes };
  const header = describeHeader(bytes);
  fileInfo.innerHTML = "";
  const name = document.createElement("strong");
  name.textContent = f.name;
  const info = document.createElement("span");
  info.textContent = ` · ${formatSize(bytes.length)} · ${header.text}`;
  info.className = header.ok ? "" : "warn";
  fileInfo.append(name, info);
  drop.classList.add("has-file");
  start();
}

function start() {
  if (!file) return;
  if (job) cancel(true);

  const id = nextId++;
  const timer = setTimeout(() => {
    resetWorker();
    finish({ id, ok: false, error: `Timed out after ${TIMEOUT_MS / 1000}s — the input may be too large or trigger a bug.` });
  }, TIMEOUT_MS);
  job = { id, timer, mode: mode() };

  setBusy(true);
  setStatus("Working…");
  // Copy the buffer so the original stays usable for re-runs.
  const bytes = file.bytes.slice().buffer;
  worker.postMessage({ id, bytes, mode: job.mode, flatten: flattenBox.checked }, [bytes]);
}

function cancel(silent = false) {
  if (!job) return;
  clearTimeout(job.timer);
  job = null;
  resetWorker();
  setBusy(false);
  if (!silent) setStatus("Cancelled");
}

function onResult({ data }) {
  if (!job || data.id !== job.id) return;
  finish(data);
}

function finish(res) {
  if (!job) return;
  const { mode: jobMode } = job;
  clearTimeout(job.timer);
  job = null;
  setBusy(false);
  if (res.fatal) resetWorker();

  if (res.ok) {
    lastResult = { text: res.output, mode: jobMode };
    const lines = render(res.output, jobMode === "decompile" || jobMode === "deobfuscate");
    setStatus(`${lines.toLocaleString()} lines · ${Math.round(res.ms)} ms`, "ok");
  } else {
    lastResult = null;
    gutter.textContent = "";
    output.textContent = res.error;
    output.classList.add("error");
    setStatus(res.fatal ? "Decompiler crashed" : "Failed", "error");
  }
  copyBtn.disabled = downloadBtn.disabled = !lastResult;
}

// --- rendering --------------------------------------------------------------

const LUA_TOKEN = new RegExp(
  [
    String.raw`(--\[(=*)\[[\s\S]*?\]\2\]|--[^\n]*)`,                          // 1 comment
    String.raw`(\[(=*)\[[\s\S]*?\]\4\]|"(?:[^"\\\n]|\\[\s\S])*"|'(?:[^'\\\n]|\\[\s\S])*')`, // 3 string
    String.raw`\b(0[xX][0-9a-fA-F]+(?:\.[0-9a-fA-F]*)?(?:[pP][+-]?\d+)?|\d+(?:\.\d*)?(?:[eE][+-]?\d+)?)\b`, // 5 number
    String.raw`\b(and|break|do|else|elseif|end|false|for|function|goto|if|in|local|nil|not|or|repeat|return|then|true|until|while)\b`, // 6 keyword
    String.raw`\b(self|_G|_ENV|assert|error|getmetatable|setmetatable|ipairs|pairs|next|pcall|xpcall|print|rawget|rawset|rawequal|rawlen|require|select|tonumber|tostring|type|unpack|load|loadstring|dofile|string|table|math|os|io|coroutine|debug|bit32|utf8)\b`, // 7 builtin
  ].join("|"),
  "g",
);

const escapeHtml = (s) => s.replace(/[&<>]/g, (c) => ({ "&": "&amp;", "<": "&lt;", ">": "&gt;" })[c]);

function highlightLua(src) {
  let html = "";
  let last = 0;
  for (const m of src.matchAll(LUA_TOKEN)) {
    html += escapeHtml(src.slice(last, m.index));
    const cls = m[1] ? "t-com" : m[3] ? "t-str" : m[5] ? "t-num" : m[6] ? "t-kw" : "t-bi";
    html += `<span class="${cls}">${escapeHtml(m[0])}</span>`;
    last = m.index + m[0].length;
  }
  return html + escapeHtml(src.slice(last));
}

function render(text, isLua) {
  const lines = text.split("\n").length;
  output.classList.remove("error");
  if (isLua && text.length <= HIGHLIGHT_LIMIT) {
    output.innerHTML = highlightLua(text);
  } else {
    output.textContent = text;
  }
  gutter.textContent = Array.from({ length: lines }, (_, i) => i + 1).join("\n");
  $("#code").scrollTo(0, 0);
  return lines;
}

function outputName() {
  const base = file.name.replace(/\.[^.]+$/, "") || "output";
  const ext = { decompile: "lua", deobfuscate: "lua", disassemble: "txt", cfg: "dot" }[lastResult.mode];
  const suffix = lastResult.mode === "deobfuscate" ? ".deobf" : "";
  return `${base}${suffix}.${ext}`;
}

// --- wiring -----------------------------------------------------------------

fileInput.addEventListener("change", () => loadFile(fileInput.files[0]));

for (const ev of ["dragenter", "dragover"]) {
  drop.addEventListener(ev, (e) => { e.preventDefault(); drop.classList.add("over"); });
}
for (const ev of ["dragleave", "drop"]) {
  drop.addEventListener(ev, () => drop.classList.remove("over"));
}
drop.addEventListener("drop", (e) => {
  e.preventDefault();
  loadFile(e.dataTransfer.files[0]);
});
// Dropping a file anywhere else shouldn't navigate away.
window.addEventListener("dragover", (e) => e.preventDefault());
window.addEventListener("drop", (e) => e.preventDefault());

document.querySelectorAll('input[name="mode"]').forEach((r) => r.addEventListener("change", start));
flattenBox.addEventListener("change", start);
runBtn.addEventListener("click", start);
cancelBtn.addEventListener("click", () => cancel());

copyBtn.addEventListener("click", async () => {
  await navigator.clipboard.writeText(lastResult.text);
  copyBtn.textContent = "Copied";
  setTimeout(() => (copyBtn.textContent = "Copy"), 1200);
});

downloadBtn.addEventListener("click", () => {
  const url = URL.createObjectURL(new Blob([lastResult.text], { type: "text/plain" }));
  const a = Object.assign(document.createElement("a"), { href: url, download: outputName() });
  a.click();
  URL.revokeObjectURL(url);
});

spawnWorker();

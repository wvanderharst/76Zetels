/* 76 Zetels - static website.
   Reads data/current.json and data/history.json (made by build_data.py) and
   renders each page client-side. Pages are switched with the #hash. */
"use strict";

const PAGES = [
  { id: "overzicht", title: "Overzicht", render: pageOverzicht },
  { id: "nieuws", title: "Nieuws", render: pageNieuws },
  { id: "door-de-tijd", title: "Door de tijd", render: pageDoorDeTijd },
  { id: "beleid", title: "Wiens beleid", render: pageBeleid },
  { id: "scenario", title: "Scenario's", render: pageScenario },
  { id: "huidige-coalitie", title: "Huidige coalitie", render: pageHuidigeCoalitie },
  { id: "eerste-kamer", title: "Eerste Kamer", render: pageEersteKamer },
  { id: "strategisch", title: "Strategisch stemmen", render: pageStrategisch },
  { id: "blokken", title: "Blokken", render: pageBlokken },
  { id: "vorige", title: "Vorige verkiezingen", render: pageVorige },
  { id: "over", title: "Over het model", render: pageOver },
];

const DIFFICULTY = ["Makkelijk", "Gemiddeld", "Moeilijk", "Extreem", "Kiezersbedrog", "Minderheidskabinet"];
const DIFF_COLOR = ["--r1", "--r2", "--r3", "--r4", "--r5", "--r6"];
const SERIES = ["--s1", "--s2", "--s3", "--s4", "--s5", "--s6", "--s7", "--s8"];
const MONTHS = ["jan", "feb", "mrt", "apr", "mei", "jun", "jul", "aug", "sep", "okt", "nov", "dec"];

let DATA = null;      // current.json
let HISTORY = null;   // history.json
let BACKTEST = {};    // backtest.json (formation backtest and calibration, may be missing)
let SIM = null;       // derived simulation helpers
let POSTS = [];       // posts.json
const state = {};     // per-page ui state, kept while navigating

/* ---------- small helpers ---------- */

const $ = (sel, el = document) => el.querySelector(sel);
function h(tag, attrs = {}, ...children) {
  const el = document.createElement(tag);
  for (const [k, v] of Object.entries(attrs || {})) {
    if (v == null || v === false) continue;
    if (k === "class") el.className = v;
    else if (k === "html") el.innerHTML = v;
    else if (k.startsWith("on")) el.addEventListener(k.slice(2), v);
    else el.setAttribute(k, v === true ? "" : v);
  }
  for (const c of children.flat()) {
    if (c == null || c === false) continue;
    el.append(c instanceof Node ? c : document.createTextNode(String(c)));
  }
  return el;
}
const css = (name) => getComputedStyle(document.documentElement).getPropertyValue(name).trim();
const nl = (v, d = 1) => (v == null || isNaN(v)) ? "–" :
  Number(v).toLocaleString("nl-NL", { minimumFractionDigits: d, maximumFractionDigits: d });
const pct = (v, d = 1) => `${nl(v, d)}%`;
function fmtDate(s, long = false) {
  const [y, m, d] = s.split("-").map(Number);
  return long ? `${d} ${MONTHS[m - 1]} ${y}` : `${MONTHS[m - 1]} '${String(y).slice(2)}`;
}
function parseDMY(s) { const [d, m, y] = s.split("-"); return `${y}-${m}-${d}`; }
const sum = (a) => a.reduce((x, y) => x + y, 0);

// main.py: a simulation in which the formation model found no cabinet
const NO_CABINET = "Geen kabinet";
const isNoCabinet = (parties) => (Array.isArray(parties) ? parties : String(parties).split(", "))[0] === NO_CABINET;

/* a cabinet "met A, B; zonder C": all of met in it, none of zonder (PRO counts its predecessor GL/PvdA) */
const proAlias = (p) => (p === "GL/PvdA" ? "PRO" : p);
const andList = (ps) => (ps.length > 1 ? `${ps.slice(0, -1).join(", ")} en ${ps.at(-1)}` : ps[0] || "");
function comboMatch(parties, met, zonder) {
  const set = new Set(parties.map(proAlias));
  if (set.has(NO_CABINET)) return false;
  return met.every((p) => set.has(proAlias(p))) && !zonder.some((p) => set.has(proAlias(p)));
}
function comboTitle(met, zonder) {
  const a = met.length ? `met ${andList(met)}` : "", b = zonder.length ? `zonder ${andList(zonder)}` : "";
  return `Een kabinet ${[a, b].filter(Boolean).join(", ")}`.trim();
}
/* "met VVD, CDA; zonder PRO, PVV" (a part without met/zonder counts as met) */
function parseCombo(text) {
  const out = { met: [], zonder: [] }, known = new Map((DATA?.factor?.parties || []).map((p) => [p.toLowerCase(), p]));
  for (const part of String(text || "").split(";")) {
    const m = part.trim().match(/^(met|zonder)\b\s*(.*)$/i);
    const key = m && m[1].toLowerCase() === "zonder" ? "zonder" : "met";
    (m ? m[2] : part).split(",").map((x) => x.trim()).filter(Boolean).forEach((x) => out[key].push(known.get(x.toLowerCase()) || x));
  }
  return out;
}
/* share of the simulations with such a cabinet, and the coalitions that make it up */
function comboStats(met, zonder) {
  const ids = SIM.all.filter((i) => comboMatch(SIM.coalitions[SIM.coalition[i]], met, zonder));
  return { pct: (ids.length / SIM.n) * 100, majorityPct: (ids.filter((i) => SIM.majority[i]).length / SIM.n) * 100, rows: coalitionRows(ids, SIM.n) };
}

/* key position: a party that is in every option the formation weighed (option 1, 2 and,
   when there is one, 3), so it can choose which cabinet is formed. "only": it is the only
   party with the key position. All in % of the simulations. */
function keyPositions() {
  const all = {}, only = {}, cab = {};
  const howMany = [0, 0, 0, 0, 0];                 // simulations with 0, 1, 2, 3, 4+ parties in a key position
  const add = (o, k) => { o[k] = (o[k] || 0) + 1; };
  SIM.coalition.forEach((c, i) => {
    const opts = [c, ...(SIM.options?.[i] || []).filter((o) => o >= 0)].map((o) => SIM.coalitions[o]);
    const key = (p) => (p === "GL/PvdA" ? "PRO" : p);
    opts[0].forEach((p) => {
      if (p === NO_CABINET) return;
      add(cab, key(p));
      if (opts.length > 1 && opts.every((o) => o.includes(p))) add(all, key(p));
    });
    const kings = opts.length > 1 ? opts[0].filter((p) => p !== NO_CABINET && opts.every((o) => o.includes(p))) : [];
    howMany[Math.min(kings.length, 4)]++;
    if (kings.length === 1) add(only, key(kings[0]));
  });
  const pc = (o, p) => (100 * (o[p] || 0)) / SIM.n;
  const rows = Object.keys(cab).filter((p) => p !== "DNA")
    .map((p) => ({ p, all: pc(all, p), only: pc(only, p), cab: pc(cab, p) }))
    .sort((a, b) => b.all - a.all || b.only - a.only);
  rows.howMany = howMany.map((v) => (100 * v) / SIM.n);   // % of the simulations with 0, 1, 2, 3, 4+ key parties
  return rows;
}

function coalitionEl(parties) {
  const list = Array.isArray(parties) ? parties : parties.split(", ");
  const el = h("span", { class: "coalition" });
  list.forEach((p, i) => { if (i) el.append(h("span", { class: "sep" }, " · ")); el.append(p); });
  return el;
}

function card(...children) { return h("div", { class: "card" }, ...children); }
function section(title, intro, ...children) {
  return h("section", { class: "section" },
    title && h("h2", {}, title),
    intro && (typeof intro === "string" ? h("p", {}, intro) : intro),
    ...children);
}

/* stable colors: a party keeps its slot while it stays selected */
function colorFor(key, selection) {
  const slots = state._colors || (state._colors = {});
  const map = slots[selection.id] || (slots[selection.id] = {});
  for (const k of Object.keys(map)) if (!selection.values.includes(k)) delete map[k];
  if (!(key in map)) {
    const used = new Set(Object.values(map));
    map[key] = SERIES.findIndex((_, i) => !used.has(i));
    if (map[key] < 0) map[key] = 0;
  }
  return css(SERIES[map[key]]);
}

/* ---------- controls ---------- */

function multiSelect({ id, options, values, max = 8, onChange, placeholder = "Partij toevoegen" }) {
  const sel = { id, values };
  const wrap = h("div", { class: "multi" });
  function draw() {
    wrap.replaceChildren();
    values.forEach((v) => {
      wrap.append(h("span", { class: "chip" },
        h("span", { class: "dot", style: `background:${colorFor(v, sel)}` }), v,
        h("button", { type: "button", "aria-label": `${v} verwijderen`, onclick: () => {
          values.splice(values.indexOf(v), 1); draw(); onChange(values);
        } }, "×")));
    });
    if (values.length < max) {
      const s = h("select", { id: `${id}-add`, "aria-label": placeholder },
        h("option", { value: "" }, `+ ${placeholder}`),
        options.filter((o) => !values.includes(o)).map((o) => h("option", { value: o }, o)));
      s.addEventListener("change", () => { if (s.value) { values.push(s.value); draw(); onChange(values); } });
      wrap.append(s);
    }
  }
  draw();
  return { el: wrap, sel };
}

function segmented(id, options, value, onChange) {
  const el = h("div", { class: "segmented", role: "group", id });
  options.forEach((o) => el.append(h("button", {
    type: "button", "aria-pressed": String(o === value),
    onclick: () => { el.querySelectorAll("button").forEach((b) => b.setAttribute("aria-pressed", String(b.textContent === o))); onChange(o); },
  }, o)));
  return el;
}

function toggleButton(labelOn, labelOff, get, set) {
  const b = h("button", { type: "button", class: "btn" }, get() ? labelOn : labelOff);
  b.addEventListener("click", () => { set(!get()); });
  return b;
}

/* ---------- tooltip ---------- */

const tip = h("div", { class: "tooltip", hidden: true });
document.body.append(tip);
function showTip(e, head, rows) {
  tip.replaceChildren(h("div", { class: "t-head" }, head),
    ...rows.map((r) => h("div", { class: "t-row" },
      h("span", {}, r.color && h("i", { style: `background:${r.color}` }), r.label), h("b", {}, r.value))));
  tip.hidden = false;
  const pad = 14, w = tip.offsetWidth, ht = tip.offsetHeight;
  let x = e.clientX + pad, y = e.clientY + pad;
  if (x + w > innerWidth - 8) x = e.clientX - w - pad;
  if (y + ht > innerHeight - 8) y = e.clientY - ht - pad;
  tip.style.left = `${Math.max(8, x)}px`; tip.style.top = `${Math.max(8, y)}px`;
}
const hideTip = () => { tip.hidden = true; };

/* ---------- charts (plain SVG) ---------- */

const SVGNS = "http://www.w3.org/2000/svg";
function s(tag, attrs = {}, text) {
  const el = document.createElementNS(SVGNS, tag);
  for (const [k, v] of Object.entries(attrs)) if (v != null) el.setAttribute(k, v);
  if (text != null) el.textContent = text;
  return el;
}
function niceMax(v) {
  if (v <= 0) return 1;
  const p = Math.pow(10, Math.floor(Math.log10(v)));
  for (const m of [1, 1.2, 1.5, 2, 2.5, 3, 4, 5, 6, 8, 10]) if (m * p >= v) return m * p;
  return 10 * p;
}
function niceStep(raw) {
  if (!(raw > 0)) return 1;
  const p = Math.pow(10, Math.floor(Math.log10(raw)));
  for (const m of [1, 2, 2.5, 5, 10]) if (m * p >= raw) return m * p;
  return 10 * p;
}
function chartWidth(el) { return Math.max(280, Math.floor(el.clientWidth || el.parentElement?.clientWidth || 600)); }

/* Horizontal bars: items [{label, value, color?}] */
function hbar(items, { format = (v) => pct(v), max, labelWidth, title } = {}) {
  const el = h("div", { class: "chart", role: "img", "aria-label": title || "staafdiagram" });
  const draw = () => {
    const W = chartWidth(el), row = 28, gap = 6;
    const lw = labelWidth || Math.min(150, 14 + 7.5 * Math.max(...items.map((i) => i.label.length), 3));
    const valW = 64, Hh = items.length * row;
    const top = max ?? niceMax(Math.max(...items.map((i) => i.value), 0));
    const x = (v) => lw + (Math.max(0, v) / top) * (W - lw - valW);
    const svg = s("svg", { viewBox: `0 0 ${W} ${Hh}`, width: W, height: Hh });
    items.forEach((it, i) => {
      const y = i * row;
      const g = s("g");
      g.append(s("text", { x: lw - 10, y: y + row / 2 + 4, "text-anchor": "end", class: "lbl" }, it.label));
      const bw = Math.max(it.value > 0 ? 2 : 0, x(it.value) - lw);
      g.append(s("rect", { x: lw, y: y + gap / 2 + 3, width: bw, height: row - gap - 6, rx: 4, fill: it.color || css("--accent") }));
      g.append(s("text", { x: lw + bw + 8, y: y + row / 2 + 4, class: "val" }, format(it.value)));
      g.append(s("rect", { x: 0, y, width: W, height: row, fill: "transparent" }));
      g.addEventListener("mousemove", (e) => showTip(e, it.label, [{ label: it.tipLabel || "Waarde", value: format(it.value) }]));
      g.addEventListener("mouseleave", hideTip);
      svg.append(g);
    });
    svg.append(s("line", { x1: lw, x2: lw, y1: 0, y2: Hh, class: "axis" }));
    el.replaceChildren(svg);
  };
  el._draw = draw;
  return el;
}

/* Diverging horizontal bars around zero (percentage points) */
function divbar(items, { format = (v) => `${v > 0 ? "+" : ""}${nl(v)} pp`, title } = {}) {
  const el = h("div", { class: "chart", role: "img", "aria-label": title || "verschil" });
  const draw = () => {
    const W = chartWidth(el), row = 28, lw = 80, valW = 70;
    const m = niceMax(Math.max(...items.map((i) => Math.abs(i.value)), 0.1));
    const mid = lw + valW + (W - lw - 2 * valW) / 2, half = (W - lw - 2 * valW) / 2;
    const Hh = items.length * row;
    const svg = s("svg", { viewBox: `0 0 ${W} ${Hh}`, width: W, height: Hh });
    items.forEach((it, i) => {
      const y = i * row, w = (Math.abs(it.value) / m) * half;
      const g = s("g");
      g.append(s("text", { x: lw - 10, y: y + row / 2 + 4, "text-anchor": "end", class: "lbl" }, it.label));
      const xs = it.value >= 0 ? mid : mid - w;
      if (w > 0) g.append(s("rect", { x: xs, y: y + 6, width: Math.max(2, w), height: row - 12, rx: 4, fill: css(it.value >= 0 ? "--pos" : "--neg") }));
      const tx = it.value >= 0 ? mid + w + 8 : mid - w - 8;
      g.append(s("text", { x: tx, y: y + row / 2 + 4, "text-anchor": it.value >= 0 ? "start" : "end", class: "val" }, format(it.value)));
      g.append(s("rect", { x: 0, y, width: W, height: row, fill: "transparent" }));
      g.addEventListener("mousemove", (e) => showTip(e, it.label, [{ label: "Verandering", value: format(it.value) }]));
      g.addEventListener("mouseleave", hideTip);
      svg.append(g);
    });
    svg.append(s("line", { x1: mid, x2: mid, y1: 0, y2: Hh, class: "axis" }));
    el.replaceChildren(svg);
  };
  el._draw = draw;
  return el;
}

/* Line chart: x = dates (yyyy-mm-dd) or numbers; series [{name, values, color}] */
function lineChart({ x, series, yFormat = (v) => nl(v, 0), tipFormat, yMax, yMin = 0, height = 280, xNumeric = false, title, marker, events = [] }) {
  const wrap = h("div", { class: "section" });
  const legend = h("div", { class: "legend" });
  const el = h("div", { class: "chart", role: "img", "aria-label": title || "lijngrafiek" });
  if (series.length > 1) {
    series.forEach((sr) => legend.append(h("span", {}, h("i", { style: `background:${sr.color}` }), sr.name)));
    wrap.append(legend);
  }
  wrap.append(el);
  tipFormat = tipFormat || yFormat;
  const draw = () => {
    if (!series.length) { el.replaceChildren(h("div", { class: "empty" }, "Kies hierboven een of meer opties.")); return; }
    const W = chartWidth(el), H = height;
    const direct = series.length <= 4 && W > 520;
    const m = { l: 44, r: direct ? 110 : 16, t: 10, b: 28 };
    const xs = x.map((d) => (xNumeric ? d : Date.parse(d)));
    const x0 = Math.min(...xs), x1 = Math.max(...xs);
    const all = series.flatMap((sr) => sr.values.filter((v) => v != null));
    const bottom = yMin;
    const step = yMax != null ? (yMax - bottom) / 4 : niceStep((Math.max(...all, 0) - bottom) / 4);
    const top = yMax ?? bottom + step * Math.max(1, Math.ceil((Math.max(...all, 0) - bottom) / step));
    const nTicks = Math.round((top - bottom) / step);
    const X = (v) => m.l + (x1 === x0 ? (W - m.l - m.r) / 2 : ((v - x0) / (x1 - x0)) * (W - m.l - m.r));
    const Y = (v) => m.t + (1 - (v - bottom) / (top - bottom)) * (H - m.t - m.b);
    const svg = s("svg", { viewBox: `0 0 ${W} ${H}`, width: W, height: H });
    for (let i = 0; i <= nTicks; i++) {
      const v = bottom + step * i, y = Y(v);
      svg.append(s("line", { x1: m.l, x2: W - m.r, y1: y, y2: y, class: i === 0 ? "axis" : "grid" }));
      svg.append(s("text", { x: m.l - 8, y: y + 4, "text-anchor": "end" }, yFormat(v)));
    }
    // x ticks
    const nT = Math.max(2, Math.min(6, Math.floor((W - m.l - m.r) / 90)));
    if (xNumeric) {
      const st = niceStep((x1 - x0) / (nT - 1));
      for (let v = Math.ceil(x0 / st) * st; v <= x1 + 1e-9; v += st)
        svg.append(s("text", { x: X(v), y: H - 8, "text-anchor": "middle" }, nl(v, 0)));
    }
    let last = -Infinity;
    for (let i = 0; i < (xNumeric ? 0 : nT); i++) {
      const v = x0 + ((x1 - x0) * i) / (nT - 1 || 1);
      const label = xNumeric ? nl(v, 0) : fmtDate(new Date(v).toISOString().slice(0, 10));
      if (label === last) continue;
      last = label;
      svg.append(s("text", { x: X(v), y: H - 8, "text-anchor": i === 0 ? "start" : i === nT - 1 ? "end" : "middle" }, label));
    }
    let lastEv = -Infinity;
    events.forEach((ev) => {   // vertical lines, e.g. election days; labels only where they fit
      const ex = X(Date.parse(ev.date));
      svg.append(s("line", { x1: ex, x2: ex, y1: m.t, y2: H - m.b, class: "grid", "stroke-dasharray": "3 4" }));
      if (ex - lastEv < 34) return;
      svg.append(s("text", { x: ex + 4, y: m.t + 10, class: "lbl", "font-size": 10 }, ev.label));
      lastEv = ex;
    });
    const showDots = marker ?? x.length <= 40;
    const ends = [];
    series.forEach((sr) => {
      let d = "", pen = false;
      sr.values.forEach((v, i) => {
        if (v == null) { pen = false; return; }
        d += `${pen ? "L" : "M"}${X(xs[i]).toFixed(1)},${Y(v).toFixed(1)}`; pen = true;
      });
      svg.append(s("path", { d, fill: "none", stroke: sr.color, "stroke-width": 2, "stroke-linejoin": "round", "stroke-linecap": "round" }));
      if (showDots) sr.values.forEach((v, i) => {
        if (v != null) svg.append(s("circle", { cx: X(xs[i]), cy: Y(v), r: 3.5, fill: sr.color, stroke: css("--surface"), "stroke-width": 1.5 }));
      });
      const li = sr.values.map((v, i) => (v == null ? -1 : i)).filter((i) => i >= 0).pop();
      if (li != null) ends.push({ y: Y(sr.values[li]), x: X(xs[li]), sr, v: sr.values[li] });
    });
    if (direct) {
      ends.sort((a, b) => a.y - b.y);
      for (let i = 1; i < ends.length; i++) if (ends[i].y - ends[i - 1].y < 14) ends[i].y = ends[i - 1].y + 14;
      ends.forEach((e) => svg.append(s("text", { x: W - m.r + 8, y: e.y + 4, class: "lbl" }, e.sr.name.length > 14 ? e.sr.name.slice(0, 13) + "…" : e.sr.name)));
    }
    const cross = s("line", { y1: m.t, y2: H - m.b, class: "crosshair", visibility: "hidden" });
    svg.append(cross);
    const hit = s("rect", { x: m.l, y: m.t, width: Math.max(1, W - m.l - m.r), height: H - m.t - m.b, fill: "transparent" });
    hit.addEventListener("mousemove", (e) => {
      const r = svg.getBoundingClientRect(), px = ((e.clientX - r.left) / r.width) * W;
      let bi = 0, bd = Infinity;
      xs.forEach((v, i) => { const dd = Math.abs(X(v) - px); if (dd < bd) { bd = dd; bi = i; } });
      cross.setAttribute("x1", X(xs[bi])); cross.setAttribute("x2", X(xs[bi])); cross.setAttribute("visibility", "visible");
      const rows = series.map((sr) => ({ label: sr.name, value: tipFormat(sr.values[bi]), color: sr.color, v: sr.values[bi] ?? -Infinity }))
        .sort((a, b) => b.v - a.v);
      showTip(e, xNumeric ? nl(x[bi], 0) : fmtDate(x[bi], true), rows);
    });
    hit.addEventListener("mouseleave", () => { cross.setAttribute("visibility", "hidden"); hideTip(); });
    svg.append(hit);
    el.replaceChildren(svg);
  };
  el._draw = draw;
  return wrap;
}

function drawCharts(root) { root.querySelectorAll(".chart").forEach((c) => c._draw && c._draw()); }

/* ---------- simulation helpers ---------- */

function buildSim() {
  const sm = DATA.sims;
  const sets = sm.coalitions.map((c) => new Set(c));
  const parties = Object.keys(sm.seats);
  return { ...sm, sets, parties, all: [...Array(sm.n).keys()] };
}

/* coalitions table over a subset of simulations */
function coalitionRows(ids, base = SIM.n) {
  const groups = new Map();
  for (const i of ids) {
    const key = `${SIM.coalition[i]}|${SIM.majority[i]}`;
    let g = groups.get(key);
    if (!g) groups.set(key, (g = { c: SIM.coalition[i], majority: SIM.majority[i], n: 0, diff: new Array(6).fill(0), seats: 0 }));
    g.n++; g.diff[SIM.difficulty[i]]++;
    g.seats += sum(SIM.coalitions[SIM.coalition[i]].map((p) => SIM.seats[p]?.[i] ?? 0));
  }
  return [...groups.values()].map((g) => ({
    parties: SIM.coalitions[g.c], majority: !!g.majority,
    pct: (g.n / ids.length) * 100, basePct: (g.n / base) * 100,
    difficulty: g.diff.indexOf(Math.max(...g.diff)), seats: g.seats / g.n,
  })).sort((a, b) => b.pct - a.pct);
}

function inCabinet(ids, parties) {
  const out = {};
  for (const p of parties) out[p] = 0;
  for (const i of ids) for (const p of SIM.coalitions[SIM.coalition[i]]) if (p in out) out[p]++;
  for (const p of parties) out[p] = ids.length ? (out[p] / ids.length) * 100 : 0;
  return out;
}

function closeCounts(ids) {
  const c = new Array(SIM.closeNames.length).fill(0);
  for (const i of ids) c[SIM.close[i]]++;
  return SIM.closeNames.map((name, k) => ({ label: name, value: ids.length ? (c[k] / ids.length) * 100 : 0 }))
    .filter((d) => d.value > 0).sort((a, b) => b.value - a.value);
}

function coalitionTable(rows, { limit, base = false } = {}) {
  const shown = limit ? rows.slice(0, limit) : rows;
  const maxP = Math.max(...rows.map((r) => r.pct), 1);
  return h("div", { class: "table-wrap" }, h("table", {},
    h("thead", {}, h("tr", {},
      h("th", {}, "Coalitie"), h("th", { class: "num" }, base ? "Kans in scenario" : "Kans"),
      base && h("th", { class: "num" }, "Kans in basismodel"),
      h("th", {}, "Formatie"), h("th", { title: "Gemiddeld aantal zetels van de coalitie in de simulaties waarin deze coalitie gevormd wordt" }, "Gem. zetels bij deze uitkomst (76 = meerderheid)"))),
    h("tbody", {}, shown.map((r) => h("tr", {},
      h("td", {}, isNoCabinet(r.parties) ? h("span", { class: "note", title: "In deze simulaties vond het formatiemodel geen kabinet" }, NO_CABINET) : coalitionEl(r.parties)),
      h("td", { class: "num" }, h("span", { class: "pbar" }, h("i", { style: `width:${(r.pct / maxP) * 60}px` }), pct(r.pct))),
      base && h("td", { class: "num" }, pct(r.basePct)),
      ...(isNoCabinet(r.parties) ? [h("td", {}, "–"), h("td", {}, "–")] : [
      h("td", {}, h("span", { class: "sev" }, h("i", { style: `background:var(${DIFF_COLOR[r.difficulty]})` }), DIFFICULTY[r.difficulty])),
      h("td", {}, h("span", { style: "display:flex;align-items:center;gap:10px" },
        h("span", { class: "seatbar", title: `gemiddeld ${nl(r.seats, 0)} zetels in de simulaties met deze coalitie` },
          h("i", { style: `width:${Math.min(100, (r.seats / 150) * 100)}%` }), h("b", { style: "left:50.6%" })),
        h("span", { class: "note" }, nl(r.seats, 0))))]))))));
}

/* ---------- pages ---------- */

function pageOverzicht() {
  const st = state.overzicht || (state.overzicht = { showAll: false, include: ["PVV", "VVD"], exclude: ["D66"], showComb: false, showExcl: false });
  const rows = coalitionRows(SIM.all);
  const topRow = rows.find((r) => !isNoCabinet(r.parties)) || rows[0];   // the favourite is a real cabinet
  const majorityShare = (sum(SIM.majority) / SIM.n) * 100;
  const out = [];

  out.push(h("div", { class: "page-head" },
    h("span", { class: "eyebrow" }, "Coalitieverwachtingen"),
    h("h1", {}, "Inzicht in de politieke toekomst"),
    h("p", {}, "Peilingen laten zien hoeveel zetels partijen krijgen, maar in Nederland regeert een partij nooit alleen. Dit model simuleert duizenden verkiezingsuitslagen en formaties, en laat zien welke coalities waarschijnlijk zijn en wat dat betekent voor de tevredenheid van partijen en hun kiezers.")));

  out.push(h("div", { class: "hero card" },
    h("div", { class: "hero-main" },
      h("span", { class: "eyebrow" }, "Meest waarschijnlijke coalitie"),
      h("div", { class: "hero-figure" }, nl(topRow.pct, 1), h("small", {}, "%")),
      h("div", { class: "chips" }, topRow.parties.map((p) => h("span", { class: "chip" }, p))),
      h("p", { class: "note" }, `${topRow.majority ? "Met meerderheid" : "Zonder meerderheid"} · formatie ${DIFFICULTY[topRow.difficulty].toLowerCase()} · gemiddeld ${nl(topRow.seats, 0)} zetels als deze coalitie er komt`)),
    h("div", { class: "stats" },
      h("div", { class: "stat" }, h("b", {}, nl(SIM.n, 0)), h("span", {}, "gesimuleerde verkiezingen")),
      h("div", { class: "stat" }, h("b", {}, pct(majorityShare, 0)), h("span", {}, "van de formaties haalt 76 zetels")),
      h("div", { class: "stat" }, h("b", {}, nl(rows.length, 0)), h("span", {}, "verschillende uitkomsten")),
      h("div", { class: "stat" }, h("b", {}, fmtDate(parseDMY(DATA.lastPoll), true)), h("span", {}, "laatste peiling")))));

  const latest = visiblePosts().slice(0, 3);
  if (latest.length) out.push(section("Laatste nieuws", null, h("div", { class: "post-list compact" }, latest.map(postCard))));

  // coalitions table
  const tableBox = h("div");
  const drawTable = () => tableBox.replaceChildren(coalitionTable(rows, { limit: st.showAll ? 0 : 5 }));
  drawTable();
  out.push(section("Vaakst voorkomende coalities", null, card(tableBox,
    h("div", { class: "controls" }, toggleButton("Toon top 5", `Toon alle ${rows.length} uitkomsten`, () => st.showAll, (v) => { st.showAll = v; render(); })))));

  // difficulty + cabinet size
  const diff = DIFFICULTY.map((d, k) => ({ label: d, value: (SIM.difficulty.filter((x) => x === k).length / SIM.n) * 100, color: css(DIFF_COLOR[k]) }));
  const sizes = {};
  SIM.coalition.forEach((c) => { const n = SIM.coalitions[c].length; if (n !== 18) sizes[n] = (sizes[n] || 0) + 1; });
  const totalSizes = sum(Object.values(sizes));
  const sizeItems = Object.keys(sizes).map(Number).sort((a, b) => a - b)
    .map((n) => ({ label: `${n} ${n === 1 ? "partij" : "partijen"}`, value: (sizes[n] / totalSizes) * 100 }));
  out.push(h("div", { class: "grid-2" },
    section("Hoe moeilijk wordt de formatie?", "Gebaseerd op hoe ver de standpunten van de coalitiepartijen uit elkaar liggen, en op uitspraken over wie niet met wie wil.", card(hbar(diff, { labelWidth: 150, title: "Moeilijkheid formatie" }))),
    section("Hoe groot wordt het kabinet?", "Kans op het aantal partijen in de coalitie.", card(hbar(sizeItems, { labelWidth: 90, title: "Grootte kabinet" })))));

  // individual + biggest party
  const indiv = inCabinet(SIM.all, SIM.parties);
  const indivItems = Object.entries(indiv).filter(([, v]) => v > 0.05).sort((a, b) => b[1] - a[1]).map(([label, value]) => ({ label, value }));
  const groot = Object.entries(DATA.grootste).filter(([, v]) => v > 0).sort((a, b) => b[1] - a[1]).map(([label, value]) => ({ label, value }));
  out.push(h("div", { class: "grid-2" },
    section("Kans op regeringsdeelname", "Per partij: in hoeveel procent van de simulaties zit de partij in het kabinet.", card(hbar(indivItems, { max: 100, title: "Kans op regeringsdeelname" }))),
    section("Grootste partij in de coalitie", "Een goede maatstaf voor wie de premier levert, al zijn er uitzonderingen zoals kabinet-Schoof.", card(hbar(groot, { max: 100, title: "Grootste coalitiepartij" })))));

  // combined chances
  const parties = DATA.factor.parties;
  const combBox = h("div"), exclBox = h("div");
  function comboRows() {
    const inc = st.include, exc = st.exclude.filter((p) => !inc.includes(p));
    const keys = DATA.combinations.filter((k) => inc.every((p) => k.includes(p)) && !exc.some((p) => k.includes(p)));
    const calc = (k, excl) => {
      let n = 0;
      for (let i = 0; i < SIM.n; i++) {
        const set = SIM.sets[SIM.coalition[i]];
        if (k.every((p) => set.has(p)) && !excl.some((p) => set.has(p))) n++;
      }
      return (n / SIM.n) * 100;
    };
    const a = keys.map((k) => ({ k, v: calc(k, []) })).filter((r) => r.v > 0).sort((x, y) => y.v - x.v);
    const b = keys.map((k) => ({ k, v: calc(k, exc) })).filter((r) => r.v > 0).sort((x, y) => y.v - x.v);
    return { a, b, exc };
  }
  const simpleTable = (list, head, limit) => h("div", { class: "table-wrap" }, h("table", {},
    h("thead", {}, h("tr", {}, h("th", {}, head), h("th", { class: "num" }, "Kans"))),
    h("tbody", {}, (limit ? list.slice(0, limit) : list).map((r) => h("tr", {}, h("td", {}, coalitionEl(r.k)), h("td", { class: "num" }, pct(r.v)))),
      !list.length && h("tr", {}, h("td", { colspan: 2, class: "empty" }, "Geen enkele simulatie voldoet hieraan.")))));
  function drawCombos() {
    const { a, b, exc } = comboRows();
    combBox.replaceChildren(simpleTable(a, "Partijen samen in het kabinet", st.showComb ? 0 : 5),
      a.length > 5 ? toggleButton("Toon top 5", `Toon alle ${a.length}`, () => st.showComb, (v) => { st.showComb = v; drawCombos(); }) : "");
    exclBox.replaceChildren(simpleTable(b, `Samen in het kabinet, zonder ${exc.join(", ") || "–"}`, st.showExcl ? 0 : 5),
      b.length > 5 ? toggleButton("Toon top 5", `Toon alle ${b.length}`, () => st.showExcl, (v) => { st.showExcl = v; drawCombos(); }) : "");
  }
  drawCombos();
  const inc = multiSelect({ id: "comb-inc", options: parties, values: st.include, onChange: drawCombos });
  const exc = multiSelect({ id: "comb-exc", options: parties, values: st.exclude, onChange: drawCombos });
  out.push(section("Gecombineerde kansen", "Kies partijen en zie hoe groot de kans is dat ze samen in het kabinet komen, eventueel zonder bepaalde andere partijen.",
    card(h("div", { class: "controls" }, h("span", { class: "control-label" }, "Samen met"), inc.el), combBox),
    card(h("div", { class: "controls" }, h("span", { class: "control-label" }, "Zonder"), exc.el), exclBox)));

  // who can choose the cabinet (key position)
  const keyAll = keyPositions(), keys = keyAll.filter((r) => r.cab >= 2).slice(0, 10);
  const maxK = Math.max(...keys.map((r) => r.cab), 1);
  out.push(section("Wie kiest het kabinet?",
    "Een partij heeft een sleutelpositie als ze in elke optie zit die de formatie overweegt (de eerste, tweede en zo mogelijk derde keuze): dan kan zij kiezen welk kabinet er komt. De kolom Als enige telt de simulaties waarin zij de enige partij met die positie is.",
    card(h("div", { class: "table-wrap" }, h("table", {},
      h("thead", {}, h("tr", {}, h("th", {}, "Partij"), h("th", { class: "num" }, "Alle opties"),
        h("th", { class: "num" }, "Als enige"), h("th", { class: "num" }, "In kabinet"))),
      h("tbody", {}, keys.map((r) => h("tr", {},
        h("td", {}, h("b", {}, r.p)),
        h("td", { class: "num" }, h("span", { class: "pbar" }, h("i", { style: `width:${(r.all / maxK) * 80}px` }), pct(r.all, 0))),
        h("td", { class: "num" }, pct(r.only, 0)),
        h("td", { class: "num" }, pct(r.cab, 0))))))),
      h("h3", {}, "Hoeveel kingmakers?"),
      (() => {   // vertical bars: share of the simulations with 0, 1, 2, 3, 4+ parties in a key position
        const top = Math.max(...keyAll.howMany, 1);
        return h("div", { class: "vbars", role: "img", "aria-label": "Aantal partijen met sleutelpositie per simulatie: " + keyAll.howMany.map((v, k) => `${k === 4 ? "4 of meer" : k}: ${pct(v, 0)}`).join(", ") },
          ...keyAll.howMany.map((v, k) => h("div", { class: "vbar", title: `${k === 4 ? "4 of meer" : k} ${k === 1 ? "partij" : "partijen"} met sleutelpositie: ${pct(v, 1)} van de simulaties` },
            h("span", { class: "vbar-v" }, pct(v, 0)),
            h("i", { style: `height:${Math.max(2, (v / top) * 120)}px` }),
            h("span", { class: "vbar-k" }, k === 4 ? "4+" : String(k)))));
      })(),
      h("p", { class: "note" }, "Aantal partijen met een sleutelpositie per simulatie (horizontaal) en het deel van de simulaties (verticaal)."),
      h("p", { class: "note" }, `Daarom tellen de kolommen van de tabel niet op tot 100%. Bij 0 is er meestal maar één optie (${pct((100 * SIM.options.filter((o) => o[0] < 0).length) / SIM.n, 0)} van de simulaties).`))));
  return out;
}

function pageDoorDeTijd() {
  const st = state.tijd || (state.tijd = { parties: ["PVV"], coalitions: null, happy: ["PVV"], premier: ["PVV"] });
  const ts = DATA.timeseries;
  const out = [];
  out.push(h("div", { class: "page-head" },
    h("span", { class: "eyebrow" }, "Ontwikkeling"),
    h("h1", {}, "Voorspelling door de tijd"),
    h("p", {}, "Hoe bewegen partijen zich door de tijd in het model? Hier zie je of een partij of visie erop vooruit of achteruit is gegaan.")));

  const box1 = h("div", { class: "grid-2" });
  const draw1 = () => {
    const sel = { id: "tijd-p", values: st.parties };
    box1.replaceChildren(
      card(h("h3", {}, "Regeringskans (%)"), lineChart({ x: ts.individual.dates, series: st.parties.filter((p) => ts.individual.series[p]).map((p) => ({ name: p, values: ts.individual.series[p], color: colorFor(p, sel) })), yMax: 100, yFormat: (v) => `${nl(v, 0)}%`, tipFormat: (v) => pct(v), title: "Regeringskans door de tijd" })),
      card(h("h3", {}, "Zetels in de peilingen"), lineChart({ x: ts.seats.dates, series: st.parties.filter((p) => ts.seats.series[p]).map((p) => ({ name: p, values: ts.seats.series[p], color: colorFor(p, sel) })), tipFormat: (v) => `${nl(v, 1)} zetels`, title: "Zetels door de tijd" })));
    drawCharts(box1);
  };
  const ms1 = multiSelect({ id: "tijd-p", options: Object.keys(ts.individual.series), values: st.parties, onChange: draw1 });
  out.push(section("Regeringskans per partij", "Links de kans dat de partij in het kabinet komt, rechts het gemiddelde aantal zetels in de peilingen. Twee aparte grafieken, zodat elke as één ding meet.",
    h("div", { class: "controls" }, ms1.el), box1));
  queueMicrotask(draw1);

  // coalitions over time
  const cols = Object.keys(ts.coalitions.series);
  if (!st.coalitions) {
    const max = (c) => Math.max(...ts.coalitions.series[c].map((v) => v ?? 0));
    const lastv = (c) => ts.coalitions.series[c].at(-1) ?? 0;
    const top = [...cols].sort((a, b) => max(b) - max(a)).slice(0, 2);
    for (const c of [...cols].sort((a, b) => lastv(b) - lastv(a)).slice(0, 2)) if (!top.includes(c) && top.length < 3) top.push(c);
    st.coalitions = top;
  }
  const box2 = card();
  const draw2 = () => {
    const sel = { id: "tijd-c", values: st.coalitions };
    box2.replaceChildren(lineChart({ x: ts.coalitions.dates, series: st.coalitions.map((c) => ({ name: c, values: ts.coalitions.series[c], color: colorFor(c, sel) })), yFormat: (v) => `${nl(v, 0)}%`, tipFormat: (v) => pct(v), title: "Coalitiekansen door de tijd" }));
    drawCharts(box2);
  };
  const ms2 = multiSelect({ id: "tijd-c", options: cols, values: st.coalitions, max: 6, onChange: draw2, placeholder: "Coalitie toevoegen" });
  out.push(section("Coalitiekansen door de tijd", "De kans dat een specifieke coalitie gevormd wordt.", h("div", { class: "controls" }, ms2.el), box2));
  queueMicrotask(draw2);

  if (ts.happiness) {
    const box3 = card();
    const draw3 = () => {
      const sel = { id: "tijd-h", values: st.happy };
      box3.replaceChildren(lineChart({ x: ts.happiness.dates, series: st.happy.filter((p) => ts.happiness.series[p]).map((p) => ({ name: p, values: ts.happiness.series[p], color: colorFor(p, sel) })), yMin: 0, yMax: 100, yFormat: (v) => nl(v, 0), tipFormat: (v) => nl(v, 1), title: "Partijtevredenheid" }));
      drawCharts(box3);
    };
    const ms3 = multiSelect({ id: "tijd-h", options: Object.keys(ts.happiness.series), values: st.happy, onChange: draw3 });
    out.push(section("Partijtevredenheid bij nieuwe verkiezingen", "De verwachte tevredenheid (0–100) als het kabinet op dat moment zou vallen en er verkiezingen kwamen met de peilingen van toen. Per coalitie is de tevredenheid van een partij bepaald door hoe dicht de gemiddelde standpunten van de coalitie bij die van de partij liggen.",
      h("div", { class: "controls" }, ms3.el), box3));
    queueMicrotask(draw3);
  }

  const box4 = card();
  const draw4 = () => {
    const sel = { id: "tijd-g", values: st.premier };
    box4.replaceChildren(lineChart({ x: ts.grootste.dates, series: st.premier.filter((p) => ts.grootste.series[p]).map((p) => ({ name: p, values: ts.grootste.series[p], color: colorFor(p, sel) })), yMax: 100, yFormat: (v) => `${nl(v, 0)}%`, tipFormat: (v) => pct(v), title: "Premierkans" }));
    drawCharts(box4);
  };
  const ms4 = multiSelect({ id: "tijd-g", options: Object.keys(ts.grootste.series), values: st.premier, onChange: draw4 });
  out.push(section("Grootste coalitiepartij", "De kans dat een partij de grootste in de coalitie is: een goede maatstaf voor wie de premier levert.", h("div", { class: "controls" }, ms4.el), box4));
  queueMicrotask(draw4);
  return out;
}

function expectedHappiness(closeItems) {
  // expected[col] = sum over parties of factor[part][col] * pct(part)
  const f = DATA.factor, out = {};
  f.parties.forEach((col, j) => {
    out[col] = sum(closeItems.map((c) => (f.rows[c.label] ? f.rows[c.label][j] * c.value : 0)));
  });
  return out;
}

function pageBeleid() {
  const st = state.beleid || (state.beleid = { party: "PVV" });
  const close = closeCounts(SIM.all);
  const exp = expectedHappiness(close);
  const expItems = Object.entries(exp).sort((a, b) => b[1] - a[1]).map(([label, value]) => ({ label, value }));
  const best = expItems[0];
  const out = [];
  out.push(h("div", { class: "page-head" },
    h("span", { class: "eyebrow" }, "Beleid"),
    h("h1", {}, "Welke partij krijgt zijn zin?"),
    h("p", {}, "Wie er in het kabinet zit is belangrijk, maar wat voor beleid het kabinet voert misschien nog meer. Soms zien partijen hun beleid uitgevoerd zonder zelf in het kabinet te zitten.")));
  out.push(h("div", { class: "grid-2" },
    section("Op wiens beleid lijkt het kabinet?", "Op welke partij het verwachte kabinetsbeleid na verkiezingen het meest lijkt. DNA staat voor een uitkomst waarin geen partij duidelijk het beleid bepaalt.", card(hbar(close, { max: 100, title: "Beleid lijkt het meest op" }))),
    section("Verwachte tevredenheid per partij", `Hoe dicht het verwachte beleid bij de eigen standpunten ligt (100 = precies het eigen beleid). ${best.label} heeft nu de beste uitgangspositie, met een verwachte tevredenheid van ${nl(best.value, 0)}.`,
      card(hbar(expItems, { max: 100, format: (v) => nl(v, 0), title: "Verwachte tevredenheid" })))));

  const tableBox = h("div");
  const drawT = () => {
    const j = DATA.factor.parties.indexOf(st.party);
    const rows = Object.entries(DATA.factor.rows).map(([p, vals]) => ({ p, v: vals[j] * 100 })).sort((a, b) => b.v - a.v);
    tableBox.replaceChildren(hbar(rows.map((r) => ({ label: r.p, value: r.v })), { max: 100, format: (v) => nl(v, 0), title: `Tevredenheid ${st.party}` }));
    drawCharts(tableBox);
  };
  const sel = h("select", { id: "beleid-party", "aria-label": "Partij" }, DATA.factor.parties.map((p) => h("option", { value: p, selected: p === st.party }, p)));
  sel.addEventListener("change", () => { st.party = sel.value; drawT(); });
  out.push(section("Tevredenheid tussen partijen", "Per partij: hoe tevreden zou de gekozen partij zijn met het beleid van elke andere partij. Middenpartijen maken andere afwegingen dan partijen aan de flanken, dus vergelijk deze getallen vooral binnen één partij.",
    card(h("div", { class: "controls" }, h("label", { class: "control-label", for: "beleid-party" }, "Partij"), sel), tableBox)));
  queueMicrotask(drawT);
  return out;
}

function pageScenario() {
  const st = state.scenario || (state.scenario = { conditions: [{ parties: ["PVV"], mode: "Minimaal", seats: 30 }] });
  const parties = SIM.parties.filter((p) => SIM.seats[p].some((v) => v > 0));
  const out = [];
  out.push(h("div", { class: "page-head" },
    h("span", { class: "eyebrow" }, "Wat als"),
    h("h1", {}, "Scenario-analyse"),
    h("p", {}, "Stel voorwaarden aan de verkiezingsuitslag, bijvoorbeeld ‘PVV en VVD samen minstens 40 zetels’, en zie hoe dat de kansen op coalities en beleid verandert. Alleen simulaties die aan alle voorwaarden voldoen tellen mee.")));

  const condBox = h("div", { class: "section" });
  const results = h("div", { class: "section" });
  function drawConds() {
    condBox.replaceChildren();
    st.conditions.forEach((c, k) => {
      const ms = multiSelect({ id: `sc-${k}`, options: parties, values: c.parties, onChange: drawResults });
      const out = h("output", { for: `sc-r-${k}` }, c.seats);
      const range = h("input", { type: "range", id: `sc-r-${k}`, min: 0, max: 76, value: c.seats, "aria-label": "Aantal zetels" });
      range.addEventListener("input", () => { c.seats = Number(range.value); out.textContent = c.seats; drawResults(); });
      condBox.append(card(
        h("div", { class: "controls" }, h("span", { class: "control-label" }, `Voorwaarde ${k + 1}`), ms.el,
          k > 0 && h("button", { type: "button", class: "btn", onclick: () => { st.conditions.splice(k, 1); drawConds(); drawResults(); } }, "Verwijderen")),
        h("div", { class: "controls" },
          segmented(`sc-m-${k}`, ["Minimaal", "Precies", "Maximaal"], c.mode, (m) => { c.mode = m; drawResults(); }),
          h("span", { class: "range" }, range, out, h("span", { class: "note" }, "zetels samen")))));
    });
    if (st.conditions.length < 4) condBox.append(h("div", {}, h("button", { type: "button", class: "btn", onclick: () => {
      st.conditions.push({ parties: [["VVD", "GL/PvdA", "D66"][st.conditions.length - 1] || "CDA"], mode: "Minimaal", seats: 10 });
      drawConds(); drawResults();
    } }, "+ Voorwaarde toevoegen")));
  }
  function drawResults() {
    const ids = SIM.all.filter((i) => st.conditions.every((c) => {
      if (!c.parties.length) return true;
      const t = sum(c.parties.map((p) => SIM.seats[p]?.[i] ?? 0));
      return c.mode === "Minimaal" ? t >= c.seats : c.mode === "Maximaal" ? t <= c.seats : t === c.seats;
    }));
    const share = (ids.length / SIM.n) * 100;
    if (!ids.length) {
      results.replaceChildren(h("div", { class: "callout warn" }, "Geen enkele simulatie voldoet aan deze voorwaarden. Maak ze wat ruimer."));
      return;
    }
    const rows = coalitionRows(ids);
    const condInd = inCabinet(ids, SIM.parties), baseInd = inCabinet(SIM.all, SIM.parties);
    const indItems = Object.entries(condInd).filter(([p, v]) => v > 0.05 || baseInd[p] > 0.05).sort((a, b) => b[1] - a[1]);
    const change = indItems.map(([label, v]) => ({ label, value: v - baseInd[label] })).sort((a, b) => b.value - a.value);
    results.replaceChildren(
      h("div", { class: "callout" }, h("b", {}, pct(share)), ` van de ${nl(SIM.n, 0)} simulaties voldoet aan de voorwaarden (${nl(ids.length, 0)} uitslagen).`),
      section("Meest waarschijnlijke coalities in dit scenario", null, card(coalitionTable(rows, { limit: 5, base: true }))),
      h("div", { class: "grid-2" },
        section("Op wiens beleid lijkt het kabinet?", null, card(hbar(closeCounts(ids), { max: 100, title: "Beleid in scenario" }))),
        section("Kans op regeringsdeelname", null, card(hbar(indItems.map(([label, value]) => ({ label, value })), { max: 100, title: "Regeringsdeelname in scenario" })))),
      section("Verandering ten opzichte van het basismodel", "In procentpunten: hoeveel groter of kleiner de kans op regeringsdeelname wordt in dit scenario.", card(divbar(change, { title: "Verandering regeringsdeelname" }))));
    drawCharts(results);
  }
  drawConds();
  out.push(condBox, results);
  queueMicrotask(drawResults);
  return out;
}

function pageHuidigeCoalitie() {
  const cc = DATA.currentCoalition;
  const yn = (b) => h("span", { class: `tag ${b ? "yes" : "no"}` }, b ? "✓ Ja" : "– Nee");
  const table = (rows) => h("div", { class: "table-wrap" }, h("table", {},
    h("thead", {}, h("tr", {}, h("th", {}, "Partij"), h("th", { class: "num" }, "Tevredenheid nu"), h("th", { class: "num" }, "Na verkiezingen"),
      h("th", { class: "num" }, "Zetels nu"), h("th", { class: "num" }, "Zetels verwacht"),
      h("th", {}, "Gelukkiger na verkiezing"), h("th", {}, "Electoraal gewin"), h("th", {}, "Kans op kabinetsval"))),
    h("tbody", {}, rows.map((r) => h("tr", {},
      h("td", { class: "coalition" }, r.party, r.formerly && h("span", { class: "note", style: "display:block;font-weight:400" }, `was ${r.formerly}`)), h("td", { class: "num" }, nl(r.now, 1)), h("td", { class: "num" }, nl(r.expected, 1)),
      h("td", { class: "num" }, r.seatsBefore), h("td", { class: "num" }, nl(r.seatsExpected, 1)),
      h("td", {}, yn(r.happier)), h("td", {}, yn(r.gain)),
      h("td", {}, r.risk ? h("span", { class: "tag risk" }, "▲ Verhoogd") : h("span", { class: "tag no" }, "Normaal")))))));
  const atRisk = [...cc.coalition, ...cc.opposition].filter((r) => r.risk).map((r) => r.party);
  return [
    h("div", { class: "page-head" },
      h("span", { class: "eyebrow" }, "Wie laat het klappen"),
      h("h1", {}, "Huidige coalitie"),
      h("p", {}, "Een strategische partij laat een coalitie pas vallen als ze bij verkiezingen niet alleen zetels kan winnen, maar ook een goede kans heeft op beleid dat dichter bij haar eigen standpunten ligt. Dat moment doet zich voor als beide tegelijk waar zijn.")),
    h("div", { class: atRisk.length ? "callout warn" : "callout" },
      atRisk.length ? `${atRisk.join(" en ")} ${atRisk.length > 1 ? "hebben" : "heeft"} nu zowel electoraal gewin als beter beleid te verwachten bij nieuwe verkiezingen.` : "Op dit moment heeft geen enkele partij zowel electoraal gewin als beter beleid te verwachten bij nieuwe verkiezingen."),
    section("Coalitiepartijen", "Tevredenheid nu en na nieuwe verkiezingen (0–100), en het verwachte aantal zetels.", card(table(cc.coalition))),
    section("Belangrijkste oppositiepartijen", "Dezelfde analyse voor de oppositie.", card(table(cc.opposition))),
  ];
}

function pageEersteKamer() {
  const ek = DATA.eersteKamer;
  const st = state.ek || (state.ek = { showAll: false, sel: null });
  const cols = Object.keys(ek.timeseries.series);
  if (!st.sel) st.sel = cols.includes(ek.current[0]?.coalition) ? [ek.current[0].coalition] : cols.slice(0, 3);
  const tbl = h("div");
  const drawTbl = () => tbl.replaceChildren(h("div", { class: "table-wrap" }, h("table", {},
    h("thead", {}, h("tr", {}, h("th", {}, "Coalitie"), h("th", { class: "num" }, "Kans op meerderheid"))),
    h("tbody", {}, (st.showAll ? ek.current : ek.current.slice(0, 5)).map((r) => h("tr", {},
      h("td", {}, coalitionEl(r.coalition)),
      h("td", { class: "num" }, h("span", { class: "pbar" }, h("i", { style: `width:${r.rate * 0.8}px` }), pct(r.rate)))))))),
    toggleButton("Toon top 5", `Toon alle ${ek.current.length}`, () => st.showAll, (v) => { st.showAll = v; drawTbl(); }));
  drawTbl();
  const box = card();
  const draw = () => {
    const sel = { id: "ek", values: st.sel };
    box.replaceChildren(lineChart({ x: ek.timeseries.dates, series: st.sel.map((c) => ({ name: c, values: ek.timeseries.series[c], color: colorFor(c, sel) })), yMax: 100, yFormat: (v) => `${nl(v, 0)}%`, tipFormat: (v) => pct(v), marker: false, title: "Eerste Kamer door de tijd" }));
    drawCharts(box);
  };
  const ms = multiSelect({ id: "ek", options: cols, values: st.sel, max: 6, onChange: draw, placeholder: "Coalitie toevoegen" });
  queueMicrotask(draw);
  return [
    h("div", { class: "page-head" },
      h("span", { class: "eyebrow" }, "Senaat"),
      h("h1", {}, "Eerste Kamer"),
      h("p", {}, "De kans dat een coalitie, of een coalitie met waarschijnlijke partners, een meerderheid haalt in de Eerste Kamer.")),
    section("Kans op een meerderheid", null, card(tbl)),
    section("Door de tijd", "Kies coalities om hun kans op een meerderheid in de Eerste Kamer over de tijd te zien.", h("div", { class: "controls" }, ms.el), box),
  ];
}

function pageStrategisch() {
  const sd = DATA.strategic;
  const st = state.strat || (state.strat = { floating: false, party: sd.parties[0], several: [] });
  const resBox = h("div");
  function advice() {
    if (st.floating) {
      if (st.several.length < 2) return h("div", { class: "callout" }, "Kies minstens twee partijen waartussen je twijfelt.");
      const sim = sd.similarity, cols = sim.parties;
      const avg = cols.map((_, j) => sum(st.several.map((p) => sim.rows[p]?.[j] ?? 0)) / st.several.length);
      const top = cols[avg.indexOf(Math.max(...avg))];
      return h("div", { class: "callout" }, st.several.includes(top)
        ? `${top} is de beste partij om op te stemmen als je een combinatie wilt van het beleid van de gekozen partijen.`
        : `${top} is de beste partij om op te stemmen. Dat is geen van de gekozen partijen, waarschijnlijk omdat ${top} meer kans heeft een coalitie te vormen of te veranderen, of omdat de gekozen partijen op veel punten ver uit elkaar liggen.`);
    }
    const p = st.party, best = sd.best[p], better = sd.better[p], diff = sd.diff[p] ?? 0;
    const self = `Stemmen op ${p} is de meest efficiënte manier om het beleid van ${p} door te voeren.`;
    if (sd.small.includes(p)) {
      return h("div", { class: "callout" }, better ? `Stemmen op ${best} geeft een hogere verwachte tevredenheid voor een kiezer van ${p}. Omdat ${p} een kleine partij is, is het effect lastig uit te drukken in procenten uitgevoerd beleid.` : self);
    }
    if (better && diff * 100 > 1) return h("div", { class: "callout" }, `Stemmen op ${best} geeft een hogere verwachte tevredenheid voor een kiezer van ${p}: ${nl(diff * 100, 0)}% meer van het gewenste beleid wordt uitgevoerd.`);
    return h("div", { class: "callout" }, self);
  }
  const controls = h("div", { class: "section" });
  function drawControls() {
    const seg = segmented("strat-mode", ["Ik heb een favoriete partij", "Ik twijfel tussen partijen"], st.floating ? "Ik twijfel tussen partijen" : "Ik heb een favoriete partij",
      (v) => { st.floating = v.startsWith("Ik twijfel"); drawControls(); });
    let pick;
    if (st.floating) pick = multiSelect({ id: "strat-multi", options: Object.keys(sd.similarity.rows), values: st.several, onChange: () => resBox.replaceChildren(advice()) }).el;
    else {
      pick = h("select", { id: "strat-party", "aria-label": "Favoriete partij" }, sd.parties.map((p) => h("option", { value: p, selected: p === st.party }, p)));
      pick.addEventListener("change", () => { st.party = pick.value; resBox.replaceChildren(advice()); });
    }
    controls.replaceChildren(h("div", { class: "controls" }, seg), h("div", { class: "controls" },
      h("span", { class: "control-label" }, st.floating ? "Partijen" : "Partij met het beste beleid"), pick));
    resBox.replaceChildren(advice());
  }
  drawControls();
  return [
    h("div", { class: "page-head" },
      h("span", { class: "eyebrow" }, "Stemhulp"),
      h("h1", {}, "Hoe stem je strategisch?"),
      h("p", {}, "Soms helpt een stem op een andere partij het beleid dat je wilt meer dan een stem op je favoriet, bijvoorbeeld omdat die partij een coalitie kan vormen of kantelen.")),
    card(controls, resBox),
    h("p", { class: "note" }, "De efficiëntie van een stem is gemeten als het effect van kleine veranderingen in de zetelverdeling op de verwachte tevredenheid. Tevredenheid is hoe sterk de gemiddelde standpunten van een coalitie lijken op die van je eigen partij."),
    h("div", { class: "callout warn" }, "Strategisch stemmen is een cijfermatige afweging en er is geen garantie dat de keuze goed uitpakt. Het model gebruikt een beperkt aantal standpunten en weegt die niet. Voor mij persoonlijk is deze functie puur informatief en heeft ze geen effect op mijn stemgedrag."),
  ];
}

/* ---------- blocs ---------- */

const BLOC_LIST = [
  { key: "extreemlinks", label: "Extreem links", color: "--s8" },
  { key: "links", label: "Links", color: "--s5" },
  { key: "midden", label: "Midden", color: "--s3" },
  { key: "christen", label: "Christendemocratisch", color: "--s7" },
  { key: "rechts", label: "Rechts", color: "--s1" },
  { key: "populistisch", label: "Populistisch rechts", color: "--s4" },
];
const NO_BLOC = "geen";
// as in data/blokken.csv (the bloc copula of the model), with the older party names; D66 is shown
// in midden here, while the model puts it in links
const DEFAULT_BLOCS = {
  PRO: "links", "GL/PvdA": "links", GL: "links", PvdA: "links", SP: "links", PvdD: "links", Volt: "links", Denk: "links", BIJ1: "links",
  D66: "midden", CDA: "midden", CU: "midden", NSC: "midden", "50PLUS": "midden",
  VVD: "rechts", SGP: "rechts",
  PVV: "populistisch", FvD: "populistisch", JA21: "populistisch", BBB: "populistisch", BVNL: "populistisch", DNA: "populistisch",
  LVF: "populistisch", LPF: "populistisch", TON: "populistisch", VNL: "populistisch", DPK: "populistisch", PVN: "populistisch", EenNL: "populistisch",
};
// second preset: the radical left and the Christian parties as blocs of their own
const SIX_BLOCS = {
  ...DEFAULT_BLOCS,
  SP: "extreemlinks", PvdD: "extreemlinks", BIJ1: "extreemlinks",
  CDA: "christen", CU: "christen", SGP: "christen",
};
const BLOC_PRESETS = { vier: { label: "Vier blokken", map: DEFAULT_BLOCS }, zes: { label: "Zes blokken", map: SIX_BLOCS } };
const BLOC_STORE = "76zetels-blokken";

// stored as { preset, changes }; an older plain { party: bloc } counts as changes to the four blocs
function blocMap() {
  const st = state.blokken || (state.blokken = { period: "alles", map: null });
  if (!st.map) {
    let saved = null;
    try { saved = JSON.parse(localStorage.getItem(BLOC_STORE) || "null"); } catch (e) { saved = null; }
    if (!saved || typeof saved !== "object") saved = {};
    const isNew = typeof saved.preset === "string";
    st.preset = isNew && BLOC_PRESETS[saved.preset] ? saved.preset : "vier";
    const changes = isNew ? saved.changes || {} : saved;
    st.map = { ...BLOC_PRESETS[st.preset].map, ...changes };
  }
  return st.map;
}
function saveBlocMap(map) {
  const preset = state.blokken?.preset || "vier", base = BLOC_PRESETS[preset].map;
  const changes = Object.fromEntries(Object.entries(map).filter(([p, b]) => base[p] !== b));
  try { localStorage.setItem(BLOC_STORE, JSON.stringify({ preset, changes })); } catch (e) { /* private mode: keep it for this visit */ }
}
const blocOfParty = (map, p) => map[p] || NO_BLOC;

// every combination of up to four of the given blocs (in the order of the list)
function blocCombos(keys = BLOC_LIST.map((b) => b.key)) {
  const out = [];
  const walk = (start, cur) => {
    if (cur.length) out.push(cur);
    if (cur.length === 4) return;
    for (let i = start; i < keys.length; i++) walk(i + 1, [...cur, keys[i]]);
  };
  walk(0, []);
  return out;
}

function pageBlokken() {
  const st = state.blokken || (state.blokken = { period: "alles", map: null });
  const map = blocMap();
  const label = (k) => BLOC_LIST.find((b) => b.key === k)?.label || "Geen blok";
  const color = (k) => css(BLOC_LIST.find((b) => b.key === k)?.color || "--muted");
  const out = [h("div", { class: "page-head" },
    h("span", { class: "eyebrow" }, "Blokken"),
    h("h1", {}, "Hoe groot worden de blokken?"),
    h("p", {}, "Partijen gegroepeerd in blokken. Kiezers wisselen vaak binnen een blok, en de verhoudingen tussen de blokken bepalen welke coalities mogelijk zijn. Kies vier blokken (links, midden, rechts en populistisch rechts) of zes blokken (met ook extreem links en christendemocratisch), en deel partijen daarna zelf anders in als je wilt."))];
  // blocs that have parties; empty blocs stay out of the charts and tables
  const activeBlocs = () => BLOC_LIST.filter((b) => Object.values(map).includes(b.key));

  // parties on the page: everyone with seats now, plus the parties of the chosen period
  const simParties = SIM.parties.filter((p) => sum(SIM.seats[p]) / SIM.n >= 0.5);
  const years = Object.keys(HISTORY).sort();
  const periods = ["alles", "huidig", ...[...years].reverse()];
  const periodLabel = (p) => (p === "alles" ? `${years[0]}–nu` : p === "huidig" ? "Nu" : `Tot ${p}`);

  const expectBox = h("div", {}), comboBox = h("div", {}), scenBox = h("div", {}), scenCtl = h("div", {}), timeBox = card(), resultBox = h("div", {}), editor = h("div", { class: "bloc-editor" }), timeEditor = h("div", { class: "bloc-editor" });

  const blocTotals = () => {
    const tot = Object.fromEntries(BLOC_LIST.map((b) => [b.key, new Array(SIM.n).fill(0)]));
    for (const p of SIM.parties) {
      const b = blocOfParty(map, p);
      if (!tot[b]) continue;
      const a = SIM.seats[p], t = tot[b];
      for (let i = 0; i < SIM.n; i++) t[i] += a[i];
    }
    return tot;
  };
  const quant = (arr, q) => { const s2 = Float64Array.from(arr).sort(); return s2[Math.round(q * (s2.length - 1))]; };

  const drawExpect = () => {
    const tot = blocTotals();
    const rows = activeBlocs().map((b) => ({ ...b, lo: quant(tot[b.key], 0.1), mid: quant(tot[b.key], 0.5), hi: quant(tot[b.key], 0.9),
      parties: simParties.filter((p) => map[p] === b.key) }));
    const max = Math.max(80, ...rows.map((r) => r.hi));
    const pos = (v) => `${(v / max) * 100}%`;
    expectBox.replaceChildren(card(...rows.map((r) => h("div", { class: "bloc-row" },
      h("div", { class: "bloc-head" },
        h("span", {}, h("i", { class: "dot", style: `background:${css(r.color)}` }), h("b", {}, r.label),
          h("span", { class: "note" }, r.parties.length ? ` ${r.parties.join(" · ")}` : " (geen partijen)")),
        h("span", { class: "bloc-num" }, h("b", {}, nl(r.mid, 0)), h("span", { class: "note" }, ` ${nl(r.lo, 0)}–${nl(r.hi, 0)}`))),
      h("div", { class: "bloc-range", title: `8 van de 10 simulaties: ${nl(r.lo, 0)} tot ${nl(r.hi, 0)} zetels` },
        h("i", { style: `left:${pos(r.lo)};width:calc(${pos(r.hi)} - ${pos(r.lo)});background:${css(r.color)}` }),
        h("b", { style: `left:calc(${pos(r.mid)} - 2px)` }))))),
      h("p", { class: "note" }, `Middelste uitkomst en de band waarin 8 van de 10 van de ${nl(SIM.n, 0)} simulaties vallen. Partijen zonder blok tellen niet mee.`));
    // chance that a combination of blocs reaches 76
    const act = activeBlocs().map((b) => b.key);
    const all = blocCombos(act).filter((ks) => ks.length < act.length).map((ks) => {
      let hit = 0;
      for (let i = 0; i < SIM.n; i++) if (ks.reduce((t, k) => t + tot[k][i], 0) >= 76) hit++;
      return { ks, v: (100 * hit) / SIM.n, mean: ks.reduce((t, k) => t + sum(tot[k]) / SIM.n, 0) };
    });
    // left out: a bloc alone or three or more blocs below 1%, and combinations that are almost
    // always a majority without one of their blocs
    const sure = all.filter((c) => c.v >= 95).map((c) => c.ks);
    const combos = all
      .filter((c) => !sure.some((k) => k.length < c.ks.length && k.every((x) => c.ks.includes(x))))
      .filter((c) => c.v >= 1 || (c.ks.length === 2 && act.length <= 4))
      .sort((a, b) => a.ks.length - b.ks.length || b.v - a.v || b.mean - a.mean);
    comboBox.replaceChildren(h("div", { class: "table-wrap" }, h("table", {},
      h("thead", {}, h("tr", {}, h("th", {}, "Blokken samen"), h("th", { class: "num" }, "Gem. zetels"), h("th", { class: "num" }, "Kans op 76 of meer"))),
      h("tbody", {}, combos.slice(0, st.allCombos ? combos.length : 15).map((c) => h("tr", {},
        h("td", {}, ...c.ks.flatMap((k, i) => [i ? h("span", { class: "sep" }, " + ") : null, h("span", {}, h("i", { class: "dot", style: `background:${color(k)}` }), label(k))]).filter(Boolean)),
        h("td", { class: "num" }, nl(c.mean, 0)),
        h("td", { class: "num" }, h("span", { class: "pbar" }, h("i", { style: `width:${c.v * 0.6}px` }), pct(c.v, 0)))))))),
      combos.length > 15 ? h("div", { class: "controls" }, h("button", { type: "button", class: "btn",
        onclick: () => { st.allCombos = !st.allCombos; drawExpect(); } }, st.allCombos ? "Minder combinaties" : `Toon alle ${combos.length} combinaties`)) : null);
  };

  /* scenario: a minimum number of seats for one or more blocs; only the simulations that meet
     every minimum count, and the other blocs show how they move with it */
  const scen = st.scenario || (st.scenario = {});
  let scenTmr;
  const drawScenCtl = () => {
    scenCtl.replaceChildren(card(...activeBlocs().map((b) => {
      const v = scen[b.key] || 0;
      const out = h("output", { for: `scen-${b.key}`, class: "scen-out" }, v ? `min. ${v}` : "geen eis");
      const range = h("input", { type: "range", id: `scen-${b.key}`, min: 0, max: 100, value: v, "aria-label": `Minimaal aantal zetels voor ${b.label}` });
      range.addEventListener("input", () => {
        scen[b.key] = Number(range.value); out.textContent = scen[b.key] ? `min. ${scen[b.key]}` : "geen eis";
        clearTimeout(scenTmr); scenTmr = setTimeout(drawScenario, 60);
      });
      return h("div", { class: "scen-pick" }, h("span", {}, h("i", { class: "dot", style: `background:${css(b.color)}` }), b.label), range, out);
    }),
    h("div", { class: "controls" }, h("button", { type: "button", class: "btn", onclick: () => {
      for (const k of Object.keys(scen)) delete scen[k];
      drawScenCtl(); drawScenario();
    } }, "Alles op nul"))));
  };
  const drawScenario = () => {
    const tot = blocTotals(), BL = activeBlocs(), act = BL.map((b) => b.key);
    const conds = act.filter((k) => scen[k] > 0);
    if (!conds.length) {
      scenBox.replaceChildren(h("p", { class: "note" }, "Zet een schuif hoger dan nul om een scenario te maken, bijvoorbeeld populistisch rechts minimaal 50 zetels."));
      return;
    }
    const ids = SIM.all.filter((i) => conds.every((k) => tot[k][i] >= scen[k]));
    const share = (ids.length / SIM.n) * 100;
    const condText = andList(conds.map((k) => `${label(k).toLowerCase()} minimaal ${scen[k]}`));
    if (ids.length < 20) {
      scenBox.replaceChildren(h("div", { class: "callout warn" }, ids.length
        ? `Maar ${ids.length} van de ${nl(SIM.n, 0)} simulaties hebben ${condText} zetels: te weinig om iets over te zeggen. Maak de eisen wat lager.`
        : `Geen enkele simulatie heeft ${condText} zetels. Maak de eisen wat lager.`));
      return;
    }
    const pick = (arr) => ids.map((i) => arr[i]);
    const rows = BL.map((b) => {
      const sc = pick(tot[b.key]);
      return { ...b, lo: quant(sc, 0.1), mid: quant(sc, 0.5), hi: quant(sc, 0.9), mean: sum(sc) / sc.length,
        bLo: quant(tot[b.key], 0.1), bMid: quant(tot[b.key], 0.5), bHi: quant(tot[b.key], 0.9), bMean: sum(tot[b.key]) / SIM.n };
    });
    const max = Math.max(80, ...rows.map((r) => Math.max(r.hi, r.bHi)));
    const pos = (v) => `${(v / max) * 100}%`;
    const delta = (d) => (Math.abs(d) < 0.5 ? "±0" : `${d > 0 ? "+" : "−"}${nl(Math.abs(d), 0)}`);
    // chance on 76 for two blocs together, in the scenario and now
    const maj = (ks, list) => (100 * list.filter((i) => ks.reduce((t, k) => t + tot[k][i], 0) >= 76).length) / list.length;
    const pairs = blocCombos(act).filter((ks) => ks.length === 2)
      .map((ks) => ({ ks, v: maj(ks, ids), base: maj(ks, SIM.all) }))
      .filter((c) => c.v >= 1 || c.base >= 1).sort((a, b) => b.v - a.v);
    const blocsEl = (ks) => ks.flatMap((k, i) => [i ? h("span", { class: "sep" }, " + ") : null, h("span", {}, h("i", { class: "dot", style: `background:${color(k)}` }), label(k))]).filter(Boolean);
    scenBox.replaceChildren(
      h("div", { class: "callout" }, h("b", {}, pct(share)), ` van de ${nl(SIM.n, 0)} simulaties heeft ${condText} zetels (${nl(ids.length, 0)} uitslagen).`),
      card(...rows.map((r) => h("div", { class: "bloc-row" },
        h("div", { class: "bloc-head" },
          h("span", {}, h("i", { class: "dot", style: `background:${css(r.color)}` }), h("b", {}, r.label),
            scen[r.key] ? h("span", { class: "note" }, ` minimaal ${scen[r.key]}`) : null),
          h("span", { class: "bloc-num" }, h("b", {}, nl(r.mid, 0)), h("span", { class: "note" }, ` ${nl(r.lo, 0)}–${nl(r.hi, 0)} · `),
            h("span", { class: `scen-delta ${r.mean - r.bMean >= 0.5 ? "up" : r.mean - r.bMean <= -0.5 ? "down" : ""}`, title: `gemiddeld ${nl(r.mean, 1)} zetels, nu ${nl(r.bMean, 1)}` }, delta(r.mean - r.bMean)))),
        h("div", { class: "bloc-range", title: `scenario: ${nl(r.lo, 0)} tot ${nl(r.hi, 0)} zetels; zonder scenario ${nl(r.bLo, 0)} tot ${nl(r.bHi, 0)}` },
          h("i", { class: "scen-base", style: `left:${pos(r.bLo)};width:calc(${pos(r.bHi)} - ${pos(r.bLo)});background:${css(r.color)}` }),
          h("i", { style: `left:${pos(r.lo)};width:calc(${pos(r.hi)} - ${pos(r.lo)});background:${css(r.color)}` }),
          h("b", { style: `left:calc(${pos(r.mid)} - 2px)` }))))),
      h("p", { class: "note" }, "Middelste uitkomst en de band van 8 van de 10 simulaties binnen het scenario; de lichte band is de verwachting zonder scenario. Het getal achter de punt is de verandering van het gemiddelde aantal zetels."),
      h("div", { class: "grid-2" },
        section("Kans op een meerderheid", "Twee blokken samen 76 of meer zetels, in dit scenario en zonder.",
          h("div", { class: "table-wrap" }, h("table", {},
            h("thead", {}, h("tr", {}, h("th", {}, "Blokken samen"), h("th", { class: "num" }, "Scenario"), h("th", { class: "num" }, "Nu"))),
            h("tbody", {}, pairs.slice(0, 8).map((c) => h("tr", {}, h("td", {}, ...blocsEl(c.ks)),
              h("td", { class: "num" }, h("span", { class: "pbar" }, h("i", { style: `width:${c.v * 0.6}px` }), pct(c.v, 0))),
              h("td", { class: "num note" }, pct(c.base, 0)))))))),
        section("Meest waarschijnlijke coalities", "Welk kabinet het formatiemodel in deze simulaties vormt.",
          h("div", { class: "table-wrap" }, h("table", {},
            h("thead", {}, h("tr", {}, h("th", {}, "Coalitie"), h("th", { class: "num" }, "Kans"))),
            h("tbody", {}, coalitionRows(ids).slice(0, 6).map((r) => h("tr", {},
              h("td", {}, isNoCabinet(r.parties) ? h("span", { class: "note" }, NO_CABINET) : coalitionEl(r.parties),
                r.majority ? null : h("span", { class: "note" }, " minderheid")),
              h("td", { class: "num" }, pct(r.pct, 0))))))))));
  };

  const blocSum = (seats, key) => Object.entries(seats).reduce((t, [p, v]) => t + (v != null && blocOfParty(map, p) === key ? v : 0), 0);
  const blocAt = (src, i, key) => {
    let t = 0, any = false;
    for (const [p, vals] of Object.entries(src.series)) if (blocOfParty(map, p) === key && vals[i] != null) { t += vals[i]; any = true; }
    return any ? t : null;
  };

  // every poll cycle after each other: weekly polls, the result on election day, then the model since 2025;
  // a gap of more than two months in the data breaks the lines
  const drawAll = () => {
    const BL = activeBlocs(), pts = [];
    for (const y of years) {
      const d = HISTORY[y];
      if (d.polls) d.polls.dates.forEach((dt, i) => pts.push({ date: dt, v: BL.map((b) => blocAt(d.polls, i, b.key)) }));
      if (d.result) pts.push({ date: d.result.date, v: BL.map((b) => blocSum(d.result.seats, b.key)) });
    }
    const cur = DATA.timeseries.seats, lastDate = pts.at(-1)?.date || "";
    cur.dates.forEach((dt, i) => { if (dt > lastDate) pts.push({ date: dt, v: BL.map((b) => blocAt(cur, i, b.key)) }); });
    const x = [], vals = BL.map(() => []);
    pts.forEach((pt, i) => {
      if (i && Date.parse(pt.date) - Date.parse(pts[i - 1].date) > 62 * 864e5) { x.push(pt.date); vals.forEach((v) => v.push(null)); }
      x.push(pt.date); pt.v.forEach((v, k) => vals[k].push(v));
    });
    const events = years.filter((y) => HISTORY[y].result).map((y) => ({ date: HISTORY[y].result.date, label: y }));
    timeBox.replaceChildren(lineChart({ x, series: BL.map((b, k) => ({ name: b.label, color: css(b.color), values: vals[k] })),
      tipFormat: (v) => (v == null ? "–" : `${nl(v, 1)} zetels`), title: "Zetels per blok sinds 2006", marker: false, height: 320, events }),
      h("p", { class: "note" }, `Peilingen per week (alle bureaus, gemiddeld over vier weken) vanaf ${fmtDate(pts[0].date, true)}, met op elke verkiezingsdag (stippellijn) de uitslag; sinds de verkiezingen van 2025 het peilingsgemiddelde van het model. Waar de lijnen onderbroken zijn, zitten geen peilingen in onze dataset.`));
    drawCharts(timeBox);
  };

  // seats per bloc at every election, and the expectation now
  const drawResults = () => {
    const tot = blocTotals(), BL = activeBlocs();
    const rows = years.filter((y) => HISTORY[y].result).map((y) => ({ label: fmtDate(HISTORY[y].result.date, true), v: BL.map((b) => blocSum(HISTORY[y].result.seats, b.key)) }));
    rows.push({ label: "Verwachting nu", v: BL.map((b) => quant(tot[b.key], 0.5)), now: true });
    const cell = (v, prev) => h("td", { class: "num" }, h("b", {}, nl(v, 0)),
      prev == null ? null : h("span", { class: "note" }, ` ${v - prev > 0 ? "+" : v - prev < 0 ? "−" : "±"}${nl(Math.abs(v - prev), 0)}`));
    resultBox.replaceChildren(card(h("div", { class: "table-wrap" }, h("table", {},
      h("thead", {}, h("tr", {}, h("th", {}, "Verkiezing"), ...BL.map((b) => h("th", { class: "num" }, h("i", { class: "dot", style: `background:${css(b.color)}` }), b.label)))),
      h("tbody", {}, rows.map((r, i) => h("tr", { class: r.now ? "hit" : "" }, h("td", {}, r.label), ...r.v.map((v, k) => cell(v, i ? rows[i - 1].v[k] : null))))))),
      h("p", { class: "note" }, "Zetels per blok bij elke verkiezing, met de verandering ten opzichte van de verkiezing ervoor. Onderste rij: de middelste uitkomst van de simulaties nu. Je eigen indeling hierboven telt mee.")));
  };

  const drawTime = () => {
    if (st.period === "alles") return drawAll();
    const isNow = st.period === "huidig";
    const src = isNow ? DATA.timeseries.seats : HISTORY[st.period]?.polls;
    if (!src) { timeBox.replaceChildren(h("div", { class: "empty" }, "Voor deze periode zijn geen peilingen beschikbaar.")); return; }
    const x = [...src.dates];
    const BL = activeBlocs();
    const series = BL.map((b) => ({ name: b.label, color: css(b.color),
      values: src.dates.map((_, i) => {
        let t = 0, any = false;
        for (const [p, vals] of Object.entries(src.series)) if (blocOfParty(map, p) === b.key && vals[i] != null) { t += vals[i]; any = true; }
        return any ? t : null;
      }) }));
    const res = !isNow && HISTORY[st.period]?.result;
    if (res) {   // the election result as the last point
      x.push(res.date);
      series.forEach((sr, k) => sr.values.push(Object.entries(res.seats).reduce((t, [p, v]) => t + (blocOfParty(map, p) === BL[k].key ? v : 0), 0)));
    }
    timeBox.replaceChildren(lineChart({ x, series, tipFormat: (v) => `${nl(v, 1)} zetels`, title: "Zetels per blok door de tijd", marker: false }),
      h("p", { class: "note" }, isNow
        ? "Zetels per blok in het peilingsgemiddelde van het model sinds de verkiezingen van 2025."
        : `Peilingen per week (alle bureaus, gemiddeld over vier weken) tot de verkiezingen van ${fmtDate(res?.date || st.period, true)}; het laatste punt is de uitslag.`));
    drawCharts(timeBox);
  };

  // two pickers on the same choice: the parties of now at the top, the parties of the chosen period at the chart
  const order = (list) => [...new Set(list)]
    .sort((a, b) => (BLOC_LIST.findIndex((x) => x.key === map[a]) - BLOC_LIST.findIndex((x) => x.key === map[b])) || a.localeCompare(b));
  const periodParties = () => order([...(st.period === "alles" || st.period === "huidig" ? simParties : []),
    ...(st.period === "huidig" ? [] : (st.period === "alles" ? years : [st.period]).flatMap((y) => [...Object.keys(HISTORY[y]?.polls?.series || {}), ...Object.keys(HISTORY[y]?.result?.seats || {})]))]);
  const timeSummary = h("summary", {});
  const drawEditor = () => {
    fillEditor(editor, order(simParties));
    const parties = periodParties();
    fillEditor(timeEditor, parties);
    timeSummary.textContent = `Partijen in de blokken aanpassen (${parties.length} partijen, ${periodLabel(st.period).toLowerCase()})`;
  };
  const fillEditor = (box, parties) => {
    box.replaceChildren(...parties.map((p) => {
      const sel = h("select", { "aria-label": `Blok van ${p}` },
        ...BLOC_LIST.map((b) => h("option", { value: b.key, selected: map[p] === b.key }, b.label)),
        h("option", { value: NO_BLOC, selected: blocOfParty(map, p) === NO_BLOC }, "Geen blok"));
      sel.addEventListener("change", () => { map[p] = sel.value; saveBlocMap(map); redraw(); });
      return h("label", { class: "bloc-pick" }, h("i", { class: "dot", style: `background:${color(blocOfParty(map, p))}` }), h("span", {}, p), sel);
    }));
  };

  const presetMap = () => BLOC_PRESETS[st.preset || "vier"].map;
  const changed = () => [...new Set([...Object.keys(map), ...Object.keys(presetMap())])].some((p) => presetMap()[p] !== map[p]);
  const usePreset = (key) => {
    st.preset = key;
    for (const k of Object.keys(map)) delete map[k];
    Object.assign(map, BLOC_PRESETS[key].map); saveBlocMap(map); redraw();
  };
  // the same controls at the top and at the chart
  const presetBoxes = [0, 1].map(() => h("div", { class: "controls" }));
  const drawPresets = () => presetBoxes.forEach((box, i) => {
    const reset = h("button", { type: "button", class: "btn" }, `Terug naar ${BLOC_PRESETS[st.preset || "vier"].label.toLowerCase()}`);
    reset.addEventListener("click", () => usePreset(st.preset || "vier"));
    const keys = Object.keys(BLOC_PRESETS);
    box.replaceChildren(h("span", { class: "control-label" }, "Indeling"),
      segmented(`blok-preset-${i}`, keys.map((k) => BLOC_PRESETS[k].label), BLOC_PRESETS[st.preset || "vier"].label,
        (lbl) => usePreset(keys.find((k) => BLOC_PRESETS[k].label === lbl))),
      ...(changed() ? [h("span", { class: "note" }, "aangepast"), reset] : []));
  });
  const redraw = () => { drawPresets(); drawEditor(); drawExpect(); drawScenCtl(); drawScenario(); drawTime(); drawResults(); };

  out.push(section("Indeling", "Kies een indeling en pas daarna per partij het blok aan. Je keuze wordt in deze browser onthouden en geldt voor de hele pagina. Partijen van eerdere verkiezingen deel je in bij de grafiek hieronder.",
    presetBoxes[0], editor));
  out.push(section("Verwachting op verkiezingsdag", null, expectBox));
  out.push(section("Kans op een meerderheid", "Kans dat een combinatie van blokken samen 76 of meer zetels haalt, uit dezelfde simulaties.", comboBox));
  out.push(section("Scenario's", "Wat als een blok groot wordt? Geef per blok een minimum aantal zetels. Alleen de simulaties die aan alle minimums voldoen tellen mee, en je ziet wat dat betekent voor de andere blokken, de meerderheden en de coalities.", scenCtl, scenBox));
  const periodSel = segmented("blok-periode", periods.map(periodLabel), periodLabel(st.period), (lbl) => {
    st.period = periods.find((p) => periodLabel(p) === lbl); drawEditor(); drawTime();
  });
  out.push(section("Blokken door de tijd", `Hoe de blokken in de peilingen bewogen: over de hele periode sinds ${years[0]}, sinds de laatste verkiezingen, of in aanloop naar één eerdere verkiezing.`,
    h("div", { class: "controls" }, periodSel),
    h("details", { class: "card bloc-details" }, timeSummary,
      h("p", { class: "note" }, "Dezelfde indeling als bovenaan, met ook de partijen van eerdere verkiezingen. De grafiek, de tabel hieronder en de verwachting rekenen direct mee."),
      presetBoxes[1], timeEditor),
    timeBox));
  out.push(section("De blokken bij elke verkiezing", null, resultBox));
  queueMicrotask(redraw);
  return out;
}

function pageVorige() {
  const years = Object.keys(HISTORY);
  const st = state.vorige || (state.vorige = { year: years.at(-1), parties: ["PVV"], coalitions: null, happy: ["PVV"], premier: ["PVV"], cyear: null });
  const d = HISTORY[st.year];
  if (st.cyear !== st.year) {
    const cols = Object.keys(d.coalitions.series);
    const lastv = (c) => d.coalitions.series[c].at(-1) ?? 0;
    st.coalitions = [...cols].sort((a, b) => lastv(b) - lastv(a)).slice(0, 3);
    for (const k of ["parties", "happy", "premier"]) {
      const pool = Object.keys((k === "parties" ? d.individual : k === "happy" ? d.happiness || {} : d.grootste).series || {});
      st[k] = st[k].filter((p) => pool.includes(p));
      if (!st[k].length && pool.length) st[k] = [pool.includes("PVV") ? "PVV" : pool.includes("VVD") ? "VVD" : pool[0]];
    }
    st.cyear = st.year;
  }
  const out = [];
  out.push(h("div", { class: "page-head" },
    h("span", { class: "eyebrow" }, "Terugblik"),
    h("h1", {}, "Vorige verkiezingen"),
    h("p", {}, "Hoe ontwikkelden de kansen op coalities zich in aanloop naar eerdere verkiezingen?")));
  const bt = BACKTEST.formation || [];
  out.push(h("div", { class: "controls" }, h("span", { class: "control-label" }, "Verkiezing"), segmented("vorige-year", years, st.year, (y) => { st.year = y; render(); })));
  const btYear = bt.find((b) => String(b.jaar) === String(st.year));
  if (btYear) out.push(backtestYear(btYear));
  out.push(section(`Laatste voorspelling voor ${st.year}`, "De tien meest waarschijnlijke coalities bij de laatste peilingen voor de verkiezingen.",
    card(h("div", { class: "table-wrap" }, h("table", {},
      h("thead", {}, h("tr", {}, h("th", {}, "Coalitie"), h("th", { class: "num" }, "Kans"))),
      h("tbody", {}, d.final.map((r) => h("tr", {}, h("td", {}, coalitionEl(r.coalition)), h("td", { class: "num" }, pct(r.pct))))))))));

  const block = (title, intro, key, ts, opts, max) => {
    const box = card();
    const draw = () => {
      const sel = { id: `v-${key}`, values: st[key] };
      box.replaceChildren(lineChart({ x: ts.dates, series: st[key].filter((p) => ts.series[p]).map((p) => ({ name: p, values: ts.series[p], color: colorFor(p, sel) })), ...opts }));
      drawCharts(box);
    };
    const ms = multiSelect({ id: `v-${key}`, options: Object.keys(ts.series), values: st[key], onChange: draw, max: max || 8, placeholder: key === "coalitions" ? "Coalitie toevoegen" : "Partij toevoegen" });
    queueMicrotask(draw);
    return section(title, intro, h("div", { class: "controls" }, ms.el), box);
  };
  const pctOpts = { yFormat: (v) => `${nl(v, 0)}%`, tipFormat: (v) => pct(v) };
  out.push(block("Regeringskans per partij", "De kans dat de partij in het kabinet komt.", "parties", d.individual, { ...pctOpts, yMax: 100 }));
  out.push(block("Coalitiekansen door de tijd", null, "coalitions", d.coalitions, pctOpts, 6));
  if (d.happiness) out.push(block("Partijtevredenheid", "Verwachte tevredenheid (0–100) als er op dat moment verkiezingen zouden zijn.", "happy", d.happiness, { yMax: 100, yFormat: (v) => nl(v, 0), tipFormat: (v) => nl(v, 1) }));
  out.push(block("Grootste coalitiepartij", null, "premier", d.grootste, { ...pctOpts, yMax: 100 }));
  out.push(h("p", { class: "note" }, "De tijdreeksen van vorige verkiezingen zijn in-sample: het model kende de uitslag al. Er zijn minder simulaties gedraaid dan voor de huidige analyse, en na een modelaanpassing worden deze reeksen niet direct bijgewerkt."));
  if (BACKTEST.calibration) out.push(calibrationSection(BACKTEST.calibration));
  if (BACKTEST.margins) out.push(marginsSection(BACKTEST.margins));
  if (bt.length) out.push(backtestOverview(bt));
  return out;
}

/* 90/95% margins per seat bucket x time to the election */
function marginsSection(m) {
  const cellEl = (c, band) => {
    if (!c) return h("td", { class: "num" }, "–");
    const target = Number(band);
    // too narrow: fewer results inside than the band promises and more margin needed;
    // too wide: clearly more inside and at least a seat less needed
    const narrow = c.pit < target - 1 && c.needed > c.model + 0.4;
    const wide = c.pit > target + 1 && c.needed < c.model - 0.9;
    return h("td", { class: `num margin-cell${narrow ? " narrow" : wide ? " wide" : ""}` },
      h("b", {}, pct(c.pit, 0)), h("div", { class: "note" }, `±${nl(c.model, 1)} → ±${nl(c.needed, 1)}`));
  };
  const tbl = (band) => card(h("h3", {}, `${band}%-band`), h("div", { class: "table-wrap" }, h("table", { class: "margins" },
    h("thead", {}, h("tr", {}, h("th", {}, "Zetels"), ...m.times.map((t) => h("th", { class: "num" }, t.replace(" d", " dagen"))), h("th", { class: "num" }, "Alle"))),
    h("tbody", {}, m.rows.map((r) => h("tr", {}, h("td", {}, r.size, h("div", { class: "note" }, `${nl(r.n, 0)} keer`)),
      ...m.times.map((t) => cellEl(r.cells[t]?.[band], band)), cellEl(r.all[band], band)))))));
  return section("Marges per partijgrootte en tijd tot de verkiezing",
    "Voor 1 tot 120 dagen voor elke verkiezing van 2006 tot en met 2025 is de zetelsimulatie van het huidige model opnieuw gedraaid met alleen de peilingen van dat moment. Per cel: het deel van de uitslagen dat binnen de band viel (eerlijk gemeten, zonder bonus voor de afronding op hele zetels), en daaronder de marge van het model naast de marge die nodig was geweest (in zetels, van de mediaan tot de rand van de band). Rood: te krap, grijs: ruimer dan nodig.",
    tbl("90"), tbl("95"),
    h("p", { class: "note" }, "Veel cellen tellen maar 30 tot 60 gevallen uit zeven verkiezingen; kijk naar patronen over meerdere cellen, niet naar losse getallen."));
}

/* formation model on the real results: one row per election */
function backtestOverview(bt) {
  const hits = bt.filter((b) => b.rang === 1).length;
  const good = sum(bt.map((b) => b.partijen_goed)), total = sum(bt.map((b) => b.partijen_totaal));
  return section("Hoe goed is het formatiemodel?",
    `Het formatiemodel kreeg na elke verkiezing sinds 2006 de echte uitslag en de standpunten van dat jaar, en simuleerde per verkiezing 1.000 formaties. Bij ${hits} van de ${bt.length} verkiezingen was het gevormde kabinet de favoriet van het model. Per partij (wel of niet in het kabinet, bij meer dan 50% kans) zat het model ${good} van de ${total} keer goed.`,
    card(h("div", { class: "table-wrap" }, h("table", {},
      h("thead", {}, h("tr", {}, h("th", {}, "Verkiezing"), h("th", {}, "Gevormd kabinet"), h("th", { class: "num" }, "Kans in model"),
        h("th", { class: "num" }, "Plaats"), h("th", {}, "Favoriet van het model"))),
      h("tbody", {}, bt.map((b) => h("tr", {},
        h("td", {}, String(b.jaar)),
        h("td", {}, coalitionEl(b.coalitie), h("div", { class: "note" }, b.kabinet)),
        h("td", { class: "num" }, pct(b.kans_echte_coalitie, 0)),
        h("td", { class: "num" }, b.rang ? `${b.rang}e` : "–"),
        h("td", {}, b.rang === 1 ? h("span", { class: "note" }, "zelfde") : h("span", {}, coalitionEl(b.favoriet), h("span", { class: "note" }, ` ${pct(b.kans_favoriet, 0)}`))))))))));
}

function backtestYear(b) {
  const actual = [...b.coalitie].sort().join("|");
  const rows = b.top.map((t) => ({ ...t, hit: [...t.coalitie].sort().join("|") === actual }));
  const parties = Object.entries(b.kans_per_partij).filter(([p, v]) => v > 0 || b.coalitie.includes(p));
  return section(`Het formatiemodel met de echte uitslag van ${b.jaar}`,
    `Het gevormde kabinet (${b.kabinet}: ${b.coalitie.join(", ")}, ${b.zetels} zetels) kreeg in het model ${pct(b.kans_echte_coalitie, 0)}${b.rang ? `, plaats ${b.rang}` : ""}. ${b.toelichting}`,
    h("div", { class: "grid-2" },
      card(h("h3", {}, "Meest gevormde coalities"), h("div", { class: "table-wrap" }, h("table", {},
        h("thead", {}, h("tr", {}, h("th", {}, "Coalitie"), h("th", { class: "num" }, "Zetels"), h("th", { class: "num" }, "Kans"))),
        h("tbody", {}, rows.map((t) => h("tr", { class: t.hit ? "hit" : "" },
          h("td", {}, coalitionEl(t.coalitie), t.hit ? h("span", { class: "tag-hit" }, "gevormd") : null),
          h("td", { class: "num" }, String(t.zetels)), h("td", { class: "num" }, pct(t.kans, 0)))))))),
      card(h("h3", {}, "Kans op een plek in het kabinet"), h("div", { class: "table-wrap" }, h("table", {},
        h("thead", {}, h("tr", {}, h("th", {}, "Partij"), h("th", { class: "num" }, "Kans"), h("th", {}, "Echt"))),
        h("tbody", {}, parties.map(([p, v]) => h("tr", {},
          h("td", {}, p), h("td", { class: "num" }, pct(v, 0)), h("td", {}, b.coalitie.includes(p) ? "in kabinet" : "–")))))))));
}

/* calibration of the seat simulation: does the election result fall inside the bands? */
function calibrationSection(c) {
  const p = (v) => pct(v, v > 99 && v < 100 ? 1 : 0);
  const m = (v) => `± ${nl(v, v % 1 ? 1 : 0)}`;
  const tbl = (rows, first) => h("div", { class: "table-wrap" }, h("table", {},
    h("thead", {},
      h("tr", {}, h("th", { rowspan: 2 }, first), h("th", { class: "num", colspan: 3 }, "Uitslag binnen de band"),
        h("th", { class: "num", colspan: 2 }, "Marge 80%-band (zetels)"), h("th", { class: "num", colspan: 2 }, "Marge 80%-band (relatief)")),
      h("tr", {}, ...["50%", "80%", "90%", "model", "nodig", "model", "nodig"].map((t) => h("th", { class: "num" }, t)))),
    h("tbody", {}, rows.map((x) => h("tr", {}, h("td", {}, x.label[0].toUpperCase() + x.label.slice(1), h("div", { class: "note" }, `${nl(x.n, 0)} keer`)),
      h("td", { class: "num" }, p(x.in50)), h("td", { class: "num" }, p(x.in80)), h("td", { class: "num" }, p(x.in90)),
      h("td", { class: "num" }, m(x.margin)), h("td", { class: "num" }, m(x.needed)),
      h("td", { class: "num" }, `${m(x.marginPct)}%`), h("td", { class: "num" }, `${m(x.neededPct)}%`))))));
  const all = c.all[0];
  return section("Hoe goed zijn de zetelmarges?",
    `Het model simuleert de zetels op de verkiezingsdag. Voor elke maand in de aanloop naar de verkiezingen van 2006 tot en met 2025, en 1, 2, 4, 7, 10, 15, 20 en 25 dagen voor elke verkiezing, is die simulatie opnieuw gedraaid met alleen de peilingen van dat moment, en vergeleken met de uitslag (${nl(all.n, 0)} keer een partij). Bij een goed afgestelde simulatie valt de uitslag in 50%, 80% en 90% van de gevallen binnen de 50%-, 80%- en 90%-band; liggen de percentages hoger, dan zijn de marges ruimer dan nodig. De marge is de afstand van de mediaan tot de rand van de 80%-band aan de kant waar de uitslag viel, gemiddeld over de gevallen, in zetels en als percentage van de zetels van de partij op het peilmoment. ‘Nodig’ is de marge die het model had moeten geven: dezelfde marges, zo geschaald dat precies 80% van de uitslagen erbinnen viel.`,
    h("p", { class: "callout" }, "De zetelsimulatie is bewust aan de ruime kant afgesteld: liever een band die iets te breed is dan een die te krap is. Voor de formatie zijn de uitschieters (een eindsprint of een ineenstorting) vaak belangrijker dan de buik van de verdeling, omdat juist zij bepalen welke coalities een meerderheid kunnen halen."),
    card(h("h3", {}, "Per partijgrootte op het peilmoment"), tbl([...c.all, ...c.size], "Partijen")),
    card(h("h3", {}, "Per tijd tot de verkiezing"), tbl(c.horizon, "Peilmoment")),
    h("p", { class: "note" }, "Alleen partijen met minstens één zetel op het peilmoment; nieuwe partijen (zoals NSC in 2023) kan de simulatie niet voorzien. Vergeleken op hele zetels."));
}

function pageOver() {
  const s = DATA.stats;
  const sel = { id: "over-run", values: Object.keys(s.running.series) };
  const steps = s.running.series[sel.values[0]].map((_, i) => (i + 1) * s.running.step);
  const runChart = lineChart({ x: steps, xNumeric: true, series: sel.values.map((c) => ({ name: c, values: s.running.series[c].map((v) => v * 100), color: colorFor(c, sel) })), yFormat: (v) => `${nl(v, 0)}%`, tipFormat: (v) => pct(v), marker: false, title: "Stabiliteit van de simulaties" });
  const conv = s.convergence;
  const one = (name, vals, fmt) => lineChart({ x: conv.steps, xNumeric: true, series: [{ name, values: vals, color: css("--accent") }], yFormat: fmt, marker: false, height: 220, title: name });
  const conc = s.concentration;
  const li = (t) => h("li", {}, t);
  return [
    h("div", { class: "page-head" },
      h("span", { class: "eyebrow" }, "Methode"),
      h("h1", {}, "Over het model")),
    h("div", { class: "prose" },
      h("p", {}, "Op deze website doe ik geen politieke uitingen en ik heb geprobeerd mijn eigen voorkeuren zoveel mogelijk buiten het model te houden. De code van het model is niet openbaar; of je de uitkomsten nuttig vindt, laat ik aan jou over. Opmerkingen over specifieke uitkomsten zijn altijd welkom: het model is nooit af."),
      h("p", {}, "Het model gebruikt vier databronnen: de drie grote peilers (Verian/EenVandaag, Ipsos I&O en Peil.nl) en de meest recente versie van het Kieskompas. Alle bronnen zijn openbaar."),
      h("p", {}, "Begin 2025 is het model één keer aangepast. Het CDA leek bijna nooit met de PVV te willen regeren, maar omdat samenwerking beleidsmatig wel interessant kan zijn, is die harde uitsluiting vervangen: hoe beter de PVV presteert, hoe kleiner de kans dat het CDA de PVV uitsluit.")),
    section("Belangrijke aannames", null, h("div", { class: "prose" }, h("ul", {},
      li("Verkiezingen worden gesimuleerd op basis van historische variantie in verkiezingstijd, de huidige variantie van een partij, de tijd tot de verkiezingen en de grootte van de partijen."),
      li("Hoe partijen samen bewegen is geschat per blok (links, midden, rechts en populistisch) uit peilingen en uitslagen sinds 2006, afhankelijk van de tijd tot de verkiezing. Vlak voor een verkiezing ruilen bijvoorbeeld VVD en de populistische partijen sterk kiezers uit. Binnen een blok vechten partijen die het Kieskompas vergelijkbaar hebben ingevuld om dezelfde kiezer."),
      li("Partijen willen samenwerken met partijen die het Kieskompas vergelijkbaar hebben ingevuld. Alle partijen zijn even kieskeurig, en meer partijen maken een formatie moeilijker. Coalities van meer dan vijf partijen zijn om rekentechnische redenen niet mogelijk."),
      li("Minderheids-, gedoog- en extraparlementaire kabinetten bestaan in het model niet: er zijn altijd meer dan 75 zetels nodig."),
      li("De zetelsimulatie is bewust aan de ruime kant afgesteld: liever een band die iets te breed is dan een die te krap is. Voor de formatie zijn de uitschieters (een eindsprint of een ineenstorting) vaak belangrijker dan de buik van de verdeling, omdat juist zij bepalen welke coalities een meerderheid kunnen halen."),
      li("Partijen met minder dan 3 zetels hebben nadelen bij de formatie, maar zijn niet volledig uitgesloten."),
      li("De puntschatting van het aantal zetels is een gewogen gemiddelde van de peilingen: hoe recenter de peiling, hoe zwaarder die telt."),
      li("De moeilijkheid van een formatie volgt uit de optimalisatiefunctie. De grenzen tussen de vijf categorieën zijn arbitrair, deels gebaseerd op eerdere formaties.")))),
    section("Belangrijke beperkingen", null, h("div", { class: "prose" }, h("ul", {},
      li("Het model houdt nog onvoldoende rekening met de stabiele basis van partijen, vooral in de verhouding tussen het verdubbelen en het verliezen van alle zetels."),
      li("Percentages met één decimaal zijn puntschattingen van de werkelijke kans, geen exacte waarden.")))),
    h("p", { class: "note" }, "De uitingen op deze website en de uitkomsten van het model zijn persoonlijk en geven niet de mening van mijn werkgever weer. Hoe het formatiemodel het deed met de echte uitslagen sinds 2006, en hoe goed de zetelmarges kloppen, staat op de pagina Vorige verkiezingen."),
    section("Stats for nerds", `Er worden ${nl(DATA.sims.n, 0)} verkiezingen gesimuleerd. De grafiek laat zien hoe het aandeel van de vijf eerste coalities stabiliseert naarmate er meer simulaties zijn.`,
      card(h("h3", {}, "Aandeel per coalitie naarmate het aantal simulaties groeit"), runChart)),
    section("Convergentie", "RMSD meet hoe sterk de verdeling verandert; de Jensen-Shannon-divergentie (JSD) hoe sterk opeenvolgende verdelingen op elkaar lijken. Een JSD onder 0,1 betekent dat de laatste helft van de simulaties minder dan 10 procent invloed had. Dit is alleen relevant voor de conditionele analyses.",
      h("div", { class: "grid-2" }, card(h("h3", {}, "RMSD (× 10.000)"), one("RMSD × 10.000", conv.rmsd.map((v) => v * 1e4), (v) => nl(v, 1))), card(h("h3", {}, "JSD"), one("JSD", conv.jsd, (v) => nl(v, 3))))),
    section("Hoe zeker is het model?", "De top-5-som is de totale kans van de vijf meest waarschijnlijke coalities: hoe hoger, hoe meer de kans geconcentreerd is. Entropie meet hoe verspreid de kansen zijn: laag betekent dat één of enkele coalities domineren.",
      h("div", { class: "grid-2" },
        card(h("h3", {}, "Top-5-som"), lineChart({ x: conc.dates, series: [{ name: "Top-5-som", values: conc.top5.map((v) => v * 100), color: css("--accent") }], yMax: 100, yFormat: (v) => `${nl(v, 0)}%`, tipFormat: (v) => pct(v), height: 220, title: "Top-5-som" })),
        card(h("h3", {}, "Entropie"), lineChart({ x: conc.dates, series: [{ name: "Entropie", values: conc.entropy, color: css("--accent") }], yFormat: (v) => nl(v, 1), tipFormat: (v) => nl(v, 2), height: 220, title: "Entropie" })))),
  ];
}


/* ---------- news posts ---------- */

const today = () => new Date().toISOString().slice(0, 10);
const visiblePosts = () => POSTS.filter((p) => p.date <= today());
const esc = (t) => t.replace(/&/g, "&amp;").replace(/</g, "&lt;").replace(/>/g, "&gt;").replace(/"/g, "&quot;");

/* Small Markdown subset: #/##/### headings, paragraphs, **vet**, *cursief*,
   [links](https://...), lists (- or 1.), > quotes, and {{grafiek: ...}} lines. */
function inlineMd(t) {
  return esc(t)
    .replace(/\*\*(.+?)\*\*/g, "<strong>$1</strong>")
    .replace(/(^|[^*])\*(?!\s)(.+?)\*/g, "$1<em>$2</em>")
    .replace(/\[([^\]]+)\]\((https?:\/\/[^)\s]+|#[\w.~-]+)\)/g, (m, txt, url) => `<a href="${url}"${url.startsWith("#") ? "" : ' target="_blank" rel="noopener"'}>${txt}</a>`);
}
function markdownBlocks(md) {
  const blocks = [];
  const lines = md.replace(/\r\n/g, "\n").split("\n");
  let para = [], list = null, quote = [];
  const flush = () => {
    if (para.length) blocks.push({ html: `<p>${inlineMd(para.join(" "))}</p>` });
    if (list) blocks.push({ html: `<${list.tag}>${list.items.map((i) => `<li>${inlineMd(i)}</li>`).join("")}</${list.tag}>` });
    if (quote.length) blocks.push({ html: `<blockquote>${inlineMd(quote.join(" "))}</blockquote>` });
    para = []; list = null; quote = [];
  };
  for (const raw of lines) {
    const line = raw.trim();
    let m;
    if (!line) { flush(); continue; }
    if ((m = line.match(/^\{\{\s*grafiek\s*:\s*(.+?)\s*\}\}$/i))) { flush(); blocks.push({ chart: m[1] }); continue; }
    if ((m = line.match(/^(#{1,3})\s+(.*)$/))) { flush(); const n = Math.min(3, m[1].length + 1); blocks.push({ html: `<h${n}>${inlineMd(m[2])}</h${n}>` }); continue; }
    if ((m = line.match(/^>\s?(.*)$/))) { if (para.length || list) flush(); quote.push(m[1]); continue; }
    if ((m = line.match(/^([-*]|\d+\.)\s+(.*)$/))) {
      const tag = /\d/.test(m[1]) ? "ol" : "ul";
      if (para.length || quote.length || (list && list.tag !== tag)) flush();
      (list || (list = { tag, items: [] })).items.push(m[2]); continue;
    }
    if (list || quote.length) flush();
    para.push(line);
  }
  flush();
  return blocks;
}

/* time series cut off at the post date */
function cutSeries(ts, date) {
  if (!ts) return null;
  const keep = ts.dates.map((d, i) => (d <= date ? i : -1)).filter((i) => i >= 0);
  if (!keep.length) return null;
  const series = {};
  for (const [k, v] of Object.entries(ts.series)) series[k] = keep.map((i) => v[i]);
  return { dates: keep.map((i) => ts.dates[i]), series };
}
const lastValues = (ts) => Object.entries(ts.series).map(([k, v]) => [k, v.at(-1)]).filter(([, v]) => v != null);
const topAt = (ts, n) => lastValues(ts).sort((a, b) => b[1] - a[1]).slice(0, n).map(([k]) => k);

const CHARTS = {
  "zetels": { title: "Zetels in de peilingen", ts: () => DATA.timeseries.seats, kind: "line", n: 5, unit: "zetels" },
  "zetels-staaf": { title: "Zetels in de peilingen", ts: () => DATA.timeseries.seats, kind: "bar", unit: "zetels" },
  "regeringskans": { title: "Kans op regeringsdeelname", ts: () => DATA.timeseries.individual, kind: "line", n: 4, unit: "%" },
  "kansen": { title: "Kans op regeringsdeelname", ts: () => DATA.timeseries.individual, kind: "bar", unit: "%" },
  "coalities": { title: "Coalitiekansen", ts: () => DATA.timeseries.coalitions, kind: "line", n: 3, unit: "%", sep: ";" },
  "top-coalities": { title: "Meest waarschijnlijke coalities", ts: () => DATA.timeseries.coalitions, kind: "bar", n: 5, unit: "%" },
  "premier": { title: "Kans op grootste coalitiepartij", ts: () => DATA.timeseries.grootste, kind: "line", n: 3, unit: "%" },
  "tevredenheid": { title: "Partijtevredenheid", ts: () => DATA.timeseries.happiness, kind: "line", n: 4, unit: "" },
  "beleid": { title: "Op wiens beleid lijkt het kabinet", ts: () => DATA.timeseries.beleid, kind: "line", n: 4, unit: "%" },
  "beleid-staaf": { title: "Op wiens beleid lijkt het kabinet", ts: () => DATA.timeseries.beleid, kind: "bar", unit: "%" },
  "meerderheid": { title: "Kans op een kabinet met 76 zetels", ts: () => DATA.timeseries.meerderheid, kind: "line", n: 1, unit: "%" },
  "moeilijkheid": { title: "Hoe moeilijk wordt de formatie", ts: () => DATA.timeseries.moeilijkheid, kind: "line", n: 4, unit: "%" },
  "moeilijkheid-staaf": { title: "Hoe moeilijk wordt de formatie", ts: () => DATA.timeseries.moeilijkheid, kind: "bar", unit: "%", keepOrder: true },
  "kabinetsgrootte": { title: "Hoeveel partijen in het kabinet", ts: () => DATA.timeseries.kabinetsgrootte, kind: "line", n: 4, unit: "%" },
  "kabinetsgrootte-staaf": { title: "Hoeveel partijen in het kabinet", ts: () => DATA.timeseries.kabinetsgrootte, kind: "bar", unit: "%", keepOrder: true },
  "eerste-kamer": { title: "Kans op een meerderheid in de Eerste Kamer", ts: () => DATA.eersteKamer.timeseries, kind: "line", n: 3, unit: "%", sep: ";" },
  "combinatie": { title: "Kans op een kabinet met of zonder bepaalde partijen", ts: () => DATA.timeseries.coalitionsAll || DATA.timeseries.coalitions, kind: "combo", unit: "%",
    hint: "met VVD; zonder PRO, PVV" },
};

/* {{grafiek: combinatie | met VVD; zonder PRO, PVV}}: the chance of such a cabinet through time,
   with the coalitions that make it up on the post date */
function comboChart(fig, ts, listRaw, titleRaw) {
  const { met, zonder } = parseCombo(listRaw || CHARTS.combinatie.hint);
  const title = titleRaw || comboTitle(met, zonder);
  fig.append(h("h3", {}, title));
  const keys = Object.keys(ts.series).filter((k) => comboMatch(k.split(", "), met, zonder));
  const values = ts.dates.map((_, i) => sum(keys.map((k) => ts.series[k][i] || 0)));
  const sel = { id: `post-${chartSeq++}`, values: ["kans"] };
  fig.append(lineChart({
    x: ts.dates, series: [{ name: "Kans", values, color: colorFor("kans", sel) }],
    yFormat: (v) => `${nl(v, 0)}%`, tipFormat: (v) => pct(v), title,
  }));
  const top = keys.map((k) => [k, ts.series[k].at(-1) || 0]).filter(([, v]) => v > 0).sort((a, b) => b[1] - a[1]).slice(0, 5);
  if (top.length) {
    const max = top[0][1];
    fig.append(h("div", { class: "table-wrap" }, h("table", {},
      h("thead", {}, h("tr", {}, h("th", {}, `Meest waarschijnlijk (samen ${pct(values.at(-1))})`), h("th", { class: "num" }, "Kans"))),
      h("tbody", {}, top.map(([k, v]) => h("tr", {}, h("td", {}, coalitionEl(k)),
        h("td", { class: "num" }, h("span", { class: "pbar" }, h("i", { style: `width:${(v / max) * 80}px` }), pct(v)))))))));
  } else fig.append(h("p", { class: "note" }, "Geen enkele simulatie voldoet hieraan."));
  const unknown = [...met, ...zonder].filter((p) => !(DATA.factor.parties || []).includes(p));
  if (unknown.length) fig.append(h("p", { class: "note" }, `Onbekende partij: ${unknown.join(", ")}.`));
}

let chartSeq = 0;
function postChart(spec, date) {
  const [typeRaw, listRaw = "", titleRaw] = spec.split("|").map((x) => x.trim());
  const type = typeRaw.toLowerCase(), def = CHARTS[type];
  const fig = h("figure", { class: "post-chart card" });
  if (!def) {
    fig.append(h("p", { class: "note" }, `Onbekende grafiek ‘${typeRaw}’. Kies uit: ${Object.keys(CHARTS).join(", ")}.`));
    return fig;
  }
  const ts = cutSeries(def.ts(), date);
  if (def.kind === "combo" && ts) {
    comboChart(fig, ts, listRaw, titleRaw);
    fig.append(h("figcaption", { class: "note" }, `Gegevens tot en met ${fmtDate(ts.dates.at(-1), true)}.`));
    return fig;
  }
  fig.append(h("h3", {}, titleRaw || def.title));
  if (!ts) {
    fig.append(h("p", { class: "note" }, `Er zijn geen gegevens van vóór ${fmtDate(date, true)} voor deze grafiek.`));
    return fig;
  }
  const lastDate = ts.dates.at(-1);
  const fmt = def.unit === "%" ? (v) => pct(v) : def.unit === "zetels" ? (v) => `${nl(v, def.kind === "bar" ? 1 : 1)}` : (v) => nl(v, 1);
  if (def.kind === "bar") {
    let vals = lastValues(ts).filter(([, v]) => v > 0);
    if (!def.keepOrder) vals = vals.sort((a, b) => b[1] - a[1]);
    const items = vals.slice(0, def.n || 30)
      .map(([label, value]) => ({ label, value }));
    const longLabels = items.some((i) => i.label.length > 12);
    if (longLabels) {
      // coalitions: a table reads better than bars with long labels
      const max = Math.max(...items.map((i) => i.value), 1);
      fig.append(h("div", { class: "table-wrap" }, h("table", {}, h("tbody", {}, items.map((i) => h("tr", {},
        h("td", {}, coalitionEl(i.label)),
        h("td", { class: "num" }, h("span", { class: "pbar" }, h("i", { style: `width:${(i.value / max) * 80}px` }), fmt(i.value)))))))));
    } else {
      fig.append(hbar(items, { max: def.unit === "%" ? 100 : undefined, format: fmt, title: def.title }));
    }
  } else {
    const sep = def.sep || ",";
    let keys = listRaw ? listRaw.split(sep).map((k) => k.trim()).filter(Boolean) : topAt(ts, def.n);
    if (def.sep) keys = keys.map((k) => k.split(",").map((x) => x.trim()).sort().join(", "));
    const missing = keys.filter((k) => !ts.series[k]);
    keys = keys.filter((k) => ts.series[k]);
    const sel = { id: `post-${chartSeq++}`, values: keys };
    fig.append(lineChart({
      x: ts.dates, series: keys.map((k) => ({ name: k, values: ts.series[k], color: colorFor(k, sel) })),
      yMax: def.unit === "%" ? undefined : undefined, yFormat: def.unit === "%" ? (v) => `${nl(v, 0)}%` : (v) => nl(v, 0),
      tipFormat: fmt, title: titleRaw || def.title,
    }));
    if (missing.length) fig.append(h("p", { class: "note" }, `Niet gevonden: ${missing.join(", ")}.`));
  }
  fig.append(h("figcaption", { class: "note" }, `Gegevens tot en met ${fmtDate(lastDate, true)}.`));
  return fig;
}

function postBody(post) {
  const body = h("div", { class: "post-body" });
  const blocks = markdownBlocks(post.body);
  if (!blocks.some((b) => b.chart)) blocks.push({ chart: "top-coalities" }, { chart: "zetels" });
  for (const b of blocks) {
    if (b.chart) body.append(postChart(b.chart, post.date));
    else body.insertAdjacentHTML("beforeend", b.html);
  }
  return body;
}

function postCard(post) {
  return h("a", { class: "post-card", href: postHref(post.slug) },
    h("time", { datetime: post.date }, fmtDate(post.date, true)),
    h("h3", {}, post.title),
    post.summary && h("p", {}, post.summary));
}

function pageNieuws() {
  const posts = visiblePosts();
  return [
    h("div", { class: "page-head" },
      h("span", { class: "eyebrow" }, "Nieuws"),
      h("h1", {}, "Nieuws en analyses"),
      h("p", {}, "Korte analyses bij nieuwe peilingen en modeluitkomsten. De grafieken in elk bericht tonen de stand op de dag van het bericht.")),
    posts.length ? h("div", { class: "post-list" }, posts.map(postCard)) : h("p", { class: "empty" }, "Er zijn nog geen berichten."),
    h("p", { class: "note" }, h("a", { href: "#schrijven" }, "Nieuw bericht schrijven"), " · ", h("a", { href: "#delen" }, "Posten op sociale media")),
  ];
}

// on the live site every post has its own address (findable by search engines);
// elsewhere (local preview) those pages do not exist, so use the in-page route
const POST_PATHS = location.hostname.endsWith("76zetels.com");
const postHref = (slug) => (POST_PATHS ? `/nieuws/${encodeURIComponent(slug)}/` : `#post-${slug}`);

function pagePost(post) {
  const i = visiblePosts().indexOf(post), all = visiblePosts();
  const prev = all[i + 1], next = all[i - 1];
  return [
    h("article", { class: "post" },
      h("div", { class: "page-head" },
        h("a", { class: "eyebrow back", href: "#nieuws" }, "← Nieuws"),
        h("h1", {}, post.title),
        h("time", { class: "stamp", datetime: post.date }, fmtDate(post.date, true)),
        post.summary && h("p", { class: "lede" }, post.summary)),
      postBody(post)),
    h("nav", { class: "post-nav", "aria-label": "Andere berichten" },
      prev ? h("a", { href: postHref(prev.slug) }, h("span", { class: "note" }, "Vorige"), prev.title) : h("span"),
      next ? h("a", { href: postHref(next.slug), class: "right" }, h("span", { class: "note" }, "Volgende"), next.title) : h("span")),
  ];
}

const slugify = (t) => t.toLowerCase().normalize("NFD").replace(/[̀-ͯ]/g, "").replace(/[^a-z0-9]+/g, "-").replace(/^-+|-+$/g, "").slice(0, 60) || "bericht";
const REPO = "wvanderharst/peilingen-dataset";

function pageSchrijven() {
  const st = state.schrijven || (state.schrijven = {
    title: "", date: today(), summary: "",
    body: "Schrijf hier je bericht.\n\n{{grafiek: zetels}}\n",
  });
  const preview = h("div", { class: "post-preview" });
  const fileBox = h("div", { class: "section" });
  const fileText = () => `---\ntitel: ${st.title || "Zonder titel"}\ndatum: ${st.date}\nsamenvatting: ${st.summary}\n---\n${st.body.trim()}\n`;
  const fileName = () => `${st.date}-${slugify(st.title)}.md`;

  function update() {
    const post = { slug: "voorbeeld", title: st.title || "Zonder titel", date: st.date, summary: st.summary, body: st.body };
    preview.replaceChildren(
      h("h1", {}, post.title), h("time", { class: "stamp" }, fmtDate(post.date, true)),
      post.summary && h("p", { class: "lede" }, post.summary), postBody(post));
    drawCharts(preview);
    const url = `https://github.com/${REPO}/new/main/website/posts?filename=${encodeURIComponent(fileName())}&value=${encodeURIComponent(fileText())}`;
    const status = h("span", { class: "note", role: "status" });
    const ta = h("textarea", { id: "post-file", rows: 6, readonly: true, "aria-label": "Inhoud van het bestand" }, fileText());
    fileBox.replaceChildren(
      h("div", { class: "controls" },
        h("a", { class: "btn primary", href: url, target: "_blank", rel: "noopener" }, "Openen in GitHub"),
        h("button", { type: "button", class: "btn", onclick: () => {
          navigator.clipboard.writeText(fileText()).then(() => { status.textContent = "Gekopieerd"; },
            () => { ta.select(); status.textContent = "Selecteer en kopieer de tekst hieronder."; });
        } }, "Kopiëren"), status),
      h("p", { class: "note" }, "‘Openen in GitHub’ maakt het bestand ", h("code", {}, `website/posts/${fileName()}`), " met deze inhoud alvast aan. Klik daar op ‘Commit changes’; na de volgende build staat het bericht op de site. Een bericht met een datum in de toekomst verschijnt pas op die dag."),
      ta);
  }

  const field = (id, label, el) => h("div", { class: "field" }, h("label", { for: id, class: "control-label" }, label), el);
  const title = h("input", { id: "post-title", type: "text", value: st.title, placeholder: "Bijvoorbeeld: PRO blijft de grootste in nieuwe peiling" });
  const date = h("input", { id: "post-date", type: "date", value: st.date });
  const summary = h("input", { id: "post-summary", type: "text", value: st.summary, placeholder: "Eén zin voor het overzicht" });
  const body = h("textarea", { id: "post-body", rows: 14 }, st.body);
  title.addEventListener("input", () => { st.title = title.value; update(); });
  date.addEventListener("input", () => { st.date = date.value || today(); update(); });
  summary.addEventListener("input", () => { st.summary = summary.value; update(); });
  let tmr;
  body.addEventListener("input", () => { st.body = body.value; clearTimeout(tmr); tmr = setTimeout(update, 250); });

  // chart picker
  const type = h("select", { id: "chart-type", "aria-label": "Soort grafiek" }, Object.entries(CHARTS).map(([k, d]) => h("option", { value: k }, `${d.title} (${d.kind === "bar" ? "staaf" : "lijn"})`)));
  const which = h("input", { id: "chart-which", type: "text", placeholder: "Leeg = automatisch, of bijv. PVV, VVD" });
  type.addEventListener("change", () => {
    const hint = CHARTS[type.value].hint;
    which.placeholder = hint ? `Bijv. ${hint}` : "Leeg = automatisch, of bijv. PVV, VVD";
    if (hint && !which.value.trim()) which.value = hint;
  });
  const insert = h("button", { type: "button", class: "btn" }, "Grafiek invoegen");
  insert.addEventListener("click", () => {
    const code = `{{grafiek: ${type.value}${which.value.trim() ? ` | ${which.value.trim()}` : ""}}}`;
    const pos = body.selectionStart ?? body.value.length;
    const before = body.value.slice(0, pos), after = body.value.slice(pos);
    body.value = `${before}${before && !before.endsWith("\n") ? "\n\n" : ""}${code}\n${after.startsWith("\n") ? "" : "\n"}${after}`;
    st.body = body.value; update();
  });

  update();
  return [
    h("div", { class: "page-head" },
      h("a", { class: "eyebrow back", href: "#nieuws" }, "← Nieuws"),
      h("h1", {}, "Bericht schrijven"),
      h("p", {}, "Vul het bericht in en bekijk rechts direct het resultaat. Grafieken tonen altijd de stand op de datum van het bericht.")),
    h("div", { class: "editor" },
      h("div", { class: "card editor-form" },
        field("post-title", "Titel", title),
        field("post-date", "Datum", date),
        field("post-summary", "Samenvatting", summary),
        field("post-body", "Tekst", body),
        h("p", { class: "note" }, "Opmaak: **vet**, *cursief*, ## tussenkop, - opsomming, > citaat, [link](https://…)."),
        h("div", { class: "field" }, h("span", { class: "control-label" }, "Grafiek toevoegen"),
          h("div", { class: "controls" }, type, which, insert)),
        h("p", { class: "note" }, "Bij coalities scheid je meerdere coalities met een puntkomma, bijvoorbeeld: CDA, D66, VVD; FvD, JA21, PVV.")),
      h("div", { class: "card" }, h("span", { class: "eyebrow" }, "Voorbeeld"), preview)),
    section("Bericht plaatsen", null, card(fileBox)),
  ];
}


/* ---------- share cards on social media ---------- */

const SITE_URL = "https://76zetels.com";
const TAGS = "#formatie #peilingen #TweedeKamer";
// Instagram: links in captions are not clickable, and hashtags carry more weight there
const IG_TAGS = "#formatie #peilingen #TweedeKamer #politiek #verkiezingen #kabinet #nederland";
const instagramText = (text) => {
  const site = SITE_URL.replace("https://", "");
  let t = text.replace(`Meer op ${site}`, `Link in bio · ${site}`);
  if (!t.includes(site)) t += `\n\nLink in bio · ${site}`;
  const extra = IG_TAGS.split(" ").filter((tag) => !t.includes(tag));
  return extra.length ? `${t}${t.endsWith(TAGS) ? " " : "\n"}${extra.join(" ")}` : t;
};

function shareCaptions() {
  const rows = coalitionRows(SIM.all);
  const top = rows[0], second = rows[1];
  const ind = Object.entries(inCabinet(SIM.all, SIM.parties)).filter(([p]) => p !== "DNA").sort((a, b) => b[1] - a[1]);
  const groot = Object.entries(DATA.grootste).sort((a, b) => b[1] - a[1]);
  const minority = (1 - sum(SIM.majority) / SIM.n) * 100;
  const sizeTs = DATA.timeseries.kabinetsgrootte;
  const size = sizeTs ? Object.entries(sizeTs.series).map(([k, v]) => [k, v.at(-1) || 0]).sort((a, b) => b[1] - a[1])[0] : null;
  const list = (ps) => ps.length > 1 ? `${ps.slice(0, -1).join(", ")} en ${ps.at(-1)}` : ps[0];
  const pct0 = (v) => `${nl(v, 0)}%`;
  const kind = (r) => (r.majority ? "met een meerderheid" : "zonder meerderheid");
  const ek = (DATA.eersteKamer?.current || []);
  const ekLine = (key, label) => { const c = ek.find((x) => x.coalition === key); return c ? `${label} ${pct0(c.rate)}${c.withCU ? ` (met CU ${pct0(c.withCU.rate)})` : ""}` : `${label} onbekend`; };
  // seats per party (PRO with its predecessor GL/PvdA), blocs as on the cards
  const seatArr = (p) => p === "PRO" && SIM.seats["GL/PvdA"] ? SIM.seats.PRO.map((v, i) => v + (SIM.seats["GL/PvdA"][i] || 0)) : SIM.seats[p];
  const q = (a, f) => { const s = [...a].sort((x, y) => x - y); return s[Math.round(f * (s.length - 1))]; };
  const seatList = SIM.parties.filter((p) => p !== "GL/PvdA" && SIM.seats[p]).map((p) => ({ p, a: seatArr(p) }))
    .map((x) => ({ ...x, mid: q(x.a, 0.5), lo: q(x.a, 0.1), hi: q(x.a, 0.9), mean: sum(x.a) / x.a.length })).sort((x, y) => y.mean - x.mean);
  const BL = { links: ["PRO", "SP", "PvdD", "Volt", "Denk", "BIJ1"], midden: ["D66", "CDA", "CU", "NSC", "50PLUS"], rechts: ["VVD", "SGP"], pop: ["PVV", "FvD", "JA21", "BBB", "BVNL", "DNA"] };
  const blocSeats = Object.fromEntries(Object.entries(BL).map(([k, ps]) => [k, Array.from({ length: SIM.n }, (_, i) => ps.reduce((t, p) => t + (SIM.seats[p] ? seatArr(p)[i] : 0), 0))]));
  // expected seats per party rounded to 150 with the largest remainders, as on the hemicycle card
  const expSeats = (() => {
    const xs = seatList.filter((x) => x.mean >= 0.5), tot = sum(xs.map((x) => x.mean));
    xs.forEach((x) => { x.qq = (x.mean / tot) * 150; x.s = Math.floor(x.qq); });
    let rest = 150 - sum(xs.map((x) => x.s));
    [...xs].sort((a, b) => (b.qq - b.s) - (a.qq - a.s)).forEach((x) => { if (rest > 0) { x.s++; rest--; } });
    return Object.fromEntries(xs.map((x) => [x.p, x.s]));
  })();
  const blocMean = (k) => sum(BL[k].map((p) => expSeats[p] || 0));
  const blocMaj = (ks) => (100 * blocSeats[ks[0]].filter((_, i) => ks.reduce((t, k) => t + blocSeats[k][i], 0) >= 76).length) / SIM.n;
  const piv = keyPositions().map((r) => [r.p, r.all]);   // key position, as on the card
  return {
    coalities: `Wie gaat er regeren? De meest waarschijnlijke coalitie is ${list(top.parties)} (${pct0(top.pct)}), ${kind(top)}. Daarna volgt ${list(second.parties)} (${pct0(second.pct)}).`,
    kansen: `Wie komt er in het kabinet? ${ind.slice(0, 3).map(([p, v]) => `${p} ${pct0(v)}`).join(", ")}. ${ind[3][0]} zit in ${pct0(ind[3][1])} van de simulaties in het kabinet.`,
    premier: `Wie levert de premier? ${groot[0][0]} is in ${pct0(groot[0][1])} van de simulaties de grootste partij in het kabinet, ${groot[1][0]} in ${pct0(groot[1][1])}.`,
    formatie: `Hoe moeilijk wordt de formatie? ${pct0(minority)} kans dat het eindigt in een kabinet zonder 76 zetels.${size ? ` Het waarschijnlijkst is een kabinet van ${size[0]} (${pct0(size[1])}).` : ""}`,
    trend: `Wie wint aan kans op het kabinet? ${list(ind.slice(0, 3).map(([p]) => p))} staan er het sterkst voor. Zo ontwikkelden de kansen zich sinds april.`,
    zetels: `Hoeveel zetels haalt elke partij? ${seatList.slice(0, 4).map((x) => `${x.p} ${x.mid} (${x.lo}–${x.hi})`).join(", ")}. Tussen haakjes: 8 van de 10 simulaties.`,
    halfrond: `Zo ziet de Kamer er nu uit: links ${blocMean("links")}, midden ${blocMean("midden")}, VVD en SGP ${blocMean("rechts")} en populistisch rechts ${blocMean("pop")} zetels (verwachting).`,
    blokken: `Hoe groot worden de blokken? Kans op 76 zetels samen: rechts met populistisch rechts ${pct0(blocMaj(["rechts", "pop"]))}, links met midden ${pct0(blocMaj(["links", "midden"]))}, midden met rechts ${pct0(blocMaj(["midden", "rechts"]))}.`,
    blokkentrend: `Hoe bewegen de blokken? Verwachting op verkiezingsdag: links ${blocMean("links")}, midden ${blocMean("midden")}, VVD en SGP ${blocMean("rechts")} en populistisch rechts ${blocMean("pop")} zetels. Zo veranderden ze sinds de verkiezingen van 2025.`,
    onmisbaar: `Wie kiest het kabinet? ${piv.slice(0, 3).map(([p, v]) => `${p} ${pct0(v)}`).join(", ")}: zo vaak zit een partij in elke optie van de formatie en kan zij kiezen welk kabinet er komt.`,
    eerstekamer: `Haalt het kabinet een meerderheid in de Eerste Kamer? Kans op 38 van de 75 zetels: ${ekLine("CDA, D66, VVD", "kabinet")}, ${ekLine("CDA, D66, JA21, SGP, VVD", "met JA21 en SGP")}, ${ekLine("CDA, D66, PRO, VVD, Volt", "met PRO en Volt")}.`,
  };
}

const SHARE_CARDS = [
  { id: "coalities", title: "Wie gaat er regeren?" },
  { id: "kansen", title: "Wie komt er in het kabinet?" },
  { id: "premier", title: "Wie levert de premier?" },
  { id: "formatie", title: "Hoe moeilijk wordt de formatie?" },
  { id: "trend", title: "Wie wint aan kans op het kabinet?" },
  { id: "eerstekamer", title: "Haalt het kabinet de Eerste Kamer?" },
  { id: "zetels", title: "Hoeveel zetels haalt elke partij?" },
  { id: "halfrond", title: "Zo ziet de Kamer er nu uit" },
  { id: "blokken", title: "Hoe groot worden de blokken?" },
  { id: "blokkentrend", title: "Hoe bewegen de blokken?" },
  { id: "onmisbaar", title: "Wie kiest het kabinet?" },
];

function pageDelen() {
  const st = state.delen || (state.delen = { text: {} });
  const captions = shareCaptions();
  const fullText = (id) => st.text[id] ?? `${captions[id]}\n\nMeer op ${SITE_URL.replace("https://", "")}\n${TAGS}`;
  const canShareFiles = !!(navigator.canShare && navigator.share);

  const cardEl = ({ id, title }) => {
    const img = `social/out/${id}.png`;
    const ta = h("textarea", { id: `share-${id}`, rows: 6, "aria-label": `Tekst bij ${title}` }, fullText(id));
    const count = h("span", { class: "note" });
    const status = h("span", { class: "note", role: "status" });
    const upd = () => { count.textContent = `${ta.value.length} tekens${ta.value.length > 280 ? " · te lang voor X (280)" : ""}`; };
    ta.addEventListener("input", () => { st.text[id] = ta.value; upd(); });
    upd();
    const enc = () => encodeURIComponent(ta.value);
    // fetch the image ahead of the click: Safari only allows sharing straight from the tap
    let filePromise = null;
    const getFile = () => (filePromise ||= fetch(img).then((r) => r.blob()).then((b) => new File([b], `76zetels-${id}.png`, { type: "image/png" })));
    getFile().catch(() => { filePromise = null; });
    const share = async () => {
      try {
        const file = await getFile();
        if (navigator.canShare && navigator.canShare({ files: [file] })) await navigator.share({ files: [file], text: ta.value });
        else await navigator.share({ text: ta.value, url: SITE_URL });
        status.textContent = "Gedeeld";
      } catch (e) {
        if (e && e.name !== "AbortError") status.textContent = "Delen lukt hier niet; sla de afbeelding op en kopieer de tekst.";
      }
    };
    const copy = () => navigator.clipboard.writeText(ta.value).then(() => { status.textContent = "Tekst gekopieerd"; },
      () => { ta.select(); status.textContent = "Selecteer de tekst en kopieer hem."; });
    const instagram = async () => {
      const text = instagramText(ta.value);
      const copied = navigator.clipboard ? navigator.clipboard.writeText(text).then(() => true, () => false) : Promise.resolve(false);
      if (canShareFiles) {
        // phone: Instagram takes the image from the share menu; the caption is pasted
        try {
          const file = await getFile();
          if (navigator.canShare({ files: [file] })) {
            const ok = await copied;
            status.textContent = ok ? "Bijschrift gekopieerd: kies Instagram en plak het bij je post." : "Kies Instagram; kopieer daarna de tekst als bijschrift.";
            await navigator.share({ files: [file] });
            return;
          }
        } catch (e) {
          if (e && e.name === "AbortError") return;
        }
      }
      // computer: save the image, copy the caption and open Instagram
      window.open("https://www.instagram.com/", "_blank", "noopener");
      const a = h("a", { href: img, download: `76zetels-${id}.png` });
      document.body.append(a); a.click(); a.remove();
      status.textContent = (await copied)
        ? "Afbeelding opgeslagen en bijschrift gekopieerd. Kies in Instagram ‘Maken’, voeg de afbeelding toe en plak het bijschrift."
        : "Afbeelding opgeslagen. Kies in Instagram ‘Maken’ en voeg de afbeelding en de tekst toe.";
    };
    const link = (label, href) => h("a", { class: "btn", href, target: "_blank", rel: "noopener" }, label);
    return h("div", { class: "card share-card" },
      h("img", { src: img, alt: title, loading: "lazy", width: 1080, height: 1350 }),
      h("div", { class: "share-side" },
        h("h3", {}, title),
        h("div", { class: "field" }, h("label", { class: "control-label", for: `share-${id}` }, "Tekst"), ta, count),
        h("div", { class: "controls" },
          canShareFiles && h("button", { type: "button", class: "btn primary", onclick: share }, "Delen…"),
          h("a", { class: "btn", href: img, download: `76zetels-${id}.png` }, "Afbeelding opslaan"),
          h("button", { type: "button", class: "btn", onclick: copy }, "Tekst kopiëren")),
        h("div", { class: "controls" },
          h("span", { class: "control-label" }, "Openen in"),
          h("button", { type: "button", class: "btn", onclick: instagram }, "Instagram"),
          link("X", `https://x.com/intent/post?text=${enc()}`),
          link("Bluesky", `https://bsky.app/intent/compose?text=${enc()}`),
          link("LinkedIn", `https://www.linkedin.com/feed/?shareActive=true&text=${enc()}`),
          link("Facebook", `https://www.facebook.com/sharer/sharer.php?u=${encodeURIComponent(SITE_URL)}`)),
        status));
  };

  return [
    h("div", { class: "page-head" },
      h("a", { class: "eyebrow back", href: "#nieuws" }, "← Nieuws"),
      h("h1", {}, "Delen op sociale media"),
      h("p", {}, "Kaarten en teksten met de laatste modeluitkomsten. Op je telefoon opent ‘Delen…’ het deelmenu met afbeelding en tekst, zodat je meteen naar Instagram, X, LinkedIn of WhatsApp kunt. Op de computer sla je de afbeelding op en open je het platform met de tekst al ingevuld; voeg daar de afbeelding toe. Instagram kan geen tekst overnemen: de knop kopieert een bijschrift (met ‘link in bio’ en extra hashtags) dat je daar plakt.")),
    h("div", { class: "share-list" }, comboBuilder(), SHARE_CARDS.map(cardEl)),
  ];

  /* own card: the chance of a cabinet with and without parties of choice, drawn by
     social/cards.html#combinatie in a frame and saved as an image in the browser */
  function comboBuilder() {
    const cs = st.combo || (st.combo = { met: ["VVD"], zonder: ["PRO", "PVV"], text: null });
    const options = DATA.factor.parties.filter((p) => p !== "GL/PvdA" && p !== "DNA");
    const frame = h("iframe", { title: "Voorbeeld van de kaart", tabindex: "-1", "aria-hidden": "true", width: 1080, height: 1350 });
    const box = h("div", { class: "combo-frame" }, frame);
    new ResizeObserver(() => { frame.style.transform = `scale(${box.clientWidth / 1080})`; }).observe(box);
    const ta = h("textarea", { id: "share-combinatie", rows: 6, "aria-label": "Tekst bij de eigen kaart" });
    const count = h("span", { class: "note" }), status = h("span", { class: "note", role: "status" });
    const links = h("div", { class: "controls" });
    const hash = () => {
      const q = new URLSearchParams();
      if (cs.met.length) q.set("met", cs.met.join(","));
      if (cs.zonder.length) q.set("zonder", cs.zonder.join(","));
      return `combinatie?${q.toString().replace(/%2C/g, ",")}`;
    };
    const caption = () => {
      const c = comboStats(cs.met, cs.zonder), top = c.rows.slice(0, 1);
      const kind = (r) => (r.majority ? "met meerderheid" : "minderheid");
      const q = `Hoe groot is de kans op ${comboTitle(cs.met, cs.zonder).replace(/^Een /, "een ")}?`;
      return `${q} ${nl(c.pct, 0)}% van de simulaties eindigt zo${c.pct ? `, ${nl(c.majorityPct, 0)}% met een meerderheid` : ""}.` +
        (top.length ? ` Meest waarschijnlijk: ${top.map((r) => `${andList(r.parties)} (${kind(r)}, ${nl(r.basePct, 0)}%)`).join("")}.` : "") +
        `\n\nMeer op ${SITE_URL.replace("https://", "")}\n${TAGS}`;
    };
    // the image is made from the frame once it has drawn the current choice
    let blobPromise = null;
    const ready = () => new Promise((resolve, reject) => {
      const t0 = Date.now();
      (function check() {
        const w = frame.contentWindow, d = frame.contentDocument;
        if (w && d && d.body?.dataset.ready === "1" && w.location.hash.slice(1) === hash() && w.cardToBlob) resolve(w);
        else if (Date.now() - t0 > 15000) reject(new Error("kaart niet geladen"));
        else setTimeout(check, 100);
      })();
    });
    const getBlob = () => (blobPromise ||= ready().then((w) => w.cardToBlob()));
    const name = () => `76zetels-kabinet-${[...cs.met.map((p) => `met-${p}`), ...cs.zonder.map((p) => `zonder-${p}`)].join("-").toLowerCase().replace(/[^a-z0-9-]/g, "")}.png`;
    const enc = () => encodeURIComponent(ta.value);
    const link = (label, href) => h("a", { class: "btn", href, target: "_blank", rel: "noopener" }, label);
    const updCount = () => { count.textContent = `${ta.value.length} tekens${ta.value.length > 280 ? " · te lang voor X (280)" : ""}`; };
    const drawLinks = () => links.replaceChildren(h("span", { class: "control-label" }, "Openen in"),
      link("X", `https://x.com/intent/post?text=${enc()}`), link("Bluesky", `https://bsky.app/intent/compose?text=${enc()}`),
      link("LinkedIn", `https://www.linkedin.com/feed/?shareActive=true&text=${enc()}`));
    let tmr;
    function update() {
      const src = `social/cards.html#${hash()}`;
      if (!frame.getAttribute("src")) frame.setAttribute("src", src);
      else if (frame.contentWindow) frame.contentWindow.location.hash = hash();
      blobPromise = null;
      clearTimeout(tmr); tmr = setTimeout(() => getBlob().catch(() => { blobPromise = null; }), 400);
      ta.value = cs.text ?? caption(); updCount(); drawLinks();
      status.textContent = "";
    }
    const onChange = () => { cs.text = null; update(); };
    const met = multiSelect({ id: "combo-met", options, values: cs.met, max: 6, onChange });
    const zonder = multiSelect({ id: "combo-zonder", options, values: cs.zonder, max: 6, onChange, placeholder: "Partij uitsluiten" });
    ta.addEventListener("input", () => { cs.text = ta.value; updCount(); drawLinks(); });
    const save = async () => {
      status.textContent = "Afbeelding maken…";
      try {
        const url = URL.createObjectURL(await getBlob());
        const a = h("a", { href: url, download: name() });
        document.body.append(a); a.click(); a.remove();
        setTimeout(() => URL.revokeObjectURL(url), 5000);
        status.textContent = "Afbeelding opgeslagen";
      } catch { status.textContent = "De afbeelding kon niet gemaakt worden."; }
    };
    const share = async () => {
      try {
        const file = new File([await getBlob()], name(), { type: "image/png" });
        if (navigator.canShare && navigator.canShare({ files: [file] })) await navigator.share({ files: [file], text: ta.value });
        else await navigator.share({ text: ta.value, url: SITE_URL });
        status.textContent = "Gedeeld";
      } catch (e) {
        if (e && e.name !== "AbortError") status.textContent = "Delen lukt hier niet; sla de afbeelding op en kopieer de tekst.";
      }
    };
    const copy = () => navigator.clipboard.writeText(ta.value).then(() => { status.textContent = "Tekst gekopieerd"; },
      () => { ta.select(); status.textContent = "Selecteer de tekst en kopieer hem."; });
    update();
    return h("div", { class: "card share-card" },
      box,
      h("div", { class: "share-side" },
        h("h3", {}, "Eigen kaart: kans op een kabinet"),
        h("p", { class: "note" }, "Kies welke partijen er wel en niet in moeten zitten; de kaart en de tekst passen zich direct aan. Dezelfde berekening als ‘Gecombineerde kansen’ op het overzicht."),
        h("div", { class: "controls" }, h("span", { class: "control-label" }, "Met"), met.el),
        h("div", { class: "controls" }, h("span", { class: "control-label" }, "Zonder"), zonder.el),
        h("div", { class: "field" }, h("label", { class: "control-label", for: "share-combinatie" }, "Tekst"), ta, count),
        h("div", { class: "controls" },
          canShareFiles && h("button", { type: "button", class: "btn primary", onclick: share }, "Delen…"),
          h("button", { type: "button", class: "btn", onclick: save }, "Afbeelding opslaan"),
          h("button", { type: "button", class: "btn", onclick: copy }, "Tekst kopiëren")),
        links,
        status));
  }
}

/* ---------- router ---------- */

const HIDDEN = [
  { id: "schrijven", title: "Bericht schrijven", nav: "nieuws", render: pageSchrijven },
  { id: "delen", title: "Delen op sociale media", nav: "nieuws", render: pageDelen },
];

function currentPage() {
  const id = location.hash.replace("#", "");
  // a post's own address, /nieuws/<slug>/ (pages written by seo.py at deploy)
  const path = !id && location.pathname.match(/^\/nieuws\/([^/]+)\/?$/);
  if (path) {
    const post = visiblePosts().find((p) => p.slug === decodeURIComponent(path[1]));
    if (post) return { id: `post-${post.slug}`, title: post.title, nav: "nieuws", render: () => pagePost(post) };
  }
  if (id.startsWith("post-")) {
    const post = visiblePosts().find((p) => `post-${p.slug}` === id);
    if (post) return { id, title: post.title, nav: "nieuws", render: () => pagePost(post) };
  }
  return PAGES.find((p) => p.id === id) || HIDDEN.find((p) => p.id === id) || PAGES[0];
}

const HOME_TITLE = document.title;

function render() {
  const page = currentPage();
  const navId = page.nav || page.id;
  document.querySelectorAll(".tabs a").forEach((a) => a.setAttribute("aria-current", a.getAttribute("href") === `#${navId}` ? "page" : "false"));
  const main = $("#main");
  main.replaceChildren(...page.render());
  // the home page keeps the full title from index.html (that is the one search engines show)
  document.title = page.id === "overzicht" ? HOME_TITLE : `${page.title} · 76 Zetels`;
  requestAnimationFrame(() => drawCharts(main));
}

async function start() {
  const tabs = $("#tabs");
  PAGES.forEach((p) => tabs.append(h("a", { href: `#${p.id}` }, p.title)));
  try {
    const [cur, hist] = await Promise.all([fetch("data/current.json").then((r) => r.json()), fetch("data/history.json").then((r) => r.json())]);
    DATA = cur; HISTORY = hist; SIM = buildSim();
    POSTS = await fetch("data/posts.json").then((r) => (r.ok ? r.json() : [])).catch(() => []);
    BACKTEST = await fetch("data/backtest.json").then((r) => (r.ok ? r.json() : {})).catch(() => ({}));
  } catch (e) {
    $("#main").replaceChildren(h("div", { class: "loading" }, "De gegevens konden niet worden geladen. Ververs de pagina om het opnieuw te proberen."));
    return;
  }
  $("#stamp").textContent = `Model bijgewerkt ${fmtDate(DATA.updated, true)} · laatste peiling ${fmtDate(parseDMY(DATA.lastPoll), true)}`;
  window.addEventListener("hashchange", () => { render(); scrollTo(0, 0); });
  let t;
  window.addEventListener("resize", () => { clearTimeout(t); t = setTimeout(() => drawCharts($("#main")), 120); });
  matchMedia("(prefers-color-scheme: dark)").addEventListener("change", render);
  new MutationObserver(render).observe(document.documentElement, { attributes: true, attributeFilter: ["data-theme"] });
  render();
}

start();

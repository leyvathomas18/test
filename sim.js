/* TANG BOT · Simulador de circuitos
   Motor: análisis nodal modificado (MNA) + Newton-Raphson (diodos, Zener, BJT) + integración trapezoidal (C, L). */
(function (root) {
'use strict';
const T = {
  R: { n: 'Resistencia', p: 'R', v: 1000, lab: 'Resistencia (Ω)' },
  V: { n: 'Batería', p: 'V', v: 5, lab: 'Voltaje (V)' },
  AC: { n: 'Fuente AC', p: 'AC', v: 5, f: 60, lab: 'Amplitud pico (V)' },
  SW: { n: 'Interruptor', p: 'S' },
  C: { n: 'Capacitor', p: 'C', v: 1e-6, lab: 'Capacitancia (F)' },
  L: { n: 'Bobina', p: 'L', v: 0.01, lab: 'Inductancia (H)' },
  D: { n: 'Diodo', p: 'D' },
  Z: { n: 'Diodo Zener', p: 'DZ', v: 5.1, lab: 'Voltaje Zener (V)' },
  Q: { n: 'Transistor NPN', p: 'Q', v: 100, lab: 'Ganancia β' },
  G: { n: 'Tierra (GND)', p: 'GND' }
};
const ICON = { R: '▭', V: '🔋', AC: '∿', SW: '⏻', C: '⊣⊢', L: '⌇', D: '▷|', Z: '▷Z', Q: 'Q', G: '⏚' };
const LP = { R: [[0,0],[4,0]], V: [[0,0],[4,0]], AC: [[0,0],[4,0]], SW: [[0,0],[4,0]], C: [[0,0],[4,0]],
  L: [[0,0],[4,0]], D: [[0,0],[4,0]], Z: [[0,0],[4,0]], Q: [[0,2],[2,0],[2,4]], G: [[0,0]] }; // Q: B, C, E
const rot = (c, p) => { let [x, y] = p; for (let i = 0; i < c.r; i++) [x, y] = [-y, x]; return [c.x + x, c.y + y]; };
const pins = c => LP[c.t].map(p => rot(c, p));

const VT = .02585, IS = 1e-14, GM = 1e-12;
const ex = v => Math.exp(Math.min(v, 40));
function dio(c, v) {
  const e = ex(v / VT); let i = IS * (e - 1), g = IS * e / VT;
  if (c.t === 'Z') { const z = ex(-(v + c.val) / (2 * VT)); i -= 5e-3 * z; g += 5e-3 * z / (2 * VT); }
  return [i, g + GM];
}
function solve(A, B) {
  const n = B.length;
  for (let i = 0; i < n; i++) {
    let p = i;
    for (let r = i + 1; r < n; r++) if (Math.abs(A[r][i]) > Math.abs(A[p][i])) p = r;
    [A[i], A[p]] = [A[p], A[i]]; [B[i], B[p]] = [B[p], B[i]];
    const d = A[i][i] || 1e-18;
    for (let r = i + 1; r < n; r++) {
      const f = A[r][i] / d;
      if (f) { for (let c = i; c < n; c++) A[r][c] -= f * A[i][c]; B[r] -= f * B[i]; }
    }
  }
  const X = new Float64Array(n);
  for (let i = n - 1; i >= 0; i--) {
    let s = B[i];
    for (let c = i + 1; c < n; c++) s -= A[i][c] * X[c];
    X[i] = s / (A[i][i] || 1e-18);
  }
  return X;
}

function make(comps, wires) {
  const par = [], M = new Map();
  const id = (x, y) => { const k = x + ',' + y; if (!M.has(k)) { M.set(k, par.length); par.push(par.length); } return M.get(k); };
  const f = a => { while (par[a] !== a) a = par[a] = par[par[a]]; return a; };
  const un = (a, b) => { par[f(a)] = f(b); };
  wires.forEach(w => un(id(w.a[0], w.a[1]), id(w.b[0], w.b[1])));
  let g0 = -1;
  comps.forEach(c => {
    c.pi = pins(c).map(p => id(p[0], p[1]));
    if (c.t === 'G') { if (g0 < 0) g0 = c.pi[0]; else un(c.pi[0], g0); }
  });
  if (g0 < 0) return { error: 'Falta un símbolo de tierra (GND).' };
  const nm = new Map([[f(g0), 0]]); let N = 1;
  comps.forEach(c => { c.n = c.pi.map(p => { const r = f(p); if (!nm.has(r)) nm.set(r, N++); return nm.get(r); }); });
  const src = comps.filter(c => c.t === 'V' || c.t === 'AC');
  src.forEach((c, k) => { c.k = N - 1 + k; });
  const S = N - 1 + src.length;
  const nl = comps.filter(c => c.t === 'D' || c.t === 'Z' || c.t === 'Q');
  comps.forEach(c => { c.vp = 0; c.ip = 0; c.vj = [0, 0]; });
  let x = new Float64Array(S), t = 0, bad = false;
  const V = n => (n ? x[n - 1] : 0);

  function step(dt) {
    t += dt;
    let xn = x;
    for (let it = 0; it < 100; it++) {
      const A = Array.from({ length: S }, () => new Float64Array(S)), B = new Float64Array(S);
      const G = (a, b, g) => { if (a) A[a-1][a-1] += g; if (b) A[b-1][b-1] += g; if (a && b) { A[a-1][b-1] -= g; A[b-1][a-1] -= g; } };
      const J = (a, b, i) => { if (a) B[a-1] -= i; if (b) B[b-1] += i; }; // fuente de corriente a→b
      for (let k = 1; k < N; k++) A[k-1][k-1] += GM;
      for (const c of comps) {
        const [a, b] = c.n;
        switch (c.t) {
          case 'R': G(a, b, 1 / c.val); break;
          case 'SW': G(a, b, c.on ? 1e3 : 1e-9); break;
          case 'C': { const g = 2 * c.val / dt; G(a, b, g); J(a, b, -(g * c.vp + c.ip)); break; }
          case 'L': { const g = dt / (2 * c.val); G(a, b, g); J(a, b, c.ip + g * c.vp); break; }
          case 'V': case 'AC': {
            const E = c.t === 'V' ? c.val : c.val * Math.sin(2 * Math.PI * c.f * t), k = c.k;
            if (a) { A[a-1][k] += 1; A[k][a-1] += 1; }
            if (b) { A[b-1][k] -= 1; A[k][b-1] -= 1; }
            B[k] = E; break;
          }
          case 'D': case 'Z': { const v = c.vj[0], [i, g] = dio(c, v); G(a, b, g); J(a, b, i - g * v); break; }
          case 'Q': {
            const [vbe, vbc] = c.vj, bf = c.val, ef = ex(vbe / VT), er = ex(vbc / VT);
            const If = IS * (ef - 1), Ir = IS * (er - 1), gf = IS * ef / VT, gr = IS * er / VT;
            const Ib = If / bf + Ir, Ic = If - 2 * Ir;
            const rb = [gf / bf + gr, -gr, -gf / bf], rc = [gf - 2 * gr, 2 * gr, -gf];
            const re = rb.map((q, j) => -(q + rc[j])), v0 = [vbe, vbe - vbc, 0];
            [[c.n[0], rb, Ib], [c.n[1], rc, Ic], [c.n[2], re, -(Ib + Ic)]].forEach(([nk, row, I0]) => {
              if (!nk) return;
              let eq = I0;
              for (let j = 0; j < 3; j++) { eq -= row[j] * v0[j]; if (c.n[j]) A[nk-1][c.n[j]-1] += row[j]; }
              B[nk-1] -= eq;
            });
          }
        }
      }
      xn = solve(A, B);
      const Vn = n => (n ? xn[n - 1] : 0);
      let ok = true;
      for (const c of nl) {
        const nv = c.t === 'Q' ? [Vn(c.n[0]) - Vn(c.n[2]), Vn(c.n[0]) - Vn(c.n[1])] : [Vn(c.n[0]) - Vn(c.n[1]), 0];
        for (let j = 0; j < (c.t === 'Q' ? 2 : 1); j++) {
          const d = nv[j] - c.vj[j];
          if (Math.abs(d) > 1e-6) ok = false;
          c.vj[j] += Math.max(-.5, Math.min(.5, d));
        }
      }
      if (ok) break;
    }
    x = xn;
    for (const c of comps) {
      const v = V(c.n[0]) - V(c.n[1]);
      if (c.t === 'C') { const g = 2 * c.val / dt; c.ip = g * v - (g * c.vp + c.ip); c.vp = v; }
      else if (c.t === 'L') { const g = dt / (2 * c.val); c.ip = g * v + c.ip + g * c.vp; c.vp = v; }
    }
    if (x.some(Number.isNaN)) bad = true;
  }
  function read(c) {
    const v = V(c.n[0]) - V(c.n[1]);
    switch (c.t) {
      case 'R': return { v, i: v / c.val };
      case 'SW': return { v, i: v * (c.on ? 1e3 : 1e-9) };
      case 'C': case 'L': return { v, i: c.ip };
      case 'V': case 'AC': return { v, i: -x[c.k] };
      case 'D': case 'Z': return { v, i: dio(c, v)[0] };
      case 'Q': {
        const vbe = V(c.n[0]) - V(c.n[2]), vbc = V(c.n[0]) - V(c.n[1]);
        return { v: V(c.n[1]) - V(c.n[2]), i: IS * (ex(vbe / VT) - 1) - 2 * IS * (ex(vbc / VT) - 1) };
      }
    }
    return { v: 0, i: 0 };
  }
  return { step, read, get t() { return t; }, get bad() { return bad; } };
}

function eng(v) {
  if (!isFinite(v)) return '—';
  const a = Math.abs(v); if (a < 1e-15) return '0';
  for (const [m, s] of [[1e9,'G'],[1e6,'M'],[1e3,'k'],[1,''],[1e-3,'m'],[1e-6,'µ'],[1e-9,'n'],[1e-12,'p']])
    if (a >= m * .9995) return +(v / m).toPrecision(3) + s;
  return v.toExponential(1);
}
function parse(s) {
  const m = String(s).trim().replace(',', '.').match(/^(-?\d*\.?\d+(?:e[-+]?\d+)?)\s*([pnuµmkMG]?)/);
  if (!m) return NaN;
  return +m[1] * ({ p: 1e-12, n: 1e-9, u: 1e-6, 'µ': 1e-6, m: 1e-3, k: 1e3, M: 1e6, G: 1e9 }[m[2]] || 1);
}
root.Sim = { T, pins, make, eng, parse };
if (typeof document !== 'undefined') ui();

/* ---------------------------- Interfaz ---------------------------- */
function ui() {
  const $ = id => document.getElementById(id), cv = $('simCv'), cx = cv.getContext('2d'), sc = $('scopeCv'), sx = sc.getContext('2d'), G = 20;
  let comps = [], wires = [], sel = null, tool = null, sim = null, run = false, dt = 1e-5, spf = 200, cnt = 0, ptr = [0, 0], wr = null, dr = null, uid = 0;
  let tdiv = 5e-3; const vdiv = [0, 0], last = [-1, -1], num = {}, pr = [{ id: 0, k: 'v' }, { id: 0, k: 'i' }], buf = [[], []];

  const ln = (c, pts) => { c.beginPath(); pts.forEach((p, i) => i ? c.lineTo(p[0], p[1]) : c.moveTo(p[0], p[1])); c.stroke(); };
  const SYM = {
    R: c => ln(c, [[0,0],[.7,0],[1,-.4],[1.5,.4],[2,-.4],[2.5,.4],[3,-.4],[3.3,0],[4,0]]),
    V: c => { ln(c, [[0,0],[1.7,0]]); ln(c, [[1.7,-.8],[1.7,.8]]); ln(c, [[2.3,-.4],[2.3,.4]]); ln(c, [[2.3,0],[4,0]]); c.font = '.7px sans-serif'; c.fillText('+', 1, -.3); },
    AC: c => { ln(c, [[0,0],[1.1,0]]); ln(c, [[2.9,0],[4,0]]); c.beginPath(); c.arc(2, 0, .9, 0, 7); c.stroke();
      const p = []; for (let i = 0; i <= 20; i++) p.push([1.4 + i * .03, -Math.sin(i / 20 * 2 * Math.PI) * .4]); ln(c, p); },
    SW: (c, k) => { ln(c, [[0,0],[1,0]]); ln(c, [[3,0],[4,0]]); ln(c, k.on ? [[1,0],[3,0]] : [[1,0],[2.8,-.9]]); },
    C: c => { ln(c, [[0,0],[1.8,0]]); ln(c, [[2.2,0],[4,0]]); ln(c, [[1.8,-.9],[1.8,.9]]); ln(c, [[2.2,-.9],[2.2,.9]]); },
    L: c => { c.beginPath(); c.moveTo(0, 0); c.lineTo(.8, 0); for (let k = 0; k < 4; k++) c.arc(1.1 + .6 * k, 0, .3, Math.PI, 0); c.lineTo(4, 0); c.stroke(); },
    D: c => { ln(c, [[0,0],[1.5,0]]); ln(c, [[2.5,0],[4,0]]); c.beginPath(); c.moveTo(1.5, -.7); c.lineTo(1.5, .7); c.lineTo(2.5, 0); c.closePath(); c.stroke(); ln(c, [[2.5,-.7],[2.5,.7]]); },
    Z: (c, k) => { SYM.D(c, k); ln(c, [[2.5,-.7],[2.2,-.9]]); ln(c, [[2.5,.7],[2.8,.9]]); },
    Q: c => { ln(c, [[0,2],[1.3,2]]); ln(c, [[1.3,1],[1.3,3]]); ln(c, [[1.3,1.4],[2,.7],[2,0]]); ln(c, [[1.3,2.6],[2,3.3],[2,4]]);
      c.beginPath(); c.moveTo(1.95, 3.25); c.lineTo(1.59, 3.11); c.lineTo(1.81, 2.89); c.closePath(); c.fill(); },
    G: c => { ln(c, [[0,0],[0,.6]]); ln(c, [[-.7,.6],[.7,.6]]); ln(c, [[-.45,.9],[.45,.9]]); ln(c, [[-.2,1.2],[.2,1.2]]); }
  };
  const valStr = c => ({ R: eng(c.val) + 'Ω', V: eng(c.val) + 'V', AC: eng(c.val) + 'V ' + eng(c.f) + 'Hz', C: eng(c.val) + 'F', L: eng(c.val) + 'H',
    Z: eng(c.val) + 'V', Q: 'β=' + c.val, SW: c.on ? 'cerrado' : 'abierto' }[c.t] || '');
  const pu = k => (k === 'v' ? 'V' : 'A');

  function fit(c) {
    const d = devicePixelRatio || 1, r = c.getBoundingClientRect(), w = Math.round(r.width * d), h = Math.round(r.height * d);
    if (c.width !== w || c.height !== h) { c.width = w; c.height = h; }
    return d;
  }
  function drawComp(c, al) {
    const on = sel && sel.o === c;
    cx.save(); cx.globalAlpha = al || 1; cx.strokeStyle = cx.fillStyle = on ? '#ffb300' : '#e6f1ff';
    cx.translate(c.x * G, c.y * G); cx.rotate(c.r * Math.PI / 2); cx.scale(G, G); cx.lineWidth = 2 / G; cx.lineJoin = 'round';
    SYM[c.t](cx, c); cx.restore();
    const ps = pins(c);
    cx.save(); cx.globalAlpha = al || 1; cx.fillStyle = '#00e5ff';
    ps.forEach(p => { cx.beginPath(); cx.arc(p[0] * G, p[1] * G, 3, 0, 7); cx.fill(); });
    if (c.t !== 'G') {
      const mx = ps.reduce((s, p) => s + p[0], 0) / ps.length * G, my = ps.reduce((s, p) => s + p[1], 0) / ps.length * G;
      const horiz = c.t !== 'Q' && ps[0][1] === ps[1][1];
      const x = c.t === 'Q' ? Math.max(...ps.map(p => p[0])) * G + 8 : horiz ? mx : mx + 20, y = c.t === 'Q' ? my - 6 : horiz ? my - 26 : my - 6;
      cx.textAlign = horiz ? 'center' : 'left'; cx.font = '12px Inter,sans-serif'; cx.fillStyle = on ? '#ffb300' : '#c9d8f2';
      cx.fillText(c.name + ' ' + valStr(c), x, y);
      if (sim && !sim.error && sim.t > 0) { const m = sim.read(c); cx.font = '11px "JetBrains Mono",monospace'; cx.fillStyle = '#00e5ff'; cx.fillText(eng(m.v) + 'V  ' + eng(m.i) + 'A', x, y + 14); }
    }
    cx.restore();
  }
  const wpath = w => [w.a, [w.b[0], w.a[1]], w.b];
  function draw() {
    const d = fit(cv); cx.setTransform(d, 0, 0, d, 0, 0);
    const W = cv.width / d, H = cv.height / d; cx.clearRect(0, 0, W, H);
    cx.fillStyle = 'rgba(0,229,255,.25)';
    for (let x = 0; x < W; x += G) for (let y = 0; y < H; y += G) cx.fillRect(x - .5, y - .5, 1.5, 1.5);
    const dw = (w, col) => { cx.strokeStyle = col; cx.lineWidth = 2; ln(cx, wpath(w).map(p => [p[0] * G, p[1] * G])); };
    wires.forEach(w => dw(w, sel && sel.o === w ? '#ffb300' : '#4dd0e1'));
    comps.forEach(c => drawComp(c));
    cx.fillStyle = '#4dd0e1'; wires.forEach(w => [w.a, w.b].forEach(p => { cx.beginPath(); cx.arc(p[0] * G, p[1] * G, 3, 0, 7); cx.fill(); }));
    if (wr) { cx.setLineDash([5, 4]); dw(wr, '#ff4081'); cx.setLineDash([]); }
    if (tool) drawComp({ t: tool, x: ptr[0], y: ptr[1], r: 0, val: T[tool].v, f: T[tool].f, on: false, name: T[tool].p }, .45);
  }
  function nice(x) { const e = Math.pow(10, Math.floor(Math.log10(x))), f = x / e; return e * (f <= 1 ? 1 : f <= 2 ? 2 : f <= 5 ? 5 : 10); }
  function drawScope() {
    const d = fit(sc); sx.setTransform(d, 0, 0, d, 0, 0);
    const W = sc.width / d, H = sc.height / d; sx.fillStyle = '#030712'; sx.fillRect(0, 0, W, H);
    sx.strokeStyle = 'rgba(0,229,255,.15)'; sx.lineWidth = 1;
    for (let i = 0; i <= 10; i++) ln(sx, [[i * W / 10, 0], [i * W / 10, H]]);
    for (let i = 0; i <= 8; i++) ln(sx, [[0, i * H / 8], [W, i * H / 8]]);
    sx.strokeStyle = 'rgba(0,229,255,.4)'; ln(sx, [[0, H / 2], [W, H / 2]]);
    sx.font = '11px "JetBrains Mono",monospace';
    const tn = sim && !sim.error ? sim.t : 0, win = tdiv * 10, t0 = Math.max(0, tn - win);
    [['#00e5ff', 0], ['#ffb300', 1]].forEach(([col, k]) => {
      const data = buf[k], p = pr[k], c = comps.find(q => q.id === p.id); if (!c || !data.length) return;
      let m = 1e-12; data.forEach(q => { m = Math.max(m, Math.abs(q[1])); });
      const dv = vdiv[k] || nice(m / 3.5);
      sx.save(); sx.beginPath(); sx.rect(0, 0, W, H); sx.clip();
      sx.strokeStyle = col; sx.lineWidth = 1.6; ln(sx, data.map(q => [(q[0] - t0) / win * W, H / 2 - q[1] / dv * H / 8]));
      sx.restore();
      sx.fillStyle = col; sx.fillText(`CH${k + 1} ${p.k.toUpperCase()}(${c.name}) ${eng(dv)}${pu(p.k)}/div${vdiv[k] ? '' : ' (auto)'} · último ${eng(data[data.length - 1][1])}${pu(p.k)}`, 8, 14 + k * 14);
    });
    sx.fillStyle = '#8fa3c7'; sx.textAlign = 'right'; sx.fillText(`${eng(tdiv)}s/div · t = ${eng(tn)}s`, W - 8, H - 8); sx.textAlign = 'left';
  }

  function rebuild() { sim = make(comps, wires); buf[0] = []; buf[1] = []; last[0] = last[1] = -1; cnt = 0; probes(); }
  function probes() {
    const o = comps.filter(c => c.t !== 'G');
    const opts = '<option value="0|v">— ninguno —</option>' + o.map(c => `<option value="${c.id}|v">V · ${c.name}</option><option value="${c.id}|i">I · ${c.name}</option>`).join('');
    pr.forEach((p, k) => {
      const s = $('ch' + k);
      if (p.id && !o.some(c => c.id === p.id)) p.id = 0;
      if (!p.id && o.length) { p.id = o[o.length - 1].id; p.k = k ? 'i' : 'v'; }
      s.innerHTML = opts; s.value = p.id + '|' + p.k;
    });
  }
  [0, 1].forEach(k => { $('ch' + k).onchange = e => { const [i, q] = e.target.value.split('|'); pr[k] = { id: +i, k: q }; buf[k] = []; last[k] = -1; }; });

  /* Paleta */
  const palEl = $('pal');
  Object.keys(T).forEach(k => {
    const b = document.createElement('button'); b.className = 'pal'; b.dataset.k = k; b.innerHTML = `<b>${ICON[k]}</b>${T[k].n}`;
    b.onclick = () => { tool = tool === k ? null : k; pal(); }; palEl.appendChild(b);
  });
  const pal = () => palEl.querySelectorAll('.pal').forEach(b => b.classList.toggle('on', b.dataset.k === tool));

  /* Propiedades */
  function props() {
    const p = $('props');
    if (!sel) { p.innerHTML = '<p class="muted">Selecciona un componente para editar sus propiedades.</p>'; return; }
    if (sel.k === 'w') { p.innerHTML = '<p class="muted">Cable seleccionado. Pulsa Eliminar para quitarlo.</p>'; return; }
    const c = sel.o, t = T[c.t]; let h = `<h4>${c.name} · ${t.n}</h4>`;
    if (c.t === 'SW') h += `<button id="swb" class="sb">${c.on ? 'Abrir' : 'Cerrar'} interruptor</button>`;
    if (t.lab) h += `<label class="lb">${t.lab}<input id="pv" value="${eng(c.val)}"></label>`;
    if (c.t === 'AC') h += `<label class="lb">Frecuencia (Hz)<input id="pf" value="${eng(c.f)}"></label>`;
    if (t.lab) h += '<p class="muted">Acepta sufijos: p, n, u, m, k, M. Ej.: 4.7k, 10u.</p>';
    p.innerHTML = h;
    const sw = $('swb'); if (sw) sw.onclick = () => { c.on = !c.on; props(); };
    const set = (id, key) => { const e = $(id); if (e) e.onchange = () => { const v = parse(e.value); if (v > 0) c[key] = v; e.value = eng(c[key]); }; };
    set('pv', 'val'); set('pf', 'f');
  }

  /* Edición */
  const wp = e => { const r = cv.getBoundingClientRect(); return [(e.clientX - r.left) / G, (e.clientY - r.top) / G]; };
  const ports = () => { const a = []; comps.forEach(c => pins(c).forEach(p => a.push(p))); wires.forEach(w => a.push(w.a, w.b)); return a; };
  const nearPort = p => ports().find(q => Math.hypot(q[0] - p[0], q[1] - p[1]) < .45);
  const box = c => { const q = (c.t === 'G' ? [[0,0],[0,1.3]] : LP[c.t]).map(p => rot(c, p)), xs = q.map(a => a[0]), ys = q.map(a => a[1]);
    return [Math.min(...xs) - .6, Math.min(...ys) - .6, Math.max(...xs) + .6, Math.max(...ys) + .6]; };
  const hitC = p => [...comps].reverse().find(c => { const b = box(c); return p[0] >= b[0] && p[0] <= b[2] && p[1] >= b[1] && p[1] <= b[3]; });
  const segD = (p, a, b) => { const dx = b[0] - a[0], dy = b[1] - a[1], l = dx * dx + dy * dy || 1, u = Math.max(0, Math.min(1, ((p[0] - a[0]) * dx + (p[1] - a[1]) * dy) / l));
    return Math.hypot(p[0] - a[0] - u * dx, p[1] - a[1] - u * dy); };
  const hitW = p => wires.find(w => { const q = wpath(w); return segD(p, q[0], q[1]) < .35 || segD(p, q[1], q[2]) < .35; });

  function place(s) {
    const t = T[tool], c = { id: ++uid, t: tool, x: s[0], y: s[1], r: 0, val: t.v, f: t.f, on: false, name: tool === 'G' ? 'GND' : t.p + (num[tool] = (num[tool] || 0) + 1) };
    comps.push(c); sel = { k: 'c', o: c }; tool = null; pal(); props(); rebuild();
  }
  cv.onpointerdown = e => {
    cv.setPointerCapture(e.pointerId); const p = wp(e), s = p.map(Math.round);
    if (tool) { place(s); return; }
    const q = nearPort(p);
    if (q) { wr = { a: q.slice(), b: q.slice() }; sel = null; props(); return; }
    const c = hitC(p);
    if (c) { sel = { k: 'c', o: c }; dr = { c, dx: c.x - p[0], dy: c.y - p[1], m: false }; props(); return; }
    const w = hitW(p); sel = w ? { k: 'w', o: w } : null; props();
  };
  cv.onpointermove = e => {
    const p = wp(e); ptr = p.map(Math.round);
    if (wr) wr.b = ptr;
    if (dr) { const nx = Math.round(p[0] + dr.dx), ny = Math.round(p[1] + dr.dy); if (nx !== dr.c.x || ny !== dr.c.y) { dr.c.x = nx; dr.c.y = ny; dr.m = true; } }
  };
  cv.onpointerup = () => {
    if (wr) { if (wr.a[0] !== wr.b[0] || wr.a[1] !== wr.b[1]) { wires.push({ a: wr.a, b: wr.b }); rebuild(); } wr = null; }
    if (dr) { if (dr.m) rebuild(); else if (dr.c.t === 'SW') { dr.c.on = !dr.c.on; props(); } dr = null; }
  };
  function rotate() { if (sel && sel.k === 'c') { sel.o.r = (sel.o.r + 1) % 4; rebuild(); } }
  function del() {
    if (!sel) return;
    if (sel.k === 'c') comps = comps.filter(c => c !== sel.o); else wires = wires.filter(w => w !== sel.o);
    sel = null; props(); rebuild();
  }
  $('bRot').onclick = rotate; $('bDel').onclick = del;
  addEventListener('keydown', e => {
    if ($('viewSim').hidden || /INPUT|SELECT|TEXTAREA/.test(e.target.tagName)) return;
    if (e.key === 'r' || e.key === 'R') rotate();
    else if (e.key === 'Delete' || e.key === 'Backspace') del();
    else if (e.key === 'Escape') { tool = null; pal(); }
  });

  /* Control de simulación */
  const st = $('st');
  $('bRun').onclick = () => {
    if (!comps.length) { st.textContent = 'Agrega componentes primero.'; return; }
    if (!sim) rebuild();
    if (sim.error) { st.textContent = sim.error; return; }
    run = true;
  };
  $('bPause').onclick = () => { run = false; };
  $('bReset').onclick = () => { run = false; rebuild(); st.textContent = 'Reiniciado: t = 0'; };
  $('dtS').onchange = e => { dt = +e.target.value; clr(); };
  const clr = () => { buf[0] = []; buf[1] = []; last[0] = last[1] = -1; };
  const TD = [1e-5,2e-5,5e-5,1e-4,2e-4,5e-4,1e-3,2e-3,5e-3,1e-2,2e-2,5e-2,.1,.2,.5,1];
  $('tdS').innerHTML = TD.map(v => `<option value="${v}"${v === tdiv ? ' selected' : ''}>${eng(v)}s</option>`).join('');
  $('tdS').onchange = e => { tdiv = +e.target.value; clr(); };
  const VD = [1e-3,2e-3,5e-3,1e-2,2e-2,5e-2,.1,.2,.5,1,2,5,10,20,50,100];
  [0, 1].forEach(k => {
    $('vd' + k).innerHTML = '<option value="0">Auto</option>' + VD.map(v => `<option value="${v}">${eng(v)}</option>`).join('');
    $('vd' + k).onchange = e => { vdiv[k] = +e.target.value; };
  });
  $('spd').oninput = e => { spf = +e.target.value; };

  function frame() {
    if (run && sim && !sim.error) {
      const t0 = performance.now();
      for (let i = 0; i < spf; i++) {
        sim.step(dt);
        const minI = Math.max(dt, tdiv / 80);
        pr.forEach((p, k) => {
          if (sim.t - last[k] < minI - dt / 2 && last[k] >= 0) return;
          const c = comps.find(q => q.id === p.id); if (!c) return;
          buf[k].push([sim.t, sim.read(c)[p.k]]); last[k] = sim.t;
          while (buf[k][0][0] < sim.t - tdiv * 10 - minI) buf[k].shift();
        });
        if (i % 10 === 9 && performance.now() - t0 > 12) break;
      }
      if (sim.bad) { run = false; st.textContent = 'La simulación no convergió. Revisa el circuito.'; }
      else st.textContent = '● Simulando · t = ' + eng(sim.t) + 's';
    } else if (sim && sim.error) st.textContent = sim.error;
    else if (sim && sim.t > 0) st.textContent = '⏸ En pausa · t = ' + eng(sim.t) + 's';
    draw(); drawScope(); requestAnimationFrame(frame);
  }
  props(); probes(); frame();
}
})(typeof window !== 'undefined' ? window : globalThis);

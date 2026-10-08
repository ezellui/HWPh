/* static_api.js — the answers of hwph_serve.py, computed in the page from the files of data/.
   Written by hwph_export.py next to index.html. A page opened from disk may load scripts but not
   fetch files, so every data file is a script: HWPH.put(key, value). */
"use strict";
(function () {
  const WAIT = new Map(), DATA = new Map();
  window.HWPH = {put(key, value) { DATA.set(key, value); const w = WAIT.get(key); if (w) { w.forEach(f => f(value)); WAIT.delete(key); } }};
  function load(key) {
    if (DATA.has(key)) return Promise.resolve(DATA.get(key));
    return new Promise((ok, bad) => {
      if (WAIT.has(key)) { WAIT.get(key).push(ok); return; }
      WAIT.set(key, [ok]);
      const s = document.createElement('script');
      s.src = 'data/' + key + '.js';
      s.onerror = () => { WAIT.delete(key); bad(fail('no_file', {file: 'data/' + key + '.js'})); };
      document.head.appendChild(s);
    });
  }
  const loadAll = keys => Promise.all(keys.map(load));
  // errors as codes, as the server sends them; the page turns them into words (i18n.js)
  function fail(code, params) { const e = new Error(code); e.code = code; e.params = params || {}; return e; }

  /* ---------- folding and words: the rules of hwph_common.py ---------- */
  const DROP = new Set('´′`˜¨᾿῾῀΄΅');
  const fc = new Map();
  function foldChar(c) {
    let f = fc.get(c);
    if (f !== undefined) return f;
    if (DROP.has(c)) f = ''; else if (c === 'ß') f = 'ss';
    else f = c.normalize('NFD').replace(/\p{M}/gu, '').toLowerCase().replace(/ς/g, 'σ').replace(/ı/g, 'i');
    fc.set(c, f); return f;
  }
  function fold(s) { let o = ''; for (const c of s || '') o += foldChar(c); return o; }
  function foldMap(s) {
    let o = '', idx = [], i = 0;
    for (const c of s) { const f = foldChar(c); o += f; for (let k = 0; k < f.length; k++) idx.push(i); i += c.length; }
    return [o, idx];
  }
  const WORD = /[\p{L}\p{N}_]+/gu;
  const words = s => (fold(s).match(WORD) || []);
  const shardOf = t => [...t].slice(0, 2).map(c => c.codePointAt(0).toString(16)).join('-');
  // the same escaping as Python's html.escape, so that snippets come out character for character alike
  const esc = s => String(s == null ? '' : s).replace(/[&<>"']/g, c => ({'&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#x27;'}[c]));

  let META = null;
  async function meta() {
    if (!META) {
      META = await load('meta');
      META.byId = new Map(META.lemmas.map(r => [r[0], r]));
      META.fold = new Map(META.lemmas.map(r => [r[0], fold(r[1])]));
      META.shardSet = new Set(META.shards);
      META.regSet = new Set(META.reg_shards);
    }
    return META;
  }

  /* ---------- search: the algorithm of hwph_search.py, line for line ---------- */
  const W = '[\\p{L}\\p{N}_]', NW = '[^\\p{L}\\p{N}_]';
  const WORD_RX = /[\p{L}\p{N}_]+/gu;
  const COLS = ['lemma', 'body', 'notes', 'lit', 'authors'];
  const WEIGHTS = [10.0, 1.0, 0.35, 0.5, 2.0], K1 = 1.2, B = 0.75, NEAR_DEFAULT = 20, MAX_EXPAND = 300, MAX_VERIFY = 1500;
  const reEsc = s => s.replace(/[.*+?^${}()|[\]\\/-]/g, '\\$&');
  const cmpStr = (a, b) => (a < b ? -1 : a > b ? 1 : 0);

  function skey(term) {
    let t = term.split('ph').join('f').split('th').join('t').split('rh').join('r').split('dt').join('t');
    t = t.split('ae').join('a').split('oe').join('o').split('ue').join('u').split('ck').join('k').split('tz').join('z');
    t = t.split('ch').join('\x00');
    t = t.replace(/c(?=[eiy])/g, 'z').split('c').join('k');
    t = t.split('\x00').join('ch').split('y').join('i');
    return t.replace(/(.)\1+/gu, '$1');
  }

  // ---- parsing
  const OPS = {OR: 'or', ODER: 'or', '|': 'or', AND: 'and', UND: 'and', NOT: 'not', NICHT: 'not'};
  const NEAR_RE = /^(?:NEAR|NAHE)(?:\/(\d+))?$/;
  function lex(q) {
    const out = []; q = q.trim(); let pos = 0;
    const rx = /\s*(?:(\()|(\))|(-?)"([^"]*)"|(\S+?)(?=[\s()"]|$))/y;
    while (pos < q.length) {
      rx.lastIndex = pos; const m = rx.exec(q);
      if (!m || rx.lastIndex === pos) break;
      pos = rx.lastIndex;
      if (m[1]) out.push(['(']);
      else if (m[2]) out.push([')']);
      else if (m[4] !== undefined) { if (m[3]) out.push(['not']); out.push(['phrase', m[4]]); }
      else {
        const w = m[5];
        if (OPS[w]) out.push([OPS[w]]);
        else if (NEAR_RE.test(w)) out.push(['near', +(NEAR_RE.exec(w)[1] || NEAR_DEFAULT)]);
        else if (w.length > 1 && w[0] === '-') { out.push(['not']); out.push(['word', w.slice(1)]); }
        else out.push(['word', w]);
      }
    }
    return out;
  }
  function wordPattern(w) {
    const parts = [], cs = Array.from(w);
    for (let i = 0; i < cs.length; i++) {
      const c = cs[i];
      if (c === '*') parts.push(['any']);
      else if (c === '?') parts.push(['one']);
      else if (c === '^' && i + 1 < cs.length) { const n = cs[++i]; parts.push(n === '#' ? ['digit'] : n === '$' ? ['letter'] : ['lit', fold(n)]); }
      else parts.push(['lit', c]);
    }
    return parts;
  }
  function wordTokens(text) {
    const out = [];
    for (const raw of (text.match(/[\p{L}\p{N}_*?^#$]+/gu) || [])) {
      const ps = wordPattern(raw), lit = ps.filter(p => p[0] === 'lit').map(p => p[1]).join('');
      if (!/[\p{L}\p{N}_]/u.test(fold(lit)) && !ps.some(p => p[0] !== 'lit')) continue;
      out.push(raw);
    }
    return out;
  }
  function parse(q) {
    const toks = lex(q); let pos = 0;
    const peek = () => (pos < toks.length ? toks[pos] : null), take = () => toks[pos++];
    const leaf = () => {
      const t = peek(); if (!t) return null;
      if (t[0] === '(') { take(); const e = exprAnd(); if (peek() && peek()[0] === ')') take(); return e; }
      if (t[0] === 'phrase' || t[0] === 'word') {
        take(); const ws = wordTokens(t[1]);
        if (!ws.length) return null;
        return ws.length === 1 ? ['term', ws[0]] : ['phrase', ws];
      }
      return null;
    };
    const near = () => {
      const x = leaf(); let items = [x], dist = null;
      while (peek() && peek()[0] === 'near') {
        const d = take()[1]; dist = dist === null ? d : Math.min(dist, d);
        const y = leaf(); if (y !== null) items.push(y);
      }
      items = items.filter(i => i !== null);
      if (dist === null || items.length < 2) return items.length ? items[0] : null;
      if (items.some(i => i[0] !== 'term' && i[0] !== 'phrase')) throw fail('bad_query', {detail: 'NEAR'});
      return ['near', dist, items];
    };
    const unary = () => {
      const t = peek();
      if (t && t[0] === 'not') { take(); const x = near(); return x ? ['not', x] : null; }
      return near();
    };
    const exprOr = () => {
      let items = [unary()];
      while (peek() && peek()[0] === 'or') { take(); items.push(unary()); }
      items = items.filter(i => i !== null);
      if (!items.length) return null;
      return items.length === 1 ? items[0] : ['or', items];
    };
    function exprAnd() {
      const items = [];
      while (peek() && peek()[0] !== ')') {
        if (peek()[0] === 'and' || peek()[0] === 'or') { take(); continue; }
        const x = exprOr();
        if (x === null) { if (peek() && peek()[0] !== ')') take(); continue; }
        items.push(x);
      }
      if (!items.length) return null;
      return items.length === 1 ? items[0] : ['and', items];
    }
    let tree = exprAnd();
    while (peek()) {
      take(); const more = exprAnd();
      if (more !== null) tree = tree !== null ? ['and', [tree, more]] : more;
    }
    return tree;
  }
  function leaves(tree, neg) {
    if (!tree) return [];
    const k = tree[0];
    if (k === 'term' || k === 'phrase' || k === 'near') return [[tree, !!neg]];
    if (k === 'not') return leaves(tree[1], true);
    return [].concat(...tree[1].map(c => leaves(c, neg)));
  }

  // ---- patterns -> words of the index
  function patternRegex(raw, cs) {
    return wordPattern(raw).map(p => {
      if (p[0] === 'lit') { const ch = cs ? p[1] : fold(p[1]); return ch ? reEsc(ch) : ''; }
      if (p[0] === 'any') return W + '*';
      if (p[0] === 'one') return W;
      if (p[0] === 'digit') return '\\p{Nd}';
      return '\\p{L}';
    }).join('');
  }
  function kindOf(raw) {
    const ps = wordPattern(raw), wild = [];
    ps.forEach((p, i) => { if (p[0] !== 'lit') wild.push(i); });
    if (!wild.length) return 'plain';
    if (wild.length === 1 && wild[0] === ps.length - 1 && ps[ps.length - 1][0] === 'any') return 'prefix';
    return 'wild';
  }
  function skeyPattern(raw) {
    let out = '', run = '';
    for (const p of wordPattern(raw)) {
      if (p[0] === 'lit') run += fold(p[1]);
      else { out += run ? skey(run) : ''; run = ''; out += {any: '*', one: '?', digit: '^#', letter: '^$'}[p[0]]; }
    }
    return out + (run ? skey(run) : '');
  }
  function decode(str) {
    const out = new Map(); let prev = 0;
    for (const e of str.split(' ')) {
      const [a, c] = e.split(':'); prev += parseInt(a, 36);
      const cnt = [0, 0, 0, 0, 0]; c.split(',').forEach((x, i) => { cnt[i] = parseInt(x, 36); });
      out.set(prev, cnt);
    }
    return out;
  }
  let VOCAB = null;
  async function vocab() {           // every word of the index: term, articles, occurrences, tolerant key
    if (!VOCAB) {
      const v = await load('vocab');
      VOCAB = {terms: v.t, docs: v.d, cnt: v.c, skey: v.t.map((t, i) => v.k[i] === '' ? t : v.k[i])};
    }
    return VOCAB;
  }
  const postCache = new Map();
  async function postings(term) {
    if (postCache.has(term)) return postCache.get(term);
    const m = await meta(), name = shardOf(term);
    let d = new Map();
    if (m.shardSet.has(name)) { const sh = await load('s/' + name); if (sh[term]) d = decode(sh[term]); }
    if (postCache.size > 5000) postCache.clear();
    postCache.set(term, d);
    return d;
  }
  async function prefixTerms(head) {
    const m = await meta();
    const names = head.length >= 2 ? [shardOf(head)] : m.shards.filter(n => n.split('-')[0] === head.codePointAt(0).toString(16));
    const sh = await loadAll(names.filter(n => m.shardSet.has(n)).map(n => 's/' + n));
    const out = [];
    sh.forEach(s => Object.keys(s).forEach(t => { if (t.startsWith(head)) out.push(t); }));
    return out;
  }
  async function expandWord(raw, tolerant, max) {
    max = max || MAX_EXPAND;
    const f = fold(raw), k = kindOf(raw);
    if (k === 'plain' && !tolerant) return [[f], false];
    const v = await vocab(), rows = [];
    if (tolerant) {
      if (k === 'plain') { const key = skey(f); v.skey.forEach((s, i) => { if (s === key) rows.push(i); }); }
      else { const krx = new RegExp('^(?:' + patternRegex(skeyPattern(raw)) + ')$', 'u'); v.skey.forEach((s, i) => { if (krx.test(s)) rows.push(i); }); }
    } else {
      const rx = new RegExp('^(?:' + patternRegex(raw) + ')$', 'u');
      v.terms.forEach((t, i) => { if (rx.test(t)) rows.push(i); });
    }
    rows.sort((a, b) => v.docs[b] - v.docs[a] || cmpStr(v.terms[a], v.terms[b]));
    return [rows.slice(0, max).map(i => v.terms[i]), rows.length > max];
  }

  function leafRegex(leaf, wordsOf, cs) {
    const wordRx = raw => {
      if (cs) return patternRegex(raw, true);
      const ws = wordsOf(raw);
      if (ws === null) return patternRegex(raw);
      return ws.length ? '(?:' + ws.slice().sort((a, b) => b.length - a.length).map(reEsc).join('|') + ')' : '(?!)';
    };
    const body = leaf[0] === 'term' ? wordRx(leaf[1]) : leaf[1].map(wordRx).join(NW + '+');
    return '(?<!' + W + ')' + body + '(?!' + W + ')';
  }
  function intersect(lists) {
    if (!lists.length) return new Map();
    lists = lists.slice().sort((a, b) => a.size - b.size);
    const out = new Map();
    for (const [a, c] of lists[0]) {
      let cc = c.slice(), ok = true;
      for (const o of lists.slice(1)) { const e = o.get(a); if (!e) { ok = false; break; } cc = cc.map((x, i) => Math.min(x, e[i])); }
      if (ok) out.set(a, cc);
    }
    return out;
  }
  function bisectLeft(arr, x) { let lo = 0, hi = arr.length; while (lo < hi) { const m = (lo + hi) >> 1; if (arr[m] < x) lo = m + 1; else hi = m; } return lo; }
  function bisectRight(arr, x) { let lo = 0, hi = arr.length; while (lo < hi) { const m = (lo + hi) >> 1; if (x < arr[m]) hi = m; else lo = m + 1; } return lo; }
  function nearCount(text, rxs, dist, starts) {
    if (!text) return 0;
    const spans = [];
    for (const rx of rxs) {
      const occ = []; rx.lastIndex = 0; let m;
      while ((m = rx.exec(text))) {
        if (!m[0].length) { rx.lastIndex++; continue; }
        const a = bisectLeft(starts, m.index), b = bisectRight(starts, m.index + m[0].length - 1) - 1;
        occ.push([a, Math.max(a, b)]);
      }
      if (!occ.length) return 0;
      spans.push(occ);
    }
    let n = 0;
    for (const [a0, b0] of spans[0]) {
      let ok = true, lo = a0, hi = b0;
      for (const occ of spans.slice(1)) {
        let best = null;
        for (const [a, b] of occ) {
          const l2 = Math.min(lo, a), h2 = Math.max(hi, b), gap = Math.max(a, lo) - Math.min(b, hi) - 1;
          if (gap <= dist && (best === null || h2 - l2 < best[1] - best[0])) best = [l2, h2];
        }
        if (best === null) { ok = false; break; }
        [lo, hi] = best;
      }
      if (ok) n++;
    }
    return n;
  }

  class Search {
    constructor(tolerant, cs, col) { this.tolerant = tolerant; this.cs = cs; this.col = col; this.expanded = new Map(); this.cut = false; this.approx = null; }
    wordsOf(raw) { return this.expanded.get(raw); }            // filled by prepare()
    async prepare(tree) {
      for (const [lf] of leaves(tree))
        for (const it of (lf[0] === 'near' ? lf[2] : [lf]))
          for (const raw of (it[0] === 'term' ? [it[1]] : it[1])) {
            if (this.expanded.has(raw)) continue;
            if (kindOf(raw) === 'prefix' && !this.tolerant) { this.expanded.set(raw, null); continue; }
            const [ws, cut] = await expandWord(raw, this.tolerant);
            this.cut = this.cut || cut; this.expanded.set(raw, ws);
          }
    }
    async wordDocs(raw) {
      let ws = this.wordsOf(raw);
      if (ws === null) ws = await prefixTerms(fold(raw.slice(0, -1)));
      const out = new Map();
      for (const w of ws) for (const [a, c] of await postings(w)) {
        const e = out.get(a);
        if (!e) out.set(a, c.slice()); else for (let i = 0; i < 5; i++) e[i] += c[i];
      }
      return out;
    }
    restrict(docs) {
      if (this.col === null) return docs;
      const out = new Map();
      docs.forEach((c, a) => { if (c[this.col]) { const z = [0, 0, 0, 0, 0]; z[this.col] = c[this.col]; out.set(a, z); } });
      return out;
    }
    async countInTexts(rx, aid, near) {
      const m = await meta(), t = await load('t/' + aid);
      const cols = [m.byId.get(aid)[1], t.b, t.n, t.l, t.au];
      if (!this.cs && !t._folded) t._folded = cols.map(x => fold(x || ''));
      const out = [];
      for (let i = 0; i < 5; i++) {
        if (this.col !== null && i !== this.col) { out.push(0); continue; }
        const s = this.cs ? cols[i] : t._folded[i];
        if (near) {
          const key = (this.cs ? '_starts_c' : '_starts') + i;
          if (!t[key]) { t[key] = []; WORD_RX.lastIndex = 0; let mm; while ((mm = WORD_RX.exec(s || ''))) t[key].push(mm.index); }
          out.push(near(s, t[key]));
        } else {
          rx.lastIndex = 0; let n = 0, mm;
          while ((mm = rx.exec(s || ''))) { if (!mm[0].length) { rx.lastIndex++; continue; } n++; }
          out.push(n);
        }
      }
      return out;
    }
    async check(cand, counter) {
      let keys = [...cand.keys()].sort((a, b) => a - b);
      if (keys.length > MAX_VERIFY) {
        keys.sort((a, b) => cand.get(b).reduce((s, v) => s + v, 0) - cand.get(a).reduce((s, v) => s + v, 0) || a - b);
        this.approx = {checked: MAX_VERIFY, of: keys.length};
        keys = keys.slice(0, MAX_VERIFY).sort((a, b) => a - b);
      }
      const out = new Map();
      for (const a of keys) { const c = await counter(a); if (c.some(x => x > 0)) out.set(a, c); }
      return out;
    }
    async leafDocs(leaf) {
      const wo = r => this.wordsOf(r);
      if (leaf[0] === 'term') {
        const docs = await this.wordDocs(leaf[1]);
        if (!this.cs) return this.restrict(docs);
        const rx = new RegExp(leafRegex(leaf, wo, true), 'gu');
        return this.check(docs, a => this.countInTexts(rx, a));
      }
      if (leaf[0] === 'phrase') {
        const lists = []; for (const w of leaf[1]) lists.push(await this.wordDocs(w));
        const rx = new RegExp(leafRegex(leaf, wo, this.cs), 'gu');
        return this.check(intersect(lists), a => this.countInTexts(rx, a));
      }
      const lists = [];
      for (const it of leaf[2]) {
        if (it[0] === 'term') lists.push(await this.wordDocs(it[1]));
        else { const ls = []; for (const w of it[1]) ls.push(await this.wordDocs(w)); lists.push(intersect(ls)); }
      }
      const rxs = leaf[2].map(it => new RegExp(leafRegex(it, wo, this.cs), 'gu')), dist = leaf[1];
      return this.check(intersect(lists), a => this.countInTexts(null, a, (s, st) => nearCount(s, rxs, dist, st)));
    }
    async run(tree) { this.leafResults = []; return this.evalNode(tree); }
    async evalNode(node) {
      const k = node[0];
      if (k === 'term' || k === 'phrase' || k === 'near') { const d = await this.leafDocs(node); this.leafResults.push([node, d]); return new Set(d.keys()); }
      if (k === 'or') { const s = new Set(); for (const c of node[1]) { if (c[0] === 'not') continue; (await this.evalNode(c)).forEach(x => s.add(x)); } return s; }
      if (k === 'and') {
        let pos = null; const negs = [];
        for (const c of node[1]) {
          if (c[0] === 'not') { negs.push(c[1]); continue; }
          const r = await this.evalNode(c);
          pos = pos === null ? r : new Set([...pos].filter(x => r.has(x)));
        }
        if (pos === null) return new Set();
        for (const n of negs) { const saved = this.leafResults; this.leafResults = []; const r = await this.evalNode(n); this.leafResults = saved; r.forEach(x => pos.delete(x)); }
        return pos;
      }
      return new Set();
    }
    score(aid, m) {
      const L = m.lengths[aid] || [0, 0, 0, 0, 0], D = L.reduce((s, v) => s + v, 0);
      let s = 0;
      for (const [, docs] of this.leafResults) {
        const c = docs.get(aid); if (!c) continue;
        const nHit = docs.size;
        let idf = Math.log((m.n_docs - nHit + 0.5) / (nHit + 0.5)); if (idf <= 0) idf = 1e-6;
        let f = 0; for (let i = 0; i < 5; i++) f += WEIGHTS[i] * c[i];
        s += idf * (f * (K1 + 1)) / (f + K1 * (1 - B + B * D / m.avgdl));
      }
      return s;
    }
    highlight(tree) {
      const parts = [];
      for (const [lf, neg] of leaves(tree)) {
        if (neg) continue;
        for (const it of (lf[0] === 'near' ? lf[2] : [lf])) parts.push(leafRegex(it, r => this.wordsOf(r), this.cs).split(NW + '+').join(NW + '{1,4}'));
      }
      return parts.length ? parts.join('|') : null;
    }
  }

  function firstWord(tree) {
    const pos = leaves(tree).filter(([, n]) => !n).map(([l]) => l);
    if (!pos.length || pos[0][0] === 'near') return '';
    const ws = pos[0][0] === 'term' ? [pos[0][1]] : pos[0][1];
    if (ws.some(w => /[*?^]/.test(w.replace(/\*$/, '')))) return '';
    return ws.map(w => fold(w.replace(/\*$/, ''))).join(' ');
  }

  function snippets(text, rx, width, maxn, cs) {
    if (!text || !rx) return [];
    const chars = Array.from(text), fch = [], idx = [];
    chars.forEach((c, i) => { for (const f of Array.from(cs ? c : foldChar(c))) { fch.push(f); idx.push(i); } });   // capitals significant: the text itself
    const folded = fch.join(''), u2c = [];
    fch.forEach((f, k) => { for (let j = 0; j < f.length; j++) u2c.push(k); });
    u2c.push(fch.length);
    const hits = []; let m;
    rx.lastIndex = 0;
    while ((m = rx.exec(folded))) { if (!m[0].length) { rx.lastIndex++; continue; } hits.push([u2c[m.index], u2c[m.index + m[0].length]]); }
    if (!hits.length) return [];
    const chosen = [];
    for (const [s, e] of hits) { if (chosen.some(([c]) => Math.abs(s - c) < width * 2)) continue; chosen.push([s, e]); if (chosen.length >= maxn) break; }
    const cut = (x, y) => esc(chars.slice(x, y).join(''));
    return chosen.map(([s]) => {
      let a = Math.max(0, s - width); const b = Math.min(fch.length, s + width);
      let oa = a < idx.length ? idx[a] : 0; const ob = b - 1 < idx.length ? idx[b - 1] + 1 : chars.length;
      while (oa > 0 && !/\s/.test(chars[oa - 1]) && s - a < width + 20) { oa--; a--; }
      const ph = hits.filter(([hs, he]) => idx[hs] >= oa && idx[he - 1] < ob).map(([hs, he]) => [idx[hs], idx[he - 1] + 1]);
      let buf = '', pos = oa;
      for (const [hs, he] of ph) { buf += cut(pos, hs) + '<mark>' + cut(hs, he) + '</mark>'; pos = he; }
      buf += cut(pos, ob);
      return (oa > 0 ? '… ' : '') + buf.trim() + (ob < chars.length ? ' …' : '');
    });
  }
  function countHits(text, rx, cs) {
    if (!text || !rx) return 0;
    rx.lastIndex = 0; const f = cs ? text : fold(text); let n = 0, m;
    while ((m = rx.exec(f))) { if (!m[0].length) { rx.lastIndex++; continue; } n++; }
    return n;
  }

  async function runSearch(q, p, col) {
    let tree;
    try { tree = parse(q); } catch (e) { if (e.code) throw e; throw fail('bad_query', {detail: q}); }
    const S = new Search(p.get('tol') === '1', p.get('case') === '1', col);
    if (tree === null) return [null, S, new Set()];
    await S.prepare(tree);
    return [tree, S, await S.run(tree)];
  }
  // the found articles in the order of the result list (hwph_serve.py ranked_search)
  async function rankedSearch(p, col) {
    const q = (p.get('q') || '').trim(), band = p.get('band') || '';
    const m = await meta();
    let [tree, S, found] = await runSearch(q, p, col);
    if (tree === null) return [null, S, []];
    if (band) found = new Set([...found].filter(a => m.byId.get(a)[2] === band));
    const grp = p.get('grp') || '';
    if (grp) {
      if (!/^\d+$/.test(grp)) throw fail('bad_query', {detail: "invalid literal for int() with base 10: '" + grp + "'"});
      const d = await load('authors'), g = d.groups.find(x => x[0] === +grp);
      const members = new Set(g ? g[2].filter(x => x[0] !== null).map(x => x[0]) : []);
      found = new Set([...found].filter(a => members.has(a)));
    }
    const only = p.get('only') || '';
    if (only) {                                          // a selection of articles made by the reader
      const keep = new Set(only.split(',').filter(x => /^\d+$/.test(x.trim())).map(Number));
      found = new Set([...found].filter(a => keep.has(a)));
    }
    const first = firstWord(tree);
    const regDst = new Set(first ? (await registerRows(first)).filter(r => r[8] === first && r[5] !== 'author' && r[6]).map(r => r[6]) : []);
    const ranked = [...found].map(a => {
      const lf = m.fold.get(a);
      return [a, lf !== first ? 1 : 0, regDst.has(a) ? 0 : 1, first ? (lf.indexOf(first) >= 0 ? 0 : 1) : 1, -S.score(a, m)];
    }).sort((x, y) => x[1] - y[1] || x[2] - y[2] || x[3] - y[3] || x[4] - y[4] || x[0] - y[0]).map(r => r[0]);
    return [tree, S, ranked];
  }
  async function search(p) {
    const q = (p.get('q') || '').trim(), scope = p.get('scope') || 'all';
    const offset = +(p.get('offset') || 0), limit = Math.min(+(p.get('limit') || 20), 100);
    const col = COLS.indexOf(scope) >= 0 ? COLS.indexOf(scope) : null;
    const res = {q, total: 0, items: [], register: []};
    const m = await meta();
    const [tree, S, rankedIds] = await rankedSearch(p, col);
    if (tree === null) return res;
    const ranked = rankedIds.map(a => [a]);
    res.total = ranked.length;
    if (p.get('ids') === '1') res.ids = ranked.map(r => r[0]);   // every found article, for a selection
    if (S.cut) res.cut = true;
    if (S.approx) res.approx = S.approx;
    const hl = S.highlight(tree), rx = hl ? new RegExp(hl, 'gu') : null;
    for (const [aid] of ranked.slice(offset, offset + limit)) {
      const t = await load('t/' + aid), L = m.byId.get(aid);
      const texts = {body: t.b, notes: t.n, lit: t.l};
      const hits = {body: countHits(t.b, rx, S.cs), notes: countHits(t.n, rx, S.cs), lit: countHits(t.l, rx, S.cs)};
      const snips = [];
      const order = texts[scope] !== undefined ? [scope] : ['body', 'notes', 'lit'];
      for (const k of order) {
        for (const sn of snippets(texts[k], rx, 110, 2 - snips.length, S.cs)) snips.push({where: k, html: sn});
        if (snips.length >= 2) break;
      }
      res.items.push({id: aid, lemma: L[1], band: L[2], col_from: L[3], col_to: L[5], authors: t.A || [], hits, snippets: snips});
    }
    if (offset === 0 && (scope === 'all' || scope === 'register') && (tree[0] === 'term' || tree[0] === 'phrase')) {
      const ws = tree[0] === 'term' ? [tree[1]] : tree[1];
      if (!ws.some(w => /[*?^]/.test(w.replace(/\*$/, ''))))
        res.register = await registerLookup(ws.map(w => fold(w.replace(/\*$/, ''))).join(' '), 40, ws[ws.length - 1].endsWith('*'));
    }
    return res;
  }
  // the list of places (hwph_serve.py api_places)
  function colAt(marks, pos, first) { let c = first; for (const [off, col] of marks || []) { if (off <= pos) c = col; else break; } return c; }
  const PLACE_W = 60;
  function placesIn(text, rx, cs) {
    // (start, end) of every match in characters (code points) of the text
    if (!text || !rx) return [];
    const chars = Array.from(text), out = [];
    let fch, idx;
    if (cs) { fch = chars; idx = chars.map((_, i) => i); }
    else { fch = []; idx = []; chars.forEach((c, i) => { for (const f of Array.from(foldChar(c))) { fch.push(f); idx.push(i); } }); }
    const s = fch.join(''), u2c = [];
    fch.forEach((f, k) => { for (let j = 0; j < f.length; j++) u2c.push(k); });
    u2c.push(fch.length);
    rx.lastIndex = 0; let m;
    while ((m = rx.exec(s))) {
      if (!m[0].length) { rx.lastIndex++; continue; }
      const a = u2c[m.index], b = u2c[m.index + m[0].length];
      out.push([idx[a], idx[b - 1] + 1]);
    }
    return out;
  }
  function placeHtml(text, a, b) {
    const chars = Array.from(text), x = Math.max(0, a - PLACE_W), y = Math.min(chars.length, b + PLACE_W);
    const e = t => esc(t.replace(/\s+/g, ' '));
    return (x > 0 ? '… ' : '') + e(chars.slice(x, a).join('')) + '<mark>' + e(chars.slice(a, b).join('')) + '</mark>' + e(chars.slice(b, y).join('')) + (y < chars.length ? ' …' : '');
  }
  async function placesApi(p) {
    const q = (p.get('q') || '').trim(), scope = p.get('scope') || 'all';
    const limit = Math.max(1, Math.min(+(p.get('limit') || 500), 5000));
    const col = COLS.indexOf(scope) >= 0 ? COLS.indexOf(scope) : null;
    const [tree, S, ranked] = await rankedSearch(p, col);
    const res = {q, articles: ranked.length, places: [], more: false};
    if (tree === null) return res;
    if (S.cut) res.cut = true;
    const m = await meta(), hl = S.highlight(tree), rx = hl ? new RegExp(hl, 'gu') : null;
    let flows = [['body', 'b', 'cb'], ['lit', 'l', 'cl'], ['notes', 'n', 'cn']];
    if (['body', 'lit', 'notes'].includes(scope)) flows = flows.filter(f => f[0] === scope);
    for (const aid of ranked) {
      const t = await load('t/' + aid), L = m.byId.get(aid);
      for (const [where, f, c] of flows) {
        let k = 0;                                       // the n-th place of this part
        for (const [a, b] of placesIn(t[f], rx, S.cs)) {
          if (res.places.length >= limit) { res.more = true; return res; }
          res.places.push({id: aid, lemma: L[1], band: L[2], col: colAt(t[c], a, L[3]), where, k, html: placeHtml(t[f], a, b)});
          k++;
        }
      }
    }
    return res;
  }
  // one search in all registers (hwph_serve.py api_lookup)
  async function lookupApi(p) {
    const q = (p.get('q') || '').trim(), f = fold(q), N = 50;
    const res = {q, articles: [], groups: [], refs: [], authors: [], abbrevs: []};
    if (f.length < 2) return res;
    const m = await meta();
    const arts = m.lemmas.filter(r => r[4] === 'article' && m.fold.get(r[0]).includes(f))
      .sort((x, y) => (!m.fold.get(x[0]).startsWith(f)) - (!m.fold.get(y[0]).startsWith(f)) || cmpStr(m.fold.get(x[0]), m.fold.get(y[0])) || x[0] - y[0]).slice(0, N);
    res.articles = arts.map(r => ({id: r[0], lemma: r[1], band: r[2], col: r[3]}));
    const d = await load('authors');
    for (const r of arts) {
      const gs = d.groups.filter(g => g[2].some(x => x[0] === r[0])).map(g => ({id: g[0], name: g[1]}));
      if (gs.length) res.groups.push({id: r[0], lemma: r[1], groups: gs});
    }
    res.refs = await registerLookup(q, N, true);
    res.authors = (await authorsApi(new URLSearchParams({q}))).slice(0, N);
    const ab = (await load('extras')).abbrevs;
    res.abbrevs = [].concat(...ab.abbreviations.map(sec => sec.items.filter(it => fold(it.a).includes(f) || fold(it.text).includes(f)).map(it => ({a: it.a, text: it.text, sec: sec.title})))).slice(0, N);
    return res;
  }
  async function highlightApi(p) {
    const [tree, S] = await runSearchLight((p.get('q') || '').trim(), p);
    const hl = tree ? S.highlight(tree) : null;
    return {source: hl, case: S.cs};
  }
  async function runSearchLight(q, p) {
    let tree;
    try { tree = parse(q); } catch (e) { if (e.code) throw e; throw fail('bad_query', {detail: q}); }
    const S = new Search(p.get('tol') === '1', p.get('case') === '1', null);
    if (tree !== null) await S.prepare(tree);
    return [tree, S];
  }
  async function themeColumns(aid, rxs, cs, first) {
    const t = await load('t/' + aid), T = rxs.length, counts = new Map(), words = new Map();
    for (const [f, c] of [['b', 'cb'], ['n', 'cn'], ['l', 'cl']]) {
      const text = t[f] || '';
      // words in characters (code points), as Python counts
      const chars = Array.from(text), starts = [], u2c = [];
      chars.forEach((ch, i) => { for (let j = 0; j < ch.length; j++) u2c.push(i); });
      WORD_RX.lastIndex = 0; let mm;
      while ((mm = WORD_RX.exec(text))) starts.push(u2c[mm.index]);
      for (const st of starts) { const col = colAt(t[c], st, first); words.set(col, (words.get(col) || 0) + 1); }
      rxs.forEach((rx, i) => {
        for (const [a] of placesIn(text, rx, cs)) {
          const col = colAt(t[c], a, first);
          if (!counts.has(col)) counts.set(col, new Array(T).fill(0));
          counts.get(col)[i]++;
        }
      });
    }
    const out = [];
    for (const [col, arr] of counts) {
      const uses = arr.reduce((x, y) => x + y, 0), present = arr.filter(x => x).length;
      out.push([aid, col, uses / Math.max(words.get(col) || 0, 300) * 1000 * present / T, arr]);
    }
    return out;                     // sorted by the caller
  }
  // thematic search: the formula of hwph_serve.py api_theme / theme_rank
  async function themeApi(p) {
    const lines = (p.get('q') || '').split(/[\n;]+/).map(x => x.trim()).filter(Boolean).slice(0, 30);
    if (!lines.length) return {terms: [], items: [], total: 0};
    const m = await meta();
    const S = new Search(p.get('tol') === '1', p.get('case') === '1', null);
    const terms = [], per = [], leafsT = [];
    for (const line of lines) {
      let tree = null;
      const expr = line.startsWith('"') || !line.includes(' ') ? line : '"' + line.split('"').join('') + '"';   // several words: one phrase
      try { tree = parse(expr); } catch (e) { tree = null; }
      const lf = tree !== null ? leaves(tree).filter(([, n]) => !n).map(([l]) => l).slice(0, 1) : [];
      if (!lf.length || lf[0][0] === 'near') continue;
      await S.prepare(lf[0]);
      terms.push(line); per.push(await S.leafDocs(lf[0])); leafsT.push(lf[0]);
    }
    const T = per.length, arts = new Set();
    per.forEach(d => d.forEach((_, a) => arts.add(a)));
    let res = [];
    for (const a of arts) {
      const cs = per.map(d => d.has(a) ? d.get(a)[1] + d.get(a)[2] + d.get(a)[3] : 0);
      const uses = cs.reduce((x, y) => x + y, 0);
      if (!uses) continue;
      const L = m.lengths[a] || [0, 0, 0, 0, 0], words = Math.max(L[1] + L[2] + L[3], 300);
      const present = cs.filter(c => c).length;
      res.push([a, uses / words * 1000 * present / T, cs]);
    }
    res.sort((x, y) => y[1] - x[1] || x[0] - y[0]);
    const band = p.get('band') || '';
    if (band) res = res.filter(r => m.byId.get(r[0])[2] === band);
    const limit = Math.min(+(p.get('limit') || 100), 300);
    if (p.get('unit') === 'col') {
      // 'a passage of at least a page' on the CD: here a column of the book, within the best articles
      const rxs = leafsT.map(lf => new RegExp(leafRegex(lf, r => S.wordsOf(r), S.cs), 'gu'));
      let units = [];
      for (const [a] of res.slice(0, 80)) units = units.concat(await themeColumns(a, rxs, S.cs, m.byId.get(a)[3]));
      units.sort((x, y) => y[2] - x[2] || x[0] - y[0] || x[1] - y[1]);
      return {terms, items: units.slice(0, limit).map(([a, c, sc, cs]) => { const L = m.byId.get(a); return {id: a, lemma: L[1], band: L[2], col: c, score: sc, counts: cs}; }), total: units.length, cut: S.cut, unit: 'col'};
    }
    const items = res.slice(0, limit).map(([a, sc, cs]) => { const L = m.byId.get(a); return {id: a, lemma: L[1], band: L[2], col_from: L[3], col_to: L[5], score: sc, counts: cs}; });
    return {terms, items, total: res.length, cut: S.cut};
  }
  async function wordsApi(p) {
    const q = (p.get('q') || '').trim(), ws = wordTokens(q);
    if (!ws.length) return {q, items: []};
    const raw = ws[0], tol = p.get('tol') === '1';
    let list, cut = false;
    if (kindOf(raw) === 'plain' && !tol) list = [fold(raw)];
    else [list, cut] = await expandWord(raw, tol, 2000);
    const v = await vocab(), pos = new Map(v.terms.map((t, i) => [t, i]));
    const items = list.filter(t => pos.has(t)).map(t => ({term: t, docs: v.docs[pos.get(t)], cnt: v.cnt[pos.get(t)]}));
    items.sort((a, b) => b.docs - a.docs || cmpStr(a.term, b.term));
    return {q, items, cut};
  }

  /* ---------- register ---------- */
  async function registerRows(f) {
    const m = await meta();
    if (!f) return [];
    let names = f.length >= 2 ? [shardOf(f)] : m.reg_shards.filter(n => n.split('-')[0] === f.codePointAt(0).toString(16));
    names = names.filter(n => m.regSet.has(n));
    const sh = await loadAll(names.map(n => 'r/' + n));
    return [].concat(...sh);
  }
  async function registerLookup(term, limit, prefix) {
    const f = fold(term).trim();
    if (!f) return [];
    const all = (await registerRows(f)).filter(r => r[5] !== 'see' && r[5] !== 'author');
    let rows = prefix ? all.filter(r => r[8].startsWith(f)) : all.filter(r => r[8] === f);
    if (!rows.length && !prefix) rows = all.filter(r => r[8].startsWith(f));
    rows.sort((a, b) => (b[8] === f) - (a[8] === f) || (a[8] < b[8] ? -1 : a[8] > b[8] ? 1 : 0));
    return rows.slice(0, limit).map(r => ({term: r[0], target: r[1], qualifier: r[2], band: r[3], col: r[4], kind: r[5], id: r[6], lemma: r[7]}));
  }

  /* ---------- persons and graphs ---------- */
  let G = null;
  async function graph() {
    if (G) return G;
    const [g, persons] = await Promise.all([load('graph'), load('persons')]);
    G = {out: new Map(), inn: new Map(), byArt: new Map(), byPerson: new Map(), mentions: new Map(), P: new Map()};
    for (const [s, d, c] of g.xrefs) {
      if (!G.out.has(s)) G.out.set(s, []); G.out.get(s).push([d, c]);
      if (!G.inn.has(d)) G.inn.set(d, []); G.inn.get(d).push([s, c]);
    }
    for (const r of g.cites) {
      if (!G.byArt.has(r[0])) G.byArt.set(r[0], []); G.byArt.get(r[0]).push(r);
      if (!G.byPerson.has(r[1])) G.byPerson.set(r[1], []); G.byPerson.get(r[1]).push(r);
    }
    for (const r of g.mentions) { if (!G.mentions.has(r[0])) G.mentions.set(r[0], []); G.mentions.get(r[0]).push(r); }
    G.mentions.forEach(l => l.sort((a, b) => b[3] - a[3] || a[1] - b[1]));
    for (const p of persons) G.P.set(p[0], {id: p[0], name: p[1], fold: p[2], n_articles: p[3], n_body: p[4], n_notes: p[5], n_lit: p[6], editor: p[7], role: p[8]});
    G.persons = persons;
    return G;
  }
  async function patEntry(pid) { const d = await load('pat/' + Math.floor(pid / 500)); return d[pid] || [null, []]; }

  function cocited(pid, limit, scholars) {
    const mine = (G.byPerson.get(pid) || []).filter(r => r[2] + r[3] > 0);
    const me = mine.length || 1, shared = new Map();
    for (const r of mine) for (const o of G.byArt.get(r[0]) || []) {
      if (o[1] === pid || o[2] + o[3] <= 0) continue;
      const P = G.P.get(o[1]);
      if (!P || P.editor || (!scholars && P.role === 'scholar')) continue;
      shared.set(o[1], (shared.get(o[1]) || 0) + 1);
    }
    const res = [];
    for (const [id, sh] of shared) if (sh >= 2) { const P = G.P.get(id); res.push({id, name: P.name, shared: sh, role: P.role, score: sh / Math.sqrt(me * Math.max(P.n_articles, 1))}); }
    res.sort((a, b) => b.score - a.score || a.id - b.id);
    return res.slice(0, limit);
  }
  async function person(id, p) {
    const m = await meta(); await graph();
    const P = G.P.get(id); if (!P) throw fail('person_not_found');
    const [, variants] = await patEntry(id);
    const arts = (G.byPerson.get(id) || []).map(r => { const L = m.byId.get(r[0]); return {id: r[0], lemma: L[1], band: L[2], col: L[3], nb: r[2], nn: r[3], nl: r[4], f: m.fold.get(r[0])}; });
    arts.sort((a, b) => (b.nb + b.nn) - (a.nb + a.nn) || b.nl - a.nl || (a.f < b.f ? -1 : 1));
    arts.forEach(x => { delete x.f; });                       // only for sorting
    const surname = P.name.split(' ').pop();
    const lemmas = surname.length >= 4 ? m.lemmas.filter(r => r[4] === 'article' && m.fold.get(r[0]).indexOf(fold(surname)) >= 0)
      .sort((a, b) => (m.fold.get(a[0]) < m.fold.get(b[0]) ? -1 : 1)).slice(0, 30).map(r => ({id: r[0], lemma: r[1]})) : [];
    const {fold: _f, ...row} = P;                              // the name key is not part of the answer
    return Object.assign({}, row, {variants, articles: arts, cocited: cocited(id, 40, p.get('scholars') === '1'), lemmas});
  }
  async function persons(p) {
    await graph();
    const q = fold((p.get('q') || '').trim()), editors = p.get('editors') === '1', role = p.get('role') || '';
    const limit = Math.min(+(p.get('limit') || 200), 1000), out = [];
    for (const r of G.persons) {
      const P = G.P.get(r[0]);
      if (!editors && P.editor) continue;
      if (q && P.fold.indexOf(q) < 0) continue;
      if (['source', 'mixed', 'scholar'].includes(role) && P.role !== role) continue;
      if (role === 'thinkers' && P.role === 'scholar') continue;
      out.push({id: P.id, name: P.name, n_articles: P.n_articles, b: P.n_body, n: P.n_notes, l: P.n_lit, editor: P.editor, role: P.role});
      if (out.length >= limit) break;
    }
    return out;
  }
  const neighbours = a => [...new Set([...(G.out.get(a) || []).map(x => x[0]), ...(G.inn.get(a) || []).map(x => x[0])])].filter(x => x !== a);
  // one order for nodes and links, the same as hwph_serve.py: the drawing starts from it
  const cmp = (a, b) => (a < b ? -1 : a > b ? 1 : 0);
  const nodeOrder = (x, y) => x.level - y.level || cmp(x.kind, y.kind) || x.ref - y.ref;
  const linkOrder = (x, y) => cmp(x.kind, y.kind) || cmp(x.source, y.source) || cmp(x.target, y.target);
  async function graphArticle(aid, p) {
    const m = await meta(); await graph();
    const depth = p.get('depth') === '2' ? 2 : 1, withP = p.get('persons') !== '0', scholars = p.get('scholars') === '1', cap = 90;
    const level = new Map([[aid, 0]]);
    const first = neighbours(aid); first.forEach(a => { if (!level.has(a)) level.set(a, 1); });
    if (depth === 2) {
      const deg = new Map();
      for (const a of first) for (const b of neighbours(a)) if (!level.has(b)) deg.set(b, (deg.get(b) || 0) + 1);
      [...deg.entries()].sort((x, y) => y[1] - x[1] || x[0] - y[0]).slice(0, Math.max(0, cap - level.size)).forEach(([b]) => level.set(b, 2));
    }
    const ids = [...level.keys()], idset = new Set(ids);
    const nodes = ids.filter(a => m.byId.has(a)).map(a => { const L = m.byId.get(a); return {id: 'a' + a, ref: a, kind: 'article', label: L[1], level: level.get(a), sub: {k: 'loc', band: L[2], col: L[3]}}; });
    const links = [];
    for (const s of ids) for (const [d, c] of G.out.get(s) || []) if (idset.has(d) && d !== s) links.push({source: 'a' + s, target: 'a' + d, kind: 'xref', w: c});
    if (withP) {
      let top = (G.byArt.get(aid) || []).filter(r => { const P = G.P.get(r[1]); return P && !P.editor && P.role !== 'scholar' && r[2] + r[3] > 0; })
        .sort((a, b) => (b[2] + b[3]) - (a[2] + a[3]) || G.P.get(b[1]).n_articles - G.P.get(a[1]).n_articles || a[1] - b[1]).slice(0, 10).map(r => [r[1], r[2] + r[3]]);
      if (scholars) top = top.concat((G.byArt.get(aid) || []).filter(r => { const P = G.P.get(r[1]); return P && P.role === 'scholar'; })
        .sort((a, b) => (b[2] + b[3] + b[4]) - (a[2] + a[3] + a[4]) || G.P.get(b[1]).n_articles - G.P.get(a[1]).n_articles || a[1] - b[1]).slice(0, 8).map(r => [r[1], r[2] + r[3] + r[4]]));
      const pids = new Set(top.map(t => t[0]));
      for (const [pid, n] of top) { const P = G.P.get(pid); nodes.push({id: 'p' + pid, ref: pid, kind: 'person', role: P.role, label: P.name, level: 1, sub: {k: 'mentions', n}}); }
      for (const a of ids.filter(a => level.get(a) <= 1)) for (const r of G.byArt.get(a) || [])
        if (pids.has(r[1]) && r[2] + r[3] + r[4] > 0) links.push({source: 'a' + a, target: 'p' + r[1], kind: 'cite', w: 1});
    }
    return {center: 'a' + aid, nodes: nodes.sort(nodeOrder), links: links.sort(linkOrder), depth};
  }
  async function graphPerson(pid, p) {
    await graph();
    const me = G.P.get(pid); if (!me) throw fail('person_not_found');
    const n = Math.min(+(p.get('n') || 24), 60);
    const co = cocited(pid, n, p.get('scholars') === '1');
    const ids = [pid].concat(co.map(c => c.id)), idset = new Set(ids);
    const pair = new Map();
    const arts = new Set();
    ids.forEach(i => (G.byPerson.get(i) || []).forEach(r => { if (r[2] + r[3] > 0) arts.add(r[0]); }));
    for (const a of arts) {
      const here = (G.byArt.get(a) || []).filter(r => idset.has(r[1]) && r[2] + r[3] > 0).map(r => r[1]).sort((x, y) => x - y);
      for (let i = 0; i < here.length; i++) for (let j = i + 1; j < here.length; j++) { const k = here[i] + ',' + here[j]; pair.set(k, (pair.get(k) || 0) + 1); }
    }
    const nodes = [{id: 'p' + pid, ref: pid, kind: 'person', role: me.role, label: me.name, level: 0, sub: {k: 'articles', n: me.n_articles}}]
      .concat(co.map(c => ({id: 'p' + c.id, ref: c.id, kind: 'person', role: c.role, label: c.name, level: 1, sub: {k: 'shared', n: c.shared}})));
    const links = [];
    for (const [k, w] of pair) {
      if (w < 2) continue;
      const [a, b] = k.split(',').map(Number);
      const score = w / Math.sqrt(Math.max(G.P.get(a).n_articles, 1) * Math.max(G.P.get(b).n_articles, 1));
      links.push({source: 'p' + a, target: 'p' + b, kind: 'cocite', w, score});
    }
    const centre = links.filter(l => l.source === 'p' + pid || l.target === 'p' + pid);
    const others = links.filter(l => !centre.includes(l)).sort((x, y) => y.score - x.score || (x.source < y.source ? -1 : x.source > y.source ? 1 : x.target < y.target ? -1 : x.target > y.target ? 1 : 0)).slice(0, ids.length * 3);
    links.forEach(l => { delete l.score; });
    return {center: 'p' + pid, nodes: nodes.sort(nodeOrder), links: centre.concat(others).sort(linkOrder)};
  }
  async function expand(p) {
    const m = await meta(); await graph();
    const node = p.get('node') || '', what = p.get('what') || '', limit = Math.min(+(p.get('limit') || 60), 200), scholars = p.get('scholars') === '1';
    const mm = /^([ap])(\d+)$/.exec(node); if (!mm) throw fail('bad_node');
    const kind = mm[1], ref = +mm[2], items = [];
    let total = 0;
    const art = d => { const L = m.byId.get(d); return {id: 'a' + d, ref: d, kind: 'article', label: L[1], level: 2, sub: {k: 'loc', band: L[2], col: L[3]}}; };
    if (kind === 'a' && what === 'persons') {
      const rows = (G.byArt.get(ref) || []).filter(r => { const P = G.P.get(r[1]); return P && !P.editor && (scholars || (P.role !== 'scholar' && r[2] + r[3] > 0)); })
        .sort((a, b) => (G.P.get(a[1]).role === 'scholar') - (G.P.get(b[1]).role === 'scholar') || (b[2] * 2 + b[3] + b[4]) - (a[2] * 2 + a[3] + a[4]) || G.P.get(b[1]).n_articles - G.P.get(a[1]).n_articles || a[1] - b[1]);
      total = rows.length;
      for (const r of rows.slice(0, limit)) {
        const P = G.P.get(r[1]);
        items.push({node: {id: 'p' + P.id, ref: P.id, kind: 'person', role: P.role, label: P.name, level: 2, sub: {k: 'counts', b: r[2], n: r[3], l: r[4]}},
                    link: {source: node, target: 'p' + P.id, kind: 'cite', w: 1}});
      }
    } else if (kind === 'a' && what === 'concepts') {
      const rows = [], seen = new Set();
      (G.out.get(ref) || []).slice().sort((a, b) => b[1] - a[1] || a[0] - b[0]).forEach(([d]) => rows.push([d, 'xref', {k: 'xref'}]));
      (G.inn.get(ref) || []).slice().sort((a, b) => a[0] - b[0]).forEach(([s]) => rows.push([s, 'xref_in', {k: 'xref_in'}]));
      (G.mentions.get(ref) || []).forEach(r => rows.push([r[1], 'mention', {k: 'mention', n: r[2]}]));
      const uniq = rows.filter(([d]) => d !== ref && !seen.has(d) && seen.add(d) && m.byId.has(d));
      total = uniq.length;
      for (const [d, how, note] of uniq.slice(0, limit))
        items.push({node: art(d), how, note, link: how === 'xref_in' ? {source: 'a' + d, target: node, kind: 'xref', w: 1} : {source: node, target: 'a' + d, kind: how === 'xref' ? 'xref' : 'mention', w: 1}});
    } else if (kind === 'p' && what === 'articles') {
      const rows = (G.byPerson.get(ref) || []).slice().sort((a, b) => (b[2] * 2 + b[3]) - (a[2] * 2 + a[3]) || b[4] - a[4] || a[0] - b[0]);
      total = rows.length;
      for (const r of rows.slice(0, limit))
        items.push({node: art(r[0]), note: {k: 'counts', b: r[2], n: r[3], l: r[4]}, link: {source: 'a' + r[0], target: node, kind: 'cite', w: 1}});
    } else throw fail('bad_expand');
    return {items, total};
  }
  async function suggest(p) {
    const q = (p.get('q') || '').trim(), f = fold(q);
    if (f.length < 2) return {q, items: []};
    const m = await meta(); await graph();
    const items = [];
    let lem = m.lemmas.filter(r => m.fold.get(r[0]).startsWith(f)).sort((a, b) => m.fold.get(a[0]).length - m.fold.get(b[0]).length).slice(0, 7);
    if (lem.length < 7) lem = lem.concat(m.lemmas.filter(r => m.fold.get(r[0]).indexOf(f) > 0).sort((a, b) => m.fold.get(a[0]).length - m.fold.get(b[0]).length).slice(0, 7 - lem.length));
    lem.forEach(r => items.push({type: 'article', id: r[0], label: r[1], band: r[2], col: r[3]}));
    const per = [];
    for (const r of G.persons) {
      const P = G.P.get(r[0]);
      if (P.editor || P.n_articles < 2) continue;
      if (P.fold.startsWith(f) || P.fold.indexOf(' ' + f) >= 0) per.push(P);
    }
    per.sort((a, b) => (a.role === 'scholar') - (b.role === 'scholar') || b.n_articles - a.n_articles || a.id - b.id);
    per.slice(0, 5).forEach(P => items.push({type: 'person', id: P.id, label: P.name, role: P.role, n: P.n_articles}));
    const shown = new Set(items.map(x => x.label)), by = new Map();
    for (const r of await registerRows(f)) {
      if (!r[8].startsWith(f) || !['ref', 'main'].includes(r[5]) || !r[6]) continue;
      if (!by.has(r[8])) by.set(r[8], {term: r[0], id: r[6], lemma: r[7], c: 0});
      by.get(r[8]).c++;
    }
    [...by.entries()].sort((a, b) => a[0].length - b[0].length || (a[0] < b[0] ? -1 : 1)).slice(0, 5).forEach(([, x]) => {
      if (!shown.has(x.term)) items.push({type: 'register', term: x.term, id: x.id, label: x.term, lemma: x.lemma, more: x.c - 1});
    });
    return {q, items};
  }
  const BL = '(?<![\\p{L}\\p{N}])', BR = '(?![\\p{L}\\p{N}])';
  const jsEsc = t => t.replace(/[.*+?^${}()|[\]\\/]/g, '\\$&');
  async function pattern(p) {
    const m = await meta();
    if (p.get('pid')) {
      await graph();
      const pid = +p.get('pid'), P = G.P.get(pid); if (!P) throw fail('person_not_found');
      const [src] = await patEntry(pid);
      return {source: src, label: P.name, kind: 'person', id: pid};
    }
    if (!p.get('concept')) throw fail('bad_pattern');
    const cid = +p.get('concept'), L = m.byId.get(cid); if (!L) throw fail('article_not_found');
    const parts = L[1].split(/[,;/(]/).map(x => x.trim());
    const forms = [...new Set(parts.filter((h, k) => h && h.length >= 4 && h[0] === h[0].toUpperCase() && h[0] !== h[0].toLowerCase() && (k === 0 || !h.includes(' '))))]
      .sort((a, b) => b.length - a.length || (a < b ? -1 : a > b ? 1 : 0)).map(f => f.split(/\s+/).map(jsEsc).join('\\s+'));
    return {source: BL + '(?:' + forms.join('|') + ')(?:n|en|s|es|e|er|ern)?' + BR, label: L[1], kind: 'concept', id: cid};
  }

  // names and citations are needed by the first as-you-type suggestion: read them while the reader looks around
  window.addEventListener('load', () => setTimeout(() => { meta().then(graph).catch(() => {}); }, 1200));

  /* ---------- subject groups and authors (vol. 13) ---------- */
  async function groupsApi() {
    const d = await load('authors');
    return d.groups.map(([id, name, items]) => ({id, name, n: new Set(items.filter(x => x[0] !== null).map(x => x[0])).size}));
  }
  async function groupApi(gid) {
    const m = await meta(), d = await load('authors');
    const g = d.groups.find(x => x[0] === gid);
    if (!g) throw fail('group_not_found');
    return {id: g[0], name: g[1], items: g[2].map(([aid, label]) => {
      const L = aid !== null ? m.byId.get(aid) : null;
      return {id: aid, label, lemma: L ? L[1] : null, band: L ? L[2] : null, col: L ? L[3] : null};
    })};
  }
  async function authorsApi(p) {
    const q = fold((p.get('q') || '').trim()), d = await load('authors'), by = new Map();
    for (const [name, dst] of d.authors) {
      if (!by.has(name)) by.set(name, new Set());
      if (dst !== null) by.get(name).add(dst);
    }
    const out = [...by.entries()].filter(([n]) => !q || fold(n).includes(q)).map(([name, s]) => ({name, n: s.size}));
    return out.sort((a, b) => cmpStr(fold(a.name), fold(b.name)) || cmpStr(a.name, b.name));
  }
  async function authorApi(p) {
    const name = p.get('name') || '', m = await meta(), d = await load('authors');
    const rows = d.authors.filter(r => r[0] === name);
    if (!rows.length) throw fail('author_not_found');
    return {name, items: rows.map(([, dst, target, band, col]) => ({id: dst, lemma: dst !== null && m.byId.has(dst) ? m.byId.get(dst)[1] : null, target, band, col}))};
  }

  /* ---------- the same paths the server answers ---------- */
  window.HWPH_API = async function (path) {
    const u = new URL(path, 'http://x/'), p = u.searchParams, r = u.pathname;
    let m;
    if (r === '/api/info') { const mt = await meta(); return Object.assign({}, mt.info, {engine: 'static'}); }
    if (r === '/api/lemmas') { const mt = await meta(); return mt.lemmas.map(x => [x[0], x[1], x[2], x[3], x[4], x[5]]); }
    if ((m = /^\/api\/article\/(\d+)$/.exec(r))) return load('a/' + m[1]).catch(() => { throw fail('article_not_found'); });
    if (r === '/api/search') return search(p);
    if (r === '/api/highlight') return highlightApi(p);
    if (r === '/api/abbrevs') return load('extras').then(d => d.abbrevs);
    if (r === '/api/checklist') return load('extras').then(d => d.checklist);
    if (r === '/api/groups') return groupsApi();
    if ((m = /^\/api\/group\/(\d+)$/.exec(r))) return groupApi(+m[1]);
    if (r === '/api/authors') return authorsApi(p);
    if (r === '/api/author') return authorApi(p);
    if (r === '/api/words') return wordsApi(p);
    if (r === '/api/theme') return themeApi(p);
    if (r === '/api/places') return placesApi(p);
    if (r === '/api/lookup') return lookupApi(p);
    if (r === '/api/register') return registerLookup(p.get('q') || '', 300, true);
    if ((m = /^\/api\/person\/(\d+)$/.exec(r))) return person(+m[1], p);
    if (r === '/api/persons') return persons(p);
    if ((m = /^\/api\/graph\/a\/(\d+)$/.exec(r))) return graphArticle(+m[1], p);
    if ((m = /^\/api\/graph\/p\/(\d+)$/.exec(r))) return graphPerson(+m[1], p);
    if (r === '/api/expand') return expand(p);
    if (r === '/api/suggest') return suggest(p);
    if (r === '/api/pattern') return pattern(p);
    if (r === '/api/ping') return {ok: true};
    throw fail('not_found', {path: r});
  };
})();

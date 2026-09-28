// ==UserScript==
// @name         자막 도우미 (Subtitle Helper)
// @namespace    https://github.com/xixili0124-star/claude-save
// @version      1.0.0
// @description  영상 위에 자막 파일(.srt/.vtt/.smi/.ass) 또는 자동 한글 번역 자막을 표시합니다.
// @downloadURL  https://cdn.jsdelivr.net/gh/xixili0124-star/subtitle-helper@main/subtitle-helper.user.js
// @updateURL    https://cdn.jsdelivr.net/gh/xixili0124-star/subtitle-helper@main/subtitle-helper.user.js
// @match        *://*/*
// @grant        none
// @run-at       document-idle
// ==/UserScript==

/*
 * 삼성 인터넷에서는 북마크(북마클릿)로 실행하고,
 * 파이어폭스 + Violentmonkey/Tampermonkey 에서는 유저스크립트로 자동 실행됩니다.
 * 한 번 더 실행하면 설정 창이 열리고 닫힙니다.
 */
(function () {
  'use strict';

  if (window.__subHelper) { window.__subHelper.togglePanel(); return; }

  var VERSION = '1.0.0';
  var IS_USERSCRIPT = typeof GM_info !== 'undefined';
  var LS_KEY = 'subhelper:settings';
  var nativeFetch = window.fetch ? window.fetch.bind(window) : null;

  // ---------------------------------------------------------------------------
  // 설정
  // ---------------------------------------------------------------------------
  var DEFAULTS = { mode: 'translate', offset: 0, fontSize: 20, bottom: 8, showOriginal: false, lang: 'ko' };
  var settings = loadSettings();

  function loadSettings() {
    var s = {};
    try { s = JSON.parse(localStorage.getItem(LS_KEY) || '{}') || {}; } catch (e) { /* 저장소 사용 불가 */ }
    var out = {};
    Object.keys(DEFAULTS).forEach(function (k) { out[k] = k in s ? s[k] : DEFAULTS[k]; });
    return out;
  }
  function saveSettings() {
    try { localStorage.setItem(LS_KEY, JSON.stringify(settings)); } catch (e) { /* 무시 */ }
  }

  // ---------------------------------------------------------------------------
  // 상태
  // ---------------------------------------------------------------------------
  var state = {
    video: null,
    fileCues: [],
    fileName: '',
    sources: new Map(),      // key -> { key, label, cues, score, ts }
    activeKey: null,
    userPickedSource: false,
    liveText: '',
    hiddenTracks: [],
    seenUrls: new Set()
  };

  var tr = { cache: new Map(), inflight: new Set(), gen: 0, done: 0, total: 0, error: '' };

  // ---------------------------------------------------------------------------
  // 자막 파싱
  // ---------------------------------------------------------------------------
  var ENTITIES = { amp: '&', lt: '<', gt: '>', quot: '"', apos: "'", nbsp: ' ', '#39': "'" };

  function decodeEntities(s) {
    return s.replace(/&(#x[0-9a-f]+|#\d+|[a-z]+);/gi, function (m, e) {
      var k = e.toLowerCase();
      if (k in ENTITIES) return ENTITIES[k];
      if (k[0] === '#') {
        var n = k[1] === 'x' ? parseInt(k.slice(2), 16) : parseInt(k.slice(1), 10);
        return isNaN(n) ? m : String.fromCodePoint(n);
      }
      return m;
    });
  }

  function cleanText(s) {
    s = s.replace(/<br\s*\/?>/gi, '\n')
      .replace(/<[^>]*>/g, '')
      .replace(/\{\\[^}]*\}/g, '');
    s = decodeEntities(s);
    return s.split('\n').map(function (l) { return l.replace(/\s+/g, ' ').trim(); })
      .filter(Boolean).join('\n');
  }

  function parseTime(s) {
    var m = String(s).trim().match(/^(?:(\d+):)?(\d{1,2}):(\d{1,2})(?:[.,](\d+))?$/);
    if (!m) return NaN;
    var frac = m[4] ? parseFloat('0.' + m[4]) : 0;
    return (+(m[1] || 0)) * 3600 + (+m[2]) * 60 + (+m[3]) + frac;
  }

  function sortCues(cues) {
    return cues.filter(function (c) { return isFinite(c.start) && isFinite(c.end) && c.end > c.start && c.text; })
      .sort(function (a, b) { return a.start - b.start; });
  }

  var TIME_RE = /((?:\d+:)?\d{1,2}:\d{1,2}(?:[.,]\d+)?)\s*-->\s*((?:\d+:)?\d{1,2}:\d{1,2}(?:[.,]\d+)?)/;

  function parseSrtVtt(text) {
    var lines = text.split('\n');
    var cues = [];
    var i = 0;
    while (i < lines.length) {
      var m = lines[i].match(TIME_RE);
      if (!m) { i++; continue; }
      var start = parseTime(m[1]);
      var end = parseTime(m[2]);
      var buf = [];
      i++;
      while (i < lines.length && lines[i].trim() !== '') {
        if (TIME_RE.test(lines[i])) {
          // 빈 줄 없이 다음 자막이 이어진 경우: 번호 줄은 제외
          if (buf.length && /^\d+$/.test(buf[buf.length - 1].trim())) buf.pop();
          break;
        }
        buf.push(lines[i]);
        i++;
      }
      cues.push({ start: start, end: end, text: cleanText(buf.join('\n')) });
    }
    return sortCues(cues);
  }

  function parseSmi(text) {
    var syncRe = /<sync\b[^>]*?start\s*=\s*["']?(\d+)[^>]*>/gi;
    var marks = [];
    var m;
    while ((m = syncRe.exec(text))) marks.push({ t: +m[1] / 1000, idx: m.index, end: syncRe.lastIndex });

    var byClass = {};
    function push(cls, t, body) {
      (byClass[cls] = byClass[cls] || []).push({ t: t, text: cleanText(body) });
    }
    marks.forEach(function (mk, k) {
      var body = text.slice(mk.end, k + 1 < marks.length ? marks[k + 1].idx : text.length)
        .replace(/<\/body>[\s\S]*$/i, '');
      var pRe = /<p\b([^>]*)>([\s\S]*?)(?=<p\b|$)/gi;
      var pm;
      var found = false;
      while ((pm = pRe.exec(body))) {
        found = true;
        var cm = pm[1].match(/class\s*=\s*["']?([\w-]+)/i);
        push(cm ? cm[1].toUpperCase() : 'DEFAULT', mk.t, pm[2]);
      }
      if (!found) push('DEFAULT', mk.t, body);
    });

    // 한국어 클래스(KRCC 등) 우선, 없으면 내용이 가장 많은 클래스
    var classes = Object.keys(byClass);
    var chosen = classes.filter(function (c) { return /^KR/.test(c); })[0];
    if (!chosen) {
      chosen = classes.sort(function (a, b) {
        return count(byClass[b]) - count(byClass[a]);
      })[0];
    }
    function count(list) { return list.filter(function (e) { return e.text; }).length; }
    if (!chosen) return [];

    var entries = byClass[chosen].sort(function (a, b) { return a.t - b.t; });
    var cues = [];
    entries.forEach(function (e, k) {
      if (!e.text) return;
      var next = entries[k + 1];
      cues.push({ start: e.t, end: next ? next.t : e.t + 5, text: e.text });
    });
    return sortCues(cues);
  }

  function parseAss(text) {
    var lines = text.split('\n');
    var fmt = null;
    var inEvents = false;
    var cues = [];
    lines.forEach(function (line) {
      if (/^\s*\[events\]/i.test(line)) { inEvents = true; return; }
      if (/^\s*\[/.test(line)) { inEvents = false; return; }
      if (!inEvents) return;
      if (/^format:/i.test(line)) {
        fmt = line.slice(7).split(',').map(function (s) { return s.trim().toLowerCase(); });
        return;
      }
      if (!fmt || !/^dialogue:/i.test(line)) return;
      var parts = line.slice(9).split(',');
      var n = fmt.length;
      var f = parts.slice(0, n - 1).map(function (s) { return s.trim(); });
      f.push(parts.slice(n - 1).join(','));
      var get = function (k) { return f[fmt.indexOf(k)] || ''; };
      var body = get('text').replace(/\{[^}]*\}/g, '').replace(/\\N/gi, '\n').replace(/\\h/g, ' ');
      cues.push({ start: parseTime(get('start')), end: parseTime(get('end')), text: cleanText(body) });
    });
    return sortCues(cues);
  }

  function parseSubtitle(text) {
    text = text.replace(/^﻿/, '').replace(/\r\n?/g, '\n');
    if (/\[script info\]|\[events\]/i.test(text)) return parseAss(text);
    if (/<sami|<sync\b/i.test(text)) return parseSmi(text);
    return parseSrtVtt(text);
  }

  function decodeBuffer(buf) {
    var u8 = new Uint8Array(buf);
    if (u8[0] === 0xFF && u8[1] === 0xFE) return new TextDecoder('utf-16le').decode(buf);
    if (u8[0] === 0xFE && u8[1] === 0xFF) return new TextDecoder('utf-16be').decode(buf);
    try { return new TextDecoder('utf-8', { fatal: true }).decode(buf); } catch (e) {
      return new TextDecoder('euc-kr').decode(buf); // 한국어 SMI 는 대부분 CP949
    }
  }

  function isThumbnailTrack(cues) {
    var img = cues.filter(function (c) { return /#xywh=|\.(jpe?g|png|webp)\b/i.test(c.text); }).length;
    return img > cues.length / 2;
  }

  function activeCues(cues, t) {
    var out = [];
    for (var i = 0; i < cues.length; i++) {
      var c = cues[i];
      if (c.start > t) break;
      if (t < c.end) out.push(c);
    }
    return out;
  }

  // ---------------------------------------------------------------------------
  // 원문 자막 찾기 (번역 모드)
  // ---------------------------------------------------------------------------
  var SUB_URL_RE = /\.(vtt|webvtt|srt|ass|ssa)(\?|#|$)|subtitle|caption/i;
  var SEGMENT_RE = /[\/_-]\d+\.(web)?vtt(\?|#|$)/i;

  function sourceScore(key, cues) {
    var s = Math.min(cues.length, 500) / 10;
    if (/eng|english|[\/_.=-]en([\/_.-]|$)/i.test(key)) s += 100;
    return s;
  }

  function addSource(key, label, cues) {
    if (!cues.length || isThumbnailTrack(cues)) return;
    var existing = state.sources.get(key);
    if (existing) {
      // HLS 조각 자막은 합치기
      var seen = new Set(existing.cues.map(function (c) { return c.start + '|' + c.text; }));
      cues.forEach(function (c) { if (!seen.has(c.start + '|' + c.text)) existing.cues.push(c); });
      existing.cues = sortCues(existing.cues);
      existing.score = sourceScore(key, existing.cues);
    } else {
      state.sources.set(key, { key: key, label: label, cues: cues, score: sourceScore(key, cues), ts: Date.now() });
    }
    if (!state.userPickedSource) {
      var best = null;
      state.sources.forEach(function (s) { if (!best || s.score > best.score) best = s; });
      if (best && best.key !== state.activeKey) state.activeKey = best.key;
    }
    onSourceChanged();
  }

  function addSourceFromText(url, text) {
    if (!text || text.length > 5e6) return;
    var cues;
    try { cues = parseSubtitle(text); } catch (e) { return; }
    var key = SEGMENT_RE.test(url) ? url.replace(/[^\/]*$/, '*') : url;
    var name = decodeURIComponent((url.split('?')[0].split('/').pop() || url)).slice(0, 40);
    addSource(key, name, cues);
  }

  function fetchSubUrl(url) {
    if (!nativeFetch || state.seenUrls.has(url) || /^blob:|^data:/.test(url)) return;
    state.seenUrls.add(url);
    nativeFetch(url).then(function (r) { return r.ok ? r.text() : ''; })
      .then(function (t) { addSourceFromText(url, t); })
      .catch(function () { /* 교차 출처 차단 등 */ });
  }

  function scanPerformance() {
    try {
      performance.getEntriesByType('resource').forEach(function (e) {
        if (SUB_URL_RE.test(e.name)) fetchSubUrl(e.name);
      });
    } catch (e) { /* 무시 */ }
  }

  function watchNetwork() {
    try {
      new PerformanceObserver(function (list) {
        list.getEntries().forEach(function (e) { if (SUB_URL_RE.test(e.name)) fetchSubUrl(e.name); });
      }).observe({ type: 'resource', buffered: true });
    } catch (e) { /* 미지원 브라우저 */ }

    var origOpen = XMLHttpRequest.prototype.open;
    var origSend = XMLHttpRequest.prototype.send;
    XMLHttpRequest.prototype.open = function (method, url) {
      this.__shUrl = String(url);
      return origOpen.apply(this, arguments);
    };
    XMLHttpRequest.prototype.send = function () {
      var xhr = this;
      if (SUB_URL_RE.test(xhr.__shUrl || '')) {
        xhr.addEventListener('load', function () {
          try {
            if (xhr.responseType === '' || xhr.responseType === 'text') {
              state.seenUrls.add(xhr.__shUrl);
              addSourceFromText(xhr.__shUrl, xhr.responseText);
            }
          } catch (e) { /* 무시 */ }
        });
      }
      return origSend.apply(this, arguments);
    };
  }

  function scanTextTracks() {
    var v = state.video;
    if (!v || !v.textTracks) return;
    for (var i = 0; i < v.textTracks.length; i++) {
      var track = v.textTracks[i];
      if (track.kind !== 'subtitles' && track.kind !== 'captions') continue;
      if (track.mode === 'disabled') {
        track.mode = 'hidden';
        state.hiddenTracks.push({ track: track, mode: 'disabled' });
      }
      if (!track.cues || !track.cues.length) continue;
      var cues = [];
      for (var j = 0; j < track.cues.length; j++) {
        var c = track.cues[j];
        cues.push({ start: c.startTime, end: c.endTime, text: cleanText(c.text || '') });
      }
      var key = 'track:' + i + ':' + (track.language || track.label || '');
      var prev = state.sources.get(key);
      if (!prev || prev.cues.length !== cues.length) {
        state.sources.delete(key);
        addSource(key, '영상 내장 자막 ' + (track.label || track.language || i), sortCues(cues));
      }
    }
  }

  // 화면에 직접 그려지는 자막(JW Player, video.js 등)을 읽는 예비 방식
  var CAPTION_SEL = [
    '.jw-text-track-container', '.jw-captions', '.vjs-text-track-display', '.plyr__captions',
    '.art-subtitle', '.shaka-text-container', '.dplayer-subtitle', '.fp-captions',
    '.mejs__captions-layer', '.vds-captions', 'media-captions', '.ytp-caption-window-container'
  ].join(',');

  function readDomCaption() {
    var nodes = document.querySelectorAll(CAPTION_SEL);
    for (var i = 0; i < nodes.length; i++) {
      var t = (nodes[i].innerText || nodes[i].textContent || '').trim();
      if (t) return cleanText(t);
    }
    return '';
  }

  function currentSource() {
    return state.activeKey ? state.sources.get(state.activeKey) : null;
  }

  function onSourceChanged() {
    ui.refresh();
    if (settings.mode === 'translate') {
      var src = currentSource();
      if (src) translateAll(src.cues);
    }
  }

  // ---------------------------------------------------------------------------
  // 번역 (구글 번역 무료 경로)
  // ---------------------------------------------------------------------------
  function sleep(ms) { return new Promise(function (r) { setTimeout(r, ms); }); }

  function gtx(texts) {
    var q = texts.map(function (t) { return t.replace(/\s*\n\s*/g, ' '); }).join('\n');
    var url = 'https://translate.googleapis.com/translate_a/single?client=gtx&sl=auto&tl=' +
      encodeURIComponent(settings.lang) + '&dt=t&q=' + encodeURIComponent(q);
    return nativeFetch(url, { credentials: 'omit' }).then(function (r) {
      if (!r.ok) { var err = new Error('HTTP ' + r.status); err.status = r.status; throw err; }
      return r.json();
    }).then(function (data) {
      var out = (data[0] || []).map(function (seg) { return seg[0] || ''; }).join('');
      var lines = out.split('\n').map(function (s) { return s.trim(); });
      if (lines.length !== texts.length) throw new Error('mismatch');
      return lines;
    });
  }

  function clients5(text) {
    var url = 'https://clients5.google.com/translate_a/t?client=dict-chrome-ex&sl=auto&tl=' +
      encodeURIComponent(settings.lang) + '&q=' + encodeURIComponent(text.replace(/\s*\n\s*/g, ' '));
    return nativeFetch(url, { credentials: 'omit' }).then(function (r) {
      if (!r.ok) throw new Error('HTTP ' + r.status);
      return r.json();
    }).then(function (d) {
      var x = Array.isArray(d) ? d[0] : d;
      if (Array.isArray(x)) x = x[0];
      if (typeof x !== 'string') throw new Error('bad response');
      return x;
    });
  }

  async function translateBatch(texts) {
    try {
      return await gtx(texts);
    } catch (e) {
      if (e.status === 429) throw e;
      if (e.message !== 'mismatch' && texts.length === 1) return [await clients5(texts[0])];
    }
    // 묶음 번역이 어긋나면 한 줄씩
    var out = [];
    for (var i = 0; i < texts.length; i++) {
      try { out.push((await gtx([texts[i]]))[0]); } catch (e) { out.push(await clients5(texts[i])); }
    }
    return out;
  }

  async function translateAll(cues) {
    var gen = ++tr.gen;
    var now = state.video ? state.video.currentTime - settings.offset : 0;
    var ahead = cues.filter(function (c) { return c.end >= now - 2; });
    var behind = cues.filter(function (c) { return c.end < now - 2; }).reverse();
    var order = [];
    var seen = new Set();
    ahead.concat(behind).forEach(function (c) {
      if (!seen.has(c.text)) { seen.add(c.text); order.push(c.text); }
    });
    tr.total = order.length;
    tr.done = order.filter(function (t) { return tr.cache.has(t); }).length;
    tr.error = '';
    var queue = order.filter(function (t) { return !tr.cache.has(t); });
    ui.refresh();

    var retries = 0;
    while (queue.length) {
      if (gen !== tr.gen || settings.mode !== 'translate') return;
      var batch = [];
      var chars = 0;
      while (queue.length && batch.length < 20 && chars + queue[0].length < 1200) {
        chars += queue[0].length;
        batch.push(queue.shift());
      }
      if (!batch.length) batch.push(queue.shift());
      try {
        var res = await translateBatch(batch);
        batch.forEach(function (t, k) { tr.cache.set(t, res[k]); });
        tr.done += batch.length;
        tr.error = '';
        retries = 0;
      } catch (e) {
        queue = batch.concat(queue);
        retries++;
        tr.error = e.status === 429 ? '번역 요청이 많아 잠시 대기 중…' :
          '번역 서버 연결 실패 (' + e.message + '). 이 사이트가 외부 연결을 막았을 수 있습니다.';
        ui.refresh();
        if (retries > 5) return;
        await sleep(e.status === 429 ? 8000 : 3000);
        continue;
      }
      ui.refresh();
      await sleep(150);
    }
  }

  function translateLive(text) {
    if (!text || tr.cache.has(text) || tr.inflight.has(text)) return;
    tr.inflight.add(text);
    translateBatch([text]).then(function (res) {
      tr.cache.set(text, res[0]);
      tr.error = '';
    }).catch(function (e) {
      tr.error = '번역 서버 연결 실패 (' + e.message + ')';
    }).then(function () {
      tr.inflight.delete(text);
      ui.refresh();
    });
  }

  // ---------------------------------------------------------------------------
  // 영상 찾기
  // ---------------------------------------------------------------------------
  function allVideos() {
    var list = Array.prototype.slice.call(document.querySelectorAll('video'));
    document.querySelectorAll('iframe').forEach(function (f) {
      try { if (f.contentDocument) list = list.concat(Array.prototype.slice.call(f.contentDocument.querySelectorAll('video'))); } catch (e) { /* 다른 도메인 */ }
    });
    return list;
  }

  function pickVideo() {
    var best = null;
    var bestScore = 0;
    allVideos().forEach(function (v) {
      var r = v.getBoundingClientRect();
      var area = r.width * r.height;
      if (area < 100 * 60) return;
      var score = area * (v.paused ? 1 : 4);
      if (score > bestScore) { best = v; bestScore = score; }
    });
    if (best !== state.video) {
      if (state.video) state.video.removeEventListener('seeked', onSeeked);
      state.video = best;
      if (best) best.addEventListener('seeked', onSeeked);
      applyHiding();
      ui.refresh();
    }
  }

  function onSeeked() {
    var src = currentSource();
    if (settings.mode === 'translate' && src) translateAll(src.cues);
  }

  function foreignFrames() {
    var out = [];
    document.querySelectorAll('iframe').forEach(function (f) {
      var r = f.getBoundingClientRect();
      if (r.width < 200 || r.height < 100 || !f.src || /^about:|^javascript:/.test(f.src)) return;
      try { if (f.contentDocument) return; } catch (e) { /* 다른 도메인 */ }
      out.push(f.src);
    });
    return out;
  }

  // ---------------------------------------------------------------------------
  // 원래 자막 숨기기
  // ---------------------------------------------------------------------------
  var pageSheet = null;
  var pageStyleEl = null;
  var HIDE_CSS = CAPTION_SEL + '{opacity:0 !important}' +
    ' video::cue{color:transparent !important;background:transparent !important}';

  function setPageCss(css) {
    try {
      if (!pageSheet) {
        pageSheet = new CSSStyleSheet();
        document.adoptedStyleSheets = document.adoptedStyleSheets.concat([pageSheet]);
      }
      pageSheet.replaceSync(css);
      return;
    } catch (e) { /* 구형 브라우저 */ }
    if (!pageStyleEl) {
      pageStyleEl = document.createElement('style');
      (document.head || document.documentElement).appendChild(pageStyleEl);
    }
    pageStyleEl.textContent = css;
  }

  function applyHiding() {
    var on = settings.mode !== 'off';
    setPageCss(on ? HIDE_CSS : '');
    var v = state.video;
    if (!v || !v.textTracks) return;
    for (var i = 0; i < v.textTracks.length; i++) {
      var t = v.textTracks[i];
      if (on && t.mode === 'showing') {
        t.mode = 'hidden';
        state.hiddenTracks.push({ track: t, mode: 'showing' });
      }
    }
    if (!on) {
      state.hiddenTracks.forEach(function (h) { try { h.track.mode = h.mode; } catch (e) { /* 무시 */ } });
      state.hiddenTracks = [];
    }
  }

  // ---------------------------------------------------------------------------
  // 화면 (Shadow DOM 으로 사이트 스타일과 분리)
  // ---------------------------------------------------------------------------
  var CSS = [
    ':host{all:initial}',
    '*{box-sizing:border-box;font-family:system-ui,-apple-system,"Noto Sans KR","Malgun Gothic",sans-serif}',
    '.ov{position:fixed;pointer-events:none;display:flex;flex-direction:column;justify-content:flex-end;align-items:center;overflow:hidden}',
    '.line{max-width:92%;text-align:center;white-space:pre-line;color:#fff;font-weight:600;line-height:1.35;padding:2px 8px;margin-top:3px;border-radius:4px;background:rgba(0,0,0,.45);text-shadow:0 0 3px #000,0 0 3px #000,1px 1px 2px #000}',
    '.line.orig{color:#ffe08a;font-weight:500;font-size:.75em}',
    '.line.pending{color:#d0d0d0}',
    '.fab{position:fixed;right:10px;top:42%;width:46px;height:46px;border-radius:50%;border:none;background:rgba(20,20,20,.72);color:#fff;font-size:13px;font-weight:700;box-shadow:0 2px 8px rgba(0,0,0,.4);pointer-events:auto;padding:0}',
    '.fab.on{background:rgba(37,99,235,.85)}',
    '.panel{position:fixed;right:10px;bottom:10px;width:min(340px,calc(100vw - 20px));max-height:calc(100vh - 20px);overflow:auto;background:#1e1f22;color:#eee;border-radius:12px;padding:12px;font-size:14px;line-height:1.4;box-shadow:0 6px 24px rgba(0,0,0,.5);pointer-events:auto}',
    '.hidden{display:none !important}',
    '.hd{display:flex;justify-content:space-between;align-items:center;font-weight:700;font-size:15px}',
    '.row{display:flex;align-items:center;gap:4px;margin:8px 0;flex-wrap:wrap}',
    '.lbl{min-width:36px;color:#bbb}',
    '.val{min-width:52px;text-align:center;font-variant-numeric:tabular-nums}',
    'button.b{min-height:36px;min-width:38px;padding:0 8px;border-radius:8px;border:1px solid #444;background:#2c2e33;color:#eee;font-size:14px}',
    'button.b:active,.seg button:active{filter:brightness(1.3)}',
    '.seg{display:flex;border:1px solid #444;border-radius:9px;overflow:hidden;margin:10px 0}',
    '.seg button{flex:1;min-height:40px;border:0;background:#2c2e33;color:#ccc;font-size:14px}',
    '.seg button.on{background:#2563eb;color:#fff;font-weight:700}',
    '.muted{color:#9aa0a6;font-size:12px;word-break:break-all}',
    '.err{color:#ff8a80;font-size:12px;word-break:break-all}',
    'select{flex:1;min-height:36px;background:#2c2e33;color:#eee;border:1px solid #444;border-radius:8px;min-width:0;font-size:13px}',
    'label.ck{display:flex;align-items:center;gap:6px}',
    'hr{border:0;border-top:1px solid #333;margin:10px 0}',
    'a{color:#8ab4f8}'
  ].join('\n');

  function el(tag, props, children) {
    var e = document.createElement(tag);
    if (props) Object.keys(props).forEach(function (k) {
      if (k === 'on') Object.keys(props.on).forEach(function (ev) { e.addEventListener(ev, props.on[ev]); });
      else if (k === 'className') e.className = props[k];
      else if (k === 'text') e.textContent = props[k];
      else e.setAttribute(k, props[k]);
    });
    (children || []).forEach(function (c) { if (c) e.appendChild(typeof c === 'string' ? document.createTextNode(c) : c); });
    return e;
  }

  var ui = (function () {
    var host = document.createElement('div');
    host.id = 'subhelper-host';
    host.style.cssText = 'all:initial;position:fixed;left:0;top:0;width:0;height:0;z-index:2147483647;';
    var root = host.attachShadow({ mode: 'open' });
    try {
      var sheet = new CSSStyleSheet();
      sheet.replaceSync(CSS);
      root.adoptedStyleSheets = [sheet];
    } catch (e) {
      root.appendChild(el('style', { text: CSS }));
    }

    var overlay = el('div', { className: 'ov' });
    var fab = el('button', { className: 'fab', text: '자막', title: '자막 도우미', on: { click: function () { togglePanel(); } } });

    // --- 패널 ---
    var modeBtns = {};
    var seg = el('div', { className: 'seg' }, [['off', '끄기'], ['file', '자막 파일'], ['translate', '자동 번역']].map(function (p) {
      var b = el('button', { text: p[1], on: { click: function () { setMode(p[0]); } } });
      modeBtns[p[0]] = b;
      return b;
    }));

    var fileInput = el('input', { type: 'file', accept: '.srt,.vtt,.smi,.sami,.ass,.ssa,.txt', className: 'hidden' });
    fileInput.addEventListener('change', function () {
      var f = fileInput.files && fileInput.files[0];
      if (f) loadFile(f);
      fileInput.value = '';
    });
    var fileInfo = el('div', { className: 'muted' });
    var fileSec = el('div', null, [
      el('div', { className: 'row' }, [
        el('button', { className: 'b', text: '📂 자막 파일 선택', on: { click: function () { fileInput.click(); } } }),
        fileInput
      ]),
      fileInfo
    ]);

    var srcSelect = el('select');
    srcSelect.addEventListener('change', function () {
      state.activeKey = srcSelect.value || null;
      state.userPickedSource = true;
      onSourceChanged();
    });
    var origCk = el('input', { type: 'checkbox' });
    origCk.addEventListener('change', function () { settings.showOriginal = origCk.checked; saveSettings(); });
    var trInfo = el('div', { className: 'muted' });
    var trErr = el('div', { className: 'err' });
    var trSec = el('div', null, [
      el('div', { className: 'row' }, [
        el('span', { className: 'lbl', text: '원문' }), srcSelect,
        el('button', { className: 'b', text: '다시 찾기', on: { click: rescan } })
      ]),
      el('div', { className: 'row' }, [el('label', { className: 'ck' }, [origCk, '원문(영어)도 같이 보기'])]),
      trInfo, trErr
    ]);

    var offsetVal = el('span', { className: 'val' });
    var sizeVal = el('span', { className: 'val' });
    function nudge(d) { return function () { settings.offset = Math.round((settings.offset + d) * 10) / 10; saveSettings(); refresh(); }; }
    function common() {
      return el('div', null, [
        el('div', { className: 'row' }, [
          el('span', { className: 'lbl', text: '싱크' }),
          el('button', { className: 'b', text: '-0.5', on: { click: nudge(-0.5) } }),
          el('button', { className: 'b', text: '-0.1', on: { click: nudge(-0.1) } }),
          offsetVal,
          el('button', { className: 'b', text: '+0.1', on: { click: nudge(0.1) } }),
          el('button', { className: 'b', text: '+0.5', on: { click: nudge(0.5) } })
        ]),
        el('div', { className: 'muted', text: '+ 는 자막을 늦게, - 는 자막을 빠르게 표시합니다.' }),
        el('div', { className: 'row' }, [
          el('span', { className: 'lbl', text: '글자' }),
          el('button', { className: 'b', text: '가-', on: { click: function () { settings.fontSize = Math.max(10, settings.fontSize - 2); saveSettings(); refresh(); } } }),
          sizeVal,
          el('button', { className: 'b', text: '가+', on: { click: function () { settings.fontSize = Math.min(60, settings.fontSize + 2); saveSettings(); refresh(); } } })
        ]),
        el('div', { className: 'row' }, [
          el('span', { className: 'lbl', text: '위치' }),
          el('button', { className: 'b', text: '▲', on: { click: function () { settings.bottom = Math.min(80, settings.bottom + 3); saveSettings(); refresh(); } } }),
          el('button', { className: 'b', text: '▼', on: { click: function () { settings.bottom = Math.max(0, settings.bottom - 3); saveSettings(); refresh(); } } })
        ])
      ]);
    }
    var commonSec = common();
    var videoInfo = el('div', { className: 'muted' });
    var frameInfo = el('div');

    var panel = el('div', { className: 'panel hidden' }, [
      el('div', { className: 'hd' }, [
        el('span', { text: '자막 도우미 v' + VERSION }),
        el('button', { className: 'b', text: '✕', on: { click: function () { togglePanel(false); } } })
      ]),
      seg, fileSec, trSec, el('hr'), commonSec, el('hr'), videoInfo, frameInfo
    ]);

    root.appendChild(overlay);
    root.appendChild(fab);
    root.appendChild(panel);

    function mount() {
      var fs = document.fullscreenElement || document.webkitFullscreenElement;
      var target = fs && fs.tagName !== 'VIDEO' ? fs : document.documentElement;
      if (host.parentNode !== target) target.appendChild(host);
    }

    function togglePanel(force) {
      var show = typeof force === 'boolean' ? force : panel.classList.contains('hidden');
      panel.classList.toggle('hidden', !show);
      if (show) { rescan(); refresh(); }
    }

    function refresh() {
      Object.keys(modeBtns).forEach(function (k) { modeBtns[k].classList.toggle('on', settings.mode === k); });
      fab.classList.toggle('on', settings.mode !== 'off');
      fileSec.classList.toggle('hidden', settings.mode !== 'file');
      trSec.classList.toggle('hidden', settings.mode !== 'translate');
      commonSec.classList.toggle('hidden', settings.mode === 'off');

      fileInfo.textContent = state.fileName
        ? state.fileName + ' · ' + state.fileCues.length + '줄'
        : '.srt / .vtt / .smi / .ass 파일을 선택하세요. (한글 SMI 인코딩 자동 인식)';

      // 원문 자막 목록
      var keys = [];
      state.sources.forEach(function (s) { keys.push(s); });
      var sig = keys.map(function (s) { return s.key + s.cues.length; }).join('|') + state.activeKey;
      if (srcSelect.__sig !== sig) {
        srcSelect.__sig = sig;
        srcSelect.textContent = '';
        if (!keys.length) srcSelect.appendChild(el('option', { value: '', text: '화면 자막 읽기 (자막 파일 못 찾음)' }));
        keys.forEach(function (s) {
          var o = el('option', { value: s.key, text: s.label + ' (' + s.cues.length + '줄)' });
          if (s.key === state.activeKey) o.selected = true;
          srcSelect.appendChild(o);
        });
      }
      origCk.checked = !!settings.showOriginal;
      var src = currentSource();
      trInfo.textContent = src
        ? '번역 진행: ' + Math.min(tr.done, tr.total) + ' / ' + tr.total + '줄'
        : '자막 파일을 못 찾아 화면에 뜨는 자막을 실시간 번역합니다. 영상 재생 후 자막을 켜고 「다시 찾기」를 눌러보세요.';
      trErr.textContent = tr.error;

      offsetVal.textContent = (settings.offset > 0 ? '+' : '') + settings.offset.toFixed(1) + '초';
      sizeVal.textContent = settings.fontSize + 'px';
      overlay.style.fontSize = settings.fontSize + 'px';
      overlay.style.paddingBottom = settings.bottom + '%';

      var v = state.video;
      videoInfo.textContent = v
        ? '영상 감지됨 (' + Math.round(v.getBoundingClientRect().width) + '×' + Math.round(v.getBoundingClientRect().height) + ')'
        : '이 페이지에서 영상을 찾지 못했습니다.';
      frameInfo.textContent = '';
      if (!v) {
        var frames = foreignFrames();
        if (frames.length) {
          frameInfo.appendChild(el('div', { className: 'muted', text: '영상이 다른 주소의 플레이어(iframe) 안에 있습니다. 아래 버튼으로 플레이어만 따로 연 뒤, 거기서 북마크를 다시 실행하세요.' }));
          frames.slice(0, 3).forEach(function (src, i) {
            frameInfo.appendChild(el('div', { className: 'row' }, [
              el('button', { className: 'b', text: '▶ 플레이어 열기' + (frames.length > 1 ? ' ' + (i + 1) : ''), on: { click: function () { location.href = src; } } })
            ]));
          });
        }
      }
      lastLines = null;
    }

    var lastLines = null;
    var lastRect = '';
    function render(lines) {
      var v = state.video;
      if (!v) { overlay.style.display = 'none'; return; }
      var r = v.getBoundingClientRect();
      var rect = [r.left, r.top, r.width, r.height].map(Math.round).join(',');
      if (rect !== lastRect) {
        lastRect = rect;
        overlay.style.left = r.left + 'px';
        overlay.style.top = r.top + 'px';
        overlay.style.width = r.width + 'px';
        overlay.style.height = r.height + 'px';
      }
      overlay.style.display = r.width > 0 ? 'flex' : 'none';
      var sig = JSON.stringify(lines);
      if (sig === lastLines) return;
      lastLines = sig;
      overlay.textContent = '';
      lines.forEach(function (l) { overlay.appendChild(el('div', { className: 'line ' + (l.cls || ''), text: l.text })); });
    }

    return { host: host, mount: mount, togglePanel: togglePanel, refresh: refresh, render: render };
  })();

  // ---------------------------------------------------------------------------
  // 동작
  // ---------------------------------------------------------------------------
  function setMode(mode) {
    settings.mode = mode;
    saveSettings();
    applyHiding();
    ui.refresh();
    if (mode === 'translate') rescan();
  }

  function rescan() {
    pickVideo();
    scanTextTracks();
    scanPerformance();
    var src = currentSource();
    if (settings.mode === 'translate' && src) translateAll(src.cues);
  }

  function loadFile(file) {
    var reader = new FileReader();
    reader.onload = function () {
      var cues = [];
      try { cues = parseSubtitle(decodeBuffer(reader.result)); } catch (e) { /* 아래에서 안내 */ }
      state.fileCues = cues;
      state.fileName = cues.length ? file.name : file.name + ' (읽을 수 있는 자막이 없습니다)';
      ui.refresh();
    };
    reader.readAsArrayBuffer(file);
  }

  function linesNow() {
    var v = state.video;
    if (!v || settings.mode === 'off') return [];
    var t = v.currentTime - settings.offset;
    if (settings.mode === 'file') {
      return activeCues(state.fileCues, t).map(function (c) { return { text: c.text }; });
    }
    // 번역 모드
    var texts;
    var src = currentSource();
    if (src) {
      texts = activeCues(src.cues, t).map(function (c) { return c.text; });
    } else {
      var live = readDomCaption();
      if (live !== state.liveText) { state.liveText = live; translateLive(live); }
      texts = live ? [live] : [];
    }
    var out = [];
    texts.forEach(function (orig) {
      var ko = tr.cache.get(orig);
      out.push(ko ? { text: ko } : { text: orig, cls: 'pending' });
      if (ko && settings.showOriginal) out.push({ text: orig, cls: 'orig' });
    });
    return out;
  }

  var lastSlow = 0;
  var slowCount = 0;
  function tick(ts) {
    requestAnimationFrame(tick);
    if (ts - lastSlow > 1000) {
      lastSlow = ts;
      ui.mount();
      pickVideo();
      if (settings.mode === 'translate' && ++slowCount % 5 === 0) scanTextTracks();
    }
    ui.render(linesNow());
  }

  function start() {
    watchNetwork();
    ui.mount();
    pickVideo();
    applyHiding();
    ui.refresh();
    rescan();
    document.addEventListener('fullscreenchange', ui.mount);
    document.addEventListener('webkitfullscreenchange', ui.mount);
    requestAnimationFrame(tick);
    if (!IS_USERSCRIPT) ui.togglePanel(true);
  }

  window.__subHelper = { togglePanel: function () { ui.togglePanel(); }, version: VERSION };

  if (IS_USERSCRIPT) {
    // 유저스크립트: 영상이 있는 페이지(프레임)에서만 버튼 표시
    var waited = 0;
    (function waitForVideo() {
      var ok = allVideos().some(function (v) {
        var r = v.getBoundingClientRect();
        return r.width * r.height >= 200 * 120;
      });
      if (ok) return start();
      if ((waited += 2000) < 10 * 60 * 1000) setTimeout(waitForVideo, 2000);
    })();
  } else {
    start();
  }
})();

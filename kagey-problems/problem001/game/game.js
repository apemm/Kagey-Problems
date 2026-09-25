/* game.js: Problem 001, playable, on grids up to 10 x 10.
   You choose a blackout; the page thinks of a rectangle and shows you only its visible corners;
   you pick the hidden ones. A separate check tests the blackout against every rectangle on the
   grid and, if it fails, shows two rectangles that cannot be told apart.
   Mount with <div data-rectangle-game></div>, after blackout.js. */
(function () {
  'use strict';

  var B = window.Blackout;
  var SVG = 'http://www.w3.org/2000/svg';
  var UNIT = 100;                       // one grid step, in SVG units
  var LOW = 2, HIGH = 10;               // the sizes on offer, for rows and for columns
  var STORE = 'kagey001.best';          // the player's best valid blackout per size, in this browser

  /* What is known, for an n x m grid with n <= m. Keyed with the smaller side first.
     exact: the maximum is known (proved, or by an exhaustive computer search).
     Otherwise most is the largest blackout we know and bound is the proved upper bound. */
  var WAYS = {
    '2x2': 1, '3x3': 53, '3x4': 224, '3x5': 892, '3x6': 3420, '3x7': 12704, '3x8': 45864, '3x9': 161992,
    '4x4': 316, '4x5': 1810, '4x6': 26, '4x7': 292, '5x5': 8
  };
  var COMPUTED = { '5x5': 10, '5x6': 11, '5x7': 12, '6x6': 12 };

  function facts(rows, cols) {
    var n = Math.min(rows, cols), m = Math.max(rows, cols), key = n + 'x' + m;
    var f = { n: n, m: m, key: key, ways: WAYS[key] || 0, exact: true, proved: true };
    if (n === 2) { f.most = m === 2 ? 4 : m + 1; if (m > 2) f.ways = m * Math.pow(2, m - 1); }
    else if (n === 3) f.most = m + 2;
    else if (n === 4) f.most = m === 4 ? 7 : m === 5 ? 8 : m + 4;
    else if (COMPUTED[key]) { f.most = COMPUTED[key]; f.proved = false; }
    else { f.exact = false; f.proved = false; f.most = n + m; f.bound = m + Math.floor(n * n / 4); }
    return f;
  }

  /* Blackouts we hold, drawn with the smaller side as the rows ('#' blacked out).
     5 x 5 is the representative from the paper: its 8 images under the symmetries of the square
     are all 8 maximum blackouts. The others are a staircase plus one point, found by a search and
     each checked against every rectangle; on 5 x 6, 5 x 7 and 6 x 6 they are maxima, and on the
     larger grids they are the best we know. Whatever is taken from here is checked again below. */
  var WITNESS = {
    '5x5': ['..###', '..#..', '.##..', '##...', '#...#'],
    '5x6': ['##....', '.##...', '..###.', '....##', '#....#'],
    '5x7': ['##....#', '.##....', '..###..', '....##.', '.....##'],
    '5x8': ['##.....#', '.###....', '...###..', '.....##.', '......##'],
    '5x9': ['####.....', '...####..', '......##.', '.......##', '#.......#'],
    '5x10': ['####......', '...####...', '......###.', '........##', '#........#'],
    '6x6': ['###...', '..###.', '....##', '#....#', '.....#', '.....#'],
    '6x7': ['####...', '...###.', '.....##', '......#', '......#', '#.....#'],
    '6x8': ['####....', '...###..', '.....##.', '......#.', '......#.', '#.....##'],
    '6x9': ['##.......', '.##......', '..####...', '.....###.', '.......##', '#.......#'],
    '6x10': ['##.......#', '.##.......', '..###.....', '....####..', '.......##.', '........##'],
    '7x7': ['###....', '..###..', '....##.', '.....#.', '.....#.', '.....##', '#.....#'],
    '7x8': ['##......', '.###....', '...##...', '....##..', '.....##.', '......##', '#......#'],
    '7x9': ['##......#', '.##......', '..##.....', '...##....', '....###..', '......##.', '.......##'],
    '7x10': ['###.......', '..###.....', '....###...', '......##..', '.......##.', '........##', '#........#'],
    '8x8': ['###.....', '..###...', '....###.', '......#.', '......#.', '......#.', '......##', '#......#'],
    '8x9': ['###......', '..###....', '....###..', '......#..', '......#..', '......#..', '......###', '#.......#'],
    '8x10': ['###.......', '..##......', '...##.....', '....###...', '......##..', '.......##.', '........##', '#........#'],
    '9x9': ['###......', '..###....', '....###..', '......##.', '.......#.', '.......#.', '.......#.', '.......##', '#.......#'],
    '9x10': ['##........', '.##.......', '..##......', '...##.....', '....###...', '......##..', '.......##.', '........##', '#........#'],
    '10x10': ['###.......', '..###.....', '....###...', '......###.', '........##', '.........#', '.........#', '.........#', '.........#', '#........#']
  };

  // Row 0 plus column 0: m + n - 1 points, valid on every grid up to 10 x 10. The maximum on
  // three rows and on 4 x 4 and 4 x 5.
  function cross(n, m) {
    var out = [];
    for (var y = 0; y < n; y++) {
      var line = '';
      for (var x = 0; x < m; x++) line += x === 0 || y === 0 ? '#' : '.';
      out.push(line);
    }
    return out;
  }

  // The four-row construction from the paper, for m >= 6: m + 4 points.
  function fourRows(m) {
    var out = [];
    for (var y = 0; y < 4; y++) {
      var line = '';
      for (var x = 0; x < m; x++) {
        var on = y === 0 ? x >= 1 && x <= m - 2
          : y === 1 ? x >= m - 2
          : y === 2 ? x <= 1
          : x === 0 || x === m - 1;
        line += on ? '#' : '.';
      }
      out.push(line);
    }
    return out;
  }

  // A two-row maximum, chosen uniformly: one column blacked out whole, one point from each of the
  // others. These are all m * 2^(m-1) of them (the Strip Theorem).
  function twoRows(m) {
    var whole = Math.floor(Math.random() * m), top = '', bottom = '';
    for (var x = 0; x < m; x++) {
      var up = x === whole || Math.random() < 0.5, down = x === whole || !up;
      top += up ? '#' : '.';
      bottom += down ? '#' : '.';
    }
    return [top, bottom];
  }

  /* Every image of a picture (n rows, m columns) that fits a rows x cols board, under the
     symmetries of the rectangle, turning it a quarter turn first when the board stands the other way. */
  function images(pic, rows, cols) {
    var n = pic.length, m = pic[0].length, out = [];
    for (var t = 0; t < 8; t++) {
      var turn = t & 4, flipX = t & 1, flipY = t & 2;
      var w = turn ? n : m, h = turn ? m : n;
      if (w !== cols || h !== rows) continue;
      var S = new Uint8Array(rows * cols);
      for (var y = 0; y < n; y++) {
        for (var x = 0; x < m; x++) {
          if (pic[y].charAt(x) !== '#') continue;
          var X = turn ? y : x, Y = turn ? x : y;
          if (flipX) X = w - 1 - X;
          if (flipY) Y = h - 1 - Y;
          S[Y * cols + X] = 1;
        }
      }
      out.push(S);
    }
    return out;
  }

  function picture(S, rows, cols) {           // back to rows of '#' and '.', smaller side as the rows
    var out = [], turn = rows > cols;
    for (var a = 0; a < (turn ? cols : rows); a++) {
      var line = '';
      for (var b = 0; b < (turn ? rows : cols); b++) line += S[turn ? b * cols + a : a * cols + b] ? '#' : '.';
      out.push(line);
    }
    return out;
  }

  function readBest() {
    try { return JSON.parse(window.localStorage.getItem(STORE) || '{}') || {}; } catch (e) { return {}; }
  }
  function writeBest(all) {
    try { window.localStorage.setItem(STORE, JSON.stringify(all)); } catch (e) { /* private window: keep it for this visit only */ }
  }

  function make(name, attrs, parent, ns) {
    var node = ns ? document.createElementNS(ns, name) : document.createElement(name);
    for (var k in attrs) {
      if (k === 'text') node.textContent = attrs[k]; else node.setAttribute(k, attrs[k]);
    }
    if (parent) parent.appendChild(node);
    return node;
  }
  function num(n) { return n.toLocaleString('en-US'); }
  function plural(n, word) { return num(n) + ' ' + word + (n === 1 ? '' : 's'); }
  function same(S, T) { for (var k = 0; k < S.length; k++) if (S[k] !== T[k]) return false; return true; }

  function Game(root) {
    this.root = root;
    this.calm = !!(window.matchMedia && window.matchMedia('(prefers-reduced-motion: reduce)').matches);
    this.best = readBest();
    root.textContent = '';
    root.classList.add('game');

    var left = make('div', { 'class': 'game__board' }, root);
    this.svg = make('svg', { role: 'group', 'aria-label': 'The grid' }, left, SVG);

    var panel = make('div', { 'class': 'game__panel' }, root);
    var sizes = make('div', { 'class': 'game__sizes' }, panel);
    this.rowPick = this.picker(sizes, 'Rows', 'rows');
    this.colPick = this.picker(sizes, 'Columns', 'cols');

    this.count = make('p', { 'class': 'game__count' }, panel);
    this.status = make('p', { 'class': 'game__status', 'aria-live': 'polite' }, panel);
    this.actions = make('div', { 'class': 'game__actions' }, panel);

    var hint = make('details', { 'class': 'game__hint' }, panel);
    make('summary', { text: 'Hint: what is the most you can black out?' }, hint);
    this.hint = make('p', {}, hint);
    this.meter = make('div', { 'class': 'game__meter', 'aria-hidden': 'true' }, hint);
    this.hintBox = hint;
    var self = this;
    hint.addEventListener('toggle', function () { self.sync(); });

    this.resize(5, 6);
  }

  Game.prototype.picker = function (parent, label, prop) {
    var self = this, group = make('div', { 'class': 'game__pick', role: 'group', 'aria-label': label }, parent);
    make('span', { 'class': 'label', text: label }, group);
    var buttons = [];
    for (var n = LOW; n <= HIGH; n++) {
      (function (value) {
        var b = make('button', { type: 'button', text: String(value) }, group);
        b.addEventListener('click', function () {
          self.resize(prop === 'rows' ? value : self.rows, prop === 'cols' ? value : self.cols);
        });
        buttons.push(b);
      })(n);
    }
    return buttons;
  };

  Game.prototype.resize = function (rows, cols) {
    this.rows = rows;
    this.cols = cols;
    this.S = new Uint8Array(rows * cols);
    this.rects = B.allRectangles(rows, cols);
    this.index = new Map();             // corners -> which rectangle, for judging a guess
    for (var n = 0; n < this.rects.length; n++) this.index.set(B.cornerKey(this.rects[n]), n);
    this.facts = facts(rows, cols);
    this.known = null;
    this.mode = 'edit';                 // edit | guess
    this.checked = null;                // { groups, at } after a check, until the blackout changes
    this.secret = -1;
    this.picks = [];
    this.verdict = null;                // null | right | wrong | shown | notrect
    this.guess = -1;
    this.streak = 0;
    this.note = '';
    this.shown = false;                 // true when the board came from Show a maximum
    this.given = false;                 // the same, until a point is moved: not the player's own work
    this.pairAt = 0;                    // which of the pair is showing, when they cannot take turns
    this.was = null;                    // the blackout as it was last drawn, to spot what just turned
    this.drawBoard();
    this.sync();
  };

  Game.prototype.size = function () {
    var n = 0;
    for (var k = 0; k < this.S.length; k++) n += this.S[k];
    return n;
  };
  Game.prototype.record = function () { return this.best[this.facts.key] || null; };

  /* Remember a blackout the player found, if it beats their best on this size. Only called on
     blackouts that have just passed the check. */
  Game.prototype.keep = function () {
    var size = this.size(), mine = this.record();
    if (!size || this.given || (mine && mine.size >= size)) return false;
    this.best[this.facts.key] = { size: size, grid: picture(this.S, this.rows, this.cols) };
    writeBest(this.best);
    return true;
  };

  /* ---------------------------------------------------------------- board */

  Game.prototype.drawBoard = function () {
    var self = this, svg = this.svg, rows = this.rows, cols = this.cols;
    var step = Math.min(6.2, 36 / Math.max(rows, cols));    // rem per grid step, so 10 x 10 still fits
    svg.textContent = '';
    svg.setAttribute('viewBox', '0 0 ' + cols * UNIT + ' ' + rows * UNIT);
    svg.style.maxWidth = (cols * step) + 'rem';

    this.layer = make('g', { 'class': 'game__shapes' }, svg, SVG);
    this.points = [];
    for (var k = 0; k < rows * cols; k++) {
      (function (id) {
        var x = (id % cols + 0.5) * UNIT, y = (Math.floor(id / cols) + 0.5) * UNIT;
        var g = make('g', { 'class': 'pt', role: 'button', tabindex: id === 0 ? '0' : '-1', transform: 'translate(' + x + ' ' + y + ')' }, svg, SVG);
        make('rect', { 'class': 'pt__hit', x: -50, y: -50, width: 100, height: 100 }, g, SVG);
        make('rect', { 'class': 'pt__ring', x: -34, y: -34, width: 68, height: 68 }, g, SVG);
        make('rect', { 'class': 'pt__tile', x: -24, y: -24, width: 48, height: 48 }, g, SVG);
        g.addEventListener('click', function () { self.press(id); });
        g.addEventListener('keydown', function (e) { self.key(e, id); });
        self.points.push(g);
      })(k);
    }
  };

  // Arrow keys walk the grid; only one point is ever in the tab order.
  Game.prototype.key = function (e, id) {
    var cols = this.cols, rows = this.rows, x = id % cols, y = (id - x) / cols;
    if (e.key === 'Enter' || e.key === ' ') { e.preventDefault(); this.press(id); return; }
    if (e.key === 'ArrowLeft') x = Math.max(0, x - 1);
    else if (e.key === 'ArrowRight') x = Math.min(cols - 1, x + 1);
    else if (e.key === 'ArrowUp') y = Math.max(0, y - 1);
    else if (e.key === 'ArrowDown') y = Math.min(rows - 1, y + 1);
    else return;
    e.preventDefault();
    this.points[id].setAttribute('tabindex', '-1');
    var next = this.points[y * cols + x];
    next.setAttribute('tabindex', '0');
    next.focus();
  };

  Game.prototype.outline = function (rect, kind) {
    var cols = this.cols;
    var pts = rect.map(function (k) { return ((k % cols) + 0.5) * UNIT + ',' + (Math.floor(k / cols) + 0.5) * UNIT; }).join(' ');
    return make('polygon', { 'class': 'game__rect game__rect--' + kind, points: pts, pathLength: 1 }, this.layer, SVG);
  };

  /* Two rectangles that present identically. Drawn at the same time they sit on top of each other,
     which is the whole difficulty, so they take turns: one is traced, held and cleared, then the other,
     round and round. The corners they both show stay marked the whole time, because that is the point. */
  Game.prototype.drawClash = function (pair) {
    var self = this;
    pair.forEach(function (n, which) {
      var poly = self.outline(self.rects[n], which ? 'b' : 'a');
      if (self.calm) poly.classList.toggle('is-hidden', which !== (self.pairAt % 2));
      else poly.classList.add('is-cycling');
    });
  };

  /* ---------------------------------------------------------------- moves */

  Game.prototype.press = function (id) {
    if (this.mode === 'edit') {
      this.S[id] ^= 1;
      this.checked = null;                                 // the pair no longer describes this blackout
      this.shown = false;
      this.given = false;
      this.note = '';
    } else if (this.verdict !== 'right' && this.verdict !== 'wrong' && this.verdict !== 'shown') {
      var secret = this.rects[this.secret];
      if (secret.indexOf(id) >= 0 && !this.S[id]) return;                 // already lit
      if (!this.S[id]) { this.note = 'That point is visible and not lit, so it is not one of my corners.'; this.sync(); return; }
      var at = this.picks.indexOf(id), need = secret.filter(function (k) { return this.S[k]; }, this).length;
      if (at >= 0) this.picks.splice(at, 1);
      else if (this.picks.length < need) this.picks.push(id);
      else { this.note = 'Only ' + plural(need, 'corner') + ' ' + (need === 1 ? 'is' : 'are') + ' hidden. Deselect one first.'; this.sync(); return; }
      this.note = '';
      this.verdict = null;
      if (this.picks.length === need) this.judge();
    }
    this.sync();
  };

  Game.prototype.judge = function () {
    var S = this.S, secret = this.rects[this.secret];
    var mine = secret.filter(function (k) { return !S[k]; }).concat(this.picks);
    var found = this.index.get(B.cornerKey(mine));
    this.guess = found === undefined ? -1 : found;
    if (this.guess < 0) { this.verdict = 'notrect'; return; }
    this.verdict = this.guess === this.secret ? 'right' : 'wrong';
    this.streak = this.verdict === 'right' ? this.streak + 1 : 0;
  };

  /* The blackouts we can hand over on this board without searching: constructions and stored
     pictures in every orientation that fits, each checked against every rectangle first. */
  Game.prototype.stock = function () {
    if (this.known) return this.known;
    var f = this.facts, rows = this.rows, cols = this.cols, rects = this.rects, pics = [];
    if (f.n === 2 && f.m === 2) pics.push(['##', '##']);
    else if (f.n === 3 || (f.n === 4 && f.m <= 5)) pics.push(cross(f.n, f.m));
    else if (f.n === 4) pics.push(fourRows(f.m));
    else if (WITNESS[f.key]) pics.push(WITNESS[f.key]);
    var seen = Object.create(null), out = [];
    pics.forEach(function (pic) {
      images(pic, rows, cols).forEach(function (S) {
        var key = S.join('');
        if (seen[key] || B.confusable(rects, S).length) return;      // checked, not taken on trust
        seen[key] = 1;
        out.push(S);
      });
    });
    return (this.known = out);
  };

  /* Drop a maximum blackout (or on open sizes the best we know) on the board to poke at. Pressing
     it again tries for a different one: a quick random search where that is fast, otherwise the
     stock above in a new orientation. */
  Game.prototype.showMaximum = function () {
    var f = this.facts, rows = this.rows, cols = this.cols, target = f.most, current = this.S, S = null, tries = 0;
    var fresh = function (T) { return T && T.length === current.length && !same(T, current); };
    var fits = function (T) {
      if (!T) return false;
      var n = 0;
      for (var k = 0; k < T.length; k++) n += T[k];
      return n === target;
    };
    while (!S && tries++ < 4) {
      var T = null;
      if (f.n === 2 && f.m > 2) T = images(twoRows(f.m), rows, cols)[Math.floor(Math.random() * 4)];
      else if (f.n >= 5 && f.key !== '5x5') T = B.staircasePlusOne(rows, cols, Math.random, 250);
      else if (rows * cols <= 30 && !(f.ways && f.ways <= 8)) T = B.findMaximum(rows, cols, target, Math.random, 400);
      if (fits(T) && fresh(T) && !B.confusable(this.rects, T).length) S = T;
    }
    if (!S) {
      var stock = this.stock().filter(fits), unseen = stock.filter(fresh);
      var pool = unseen.length ? unseen : stock;
      if (pool.length) S = pool[Math.floor(Math.random() * pool.length)].slice();
    }
    if (!S) { this.note = 'Could not find one quickly enough. Try again.'; this.sync(); return; }
    this.S = S;
    this.mode = 'edit';
    this.picks = [];
    this.verdict = null;
    this.checked = { groups: [], at: 0 };                  // every candidate above was checked
    this.note = '';
    this.shown = true;
    this.given = true;
    this.sync();
  };

  Game.prototype.loadBest = function () {
    var mine = this.record();
    if (!mine) return;
    var S = images(mine.grid, this.rows, this.cols)[0];
    if (!S) return;
    this.S = S;
    this.mode = 'edit';
    this.shown = this.given = false;
    this.note = '';
    this.runCheck();
  };

  Game.prototype.runCheck = function () {
    this.checked = { groups: B.confusable(this.rects, this.S), at: 0, beat: false };
    this.note = '';
    this.shown = false;
    if (!this.checked.groups.length) this.checked.beat = this.keep();
    this.sync();
  };

  Game.prototype.deal = function () {
    var S = this.S, rects = this.rects, pool = [];
    this.checked = null;                                   // whatever was being demonstrated is over
    if (!this.size()) { this.note = 'Black out a few points first. With nothing hidden there is nothing to guess.'; this.sync(); return; }
    // Half the time, if the blackout is flawed, I pick from the rectangles that expose the flaw.
    var flawed = B.confusable(rects, S);
    if (flawed.length && Math.random() < 0.5) pool = flawed[Math.floor(Math.random() * flawed.length)];
    if (!pool.length) rects.forEach(function (r, n) { if (r.some(function (k) { return S[k]; })) pool.push(n); });
    this.mode = 'guess';
    this.secret = pool[Math.floor(Math.random() * pool.length)];
    this.picks = [];
    this.verdict = null;
    this.guess = -1;
    this.checked = null;
    this.note = '';
    this.sync();
  };

  /* ----------------------------------------------------------------- view */

  Game.prototype.button = function (label, fn, primary) {
    var b = make('button', { type: 'button', text: label, 'class': primary ? 'is-primary' : '' }, this.actions);
    b.addEventListener('click', fn);
    return b;
  };

  /* What a valid blackout earns, in words. */
  Game.prototype.praise = function (size) {
    var f = this.facts, most = f.most, grid = this.rows + ' × ' + this.cols, all = plural(this.rects.length, 'rectangle');
    var saved = this.checked && this.checked.beat ? ' Saved as your best on this size.' : '';
    if (f.exact) {
      if (size === most) return (this.shown ? 'One of the maximum blackouts. ' : 'Valid, and as large as it can be. ') +
        most + ' is the most you can hide on a ' + grid + ' grid, and all ' + all + ' still look different. Move a point and see what breaks.' + saved;
      return 'Valid. All ' + all + ' look different from one another' +
        (this.hintBox.open ? ', and there is room for ' + (most - size) + ' more.' : '. Can you black out more?') + saved;
    }
    if (size > most) return 'Valid, and larger than any blackout we know on a ' + grid + ' grid. If it holds up, the conjecture that ' +
      most + ' is the most is false.' + saved;
    if (size === most) return (this.shown ? 'The best blackout we know on this grid. ' : 'Valid, and as large as any blackout we know. ') +
      most + ' points on a ' + grid + ' grid, and all ' + all + ' still look different. Nobody has shown that ' + (most + 1) + ' is impossible.' + saved;
    return 'Valid. All ' + all + ' look different from one another' +
      (this.hintBox.open ? ', and we know blackouts with ' + plural(most - size, 'more point') + '.' : '. Can you black out more?') + saved;
  };

  Game.prototype.sync = function () {
    var self = this, S = this.S, rows = this.rows, cols = this.cols, size = this.size(), f = this.facts, most = f.most;
    var secret = this.mode === 'guess' ? this.rects[this.secret] : null;
    var clash = this.checked && this.checked.groups.length ? this.checked.groups[this.checked.at % this.checked.groups.length] : null;
    var done = this.verdict === 'right' || this.verdict === 'wrong' || this.verdict === 'shown';
    var mine = this.record();

    this.rowPick.forEach(function (b, n) { b.setAttribute('aria-pressed', String(n + LOW === rows)); });
    this.colPick.forEach(function (b, n) { b.setAttribute('aria-pressed', String(n + LOW === cols)); });
    this.root.setAttribute('data-mode', this.mode);

    // shapes first, so the points sit on top of them
    this.layer.textContent = '';
    var shared = [];
    if (clash) {
      shared = this.rects[clash[0]].filter(function (k) { return !S[k]; });
      this.drawClash(clash);
    }
    if (secret && done) {
      if (this.verdict === 'wrong') this.outline(this.rects[this.guess], 'b');
      this.outline(secret, 'a');
    }

    this.points.forEach(function (g, id) {
      var x = id % cols, y = (id - x) / cols, out = !!S[id];
      if (self.was && self.was.length === S.length && self.was[id] !== S[id]) {   // just toggled: let it be seen turning
        g.classList.remove('is-turning');
        void g.getBoundingClientRect();                          // restart the animation
        g.classList.add('is-turning');
      }
      var lit = !!secret && !out && secret.indexOf(id) >= 0;
      g.classList.toggle('is-out', out);
      g.classList.toggle('is-lit', lit);
      g.classList.toggle('is-pick', self.picks.indexOf(id) >= 0 || (done && !!secret && out && secret.indexOf(id) >= 0));
      g.classList.toggle('is-shared', shared.indexOf(id) >= 0);
      g.setAttribute('aria-label', 'Row ' + (y + 1) + ', column ' + (x + 1) + ', ' + (out ? 'blacked out' : lit ? 'visible, a corner of my rectangle' : 'visible'));
      if (self.mode === 'edit') g.setAttribute('aria-pressed', String(out)); else g.removeAttribute('aria-pressed');
    });
    this.was = S.slice();

    this.count.textContent = plural(size, 'point') + ' blacked out of ' + rows * cols + ' · ' + plural(this.rects.length, 'rectangle') + ' on this grid';

    // what to say
    var say = this.note;
    if (!say && this.mode === 'edit') {
      if (!this.checked) say = 'Select points to black them out. Then check your blackout, or play: I think of a rectangle, show you only the corners you left visible, and you find the rest.';
      else if (clash) {
        var hiddenAll = shared.length === 0, total = this.checked.groups.reduce(function (n, grp) { return n + grp.length; }, 0);
        say = 'Not valid. Watch the grid: two different rectangles are drawn in turn, and they show exactly the same ' +
          (hiddenAll ? 'thing, which is nothing at all' : (shared.length === 1 ? 'corner' : 'corners') + ' (ringed)') +
          ', so nothing tells them apart. In all, ' + num(total) + ' of the ' + num(this.rects.length) + ' rectangles can be confused with another.';
      } else say = this.praise(size);
    } else if (!say) {
      var showing = secret.filter(function (k) { return !S[k]; }).length, need = 4 - showing;
      if (this.verdict === 'right') say = 'Right. That is my rectangle.' + (this.streak > 1 ? ' ' + this.streak + ' in a row.' : '');
      else if (this.verdict === 'wrong') say = 'Not this time. Yours (dashed) and mine show exactly the same corners, so nothing could have told you which. That is what an invalid blackout costs you.';
      else if (this.verdict === 'shown') say = 'Here it is.';
      else if (this.verdict === 'notrect') say = 'Those four points are not the corners of a rectangle. Change a pick.';
      else say = 'I am thinking of a rectangle. ' + (showing ? plural(showing, 'corner') + ' of it ' + (showing === 1 ? 'is' : 'are') + ' lit.' : 'None of its corners are visible.') +
        ' Select the ' + plural(need, 'hidden corner').replace(/^1 /, 'one ') + ' among the blacked-out points.';
    }
    this.status.textContent = say;
    this.status.setAttribute('data-tone', clash || this.verdict === 'wrong' || this.verdict === 'notrect' ? 'bad' : (this.checked || this.verdict === 'right') ? 'good' : '');

    // what you can do
    this.actions.textContent = '';
    if (this.mode === 'edit') {
      this.button('Check this blackout', function () { self.runCheck(); }, true);
      this.button('Play', function () { self.deal(); });
      var again = this.shown && size === most;
      this.button(f.exact ? (again ? 'Another maximum' : 'Show a maximum') : (again ? 'Another one' : 'Show the best known'), function () { self.showMaximum(); });
      if (mine && !(this.checked && !clash && size === mine.size)) this.button('My best (' + mine.size + ')', function () { self.loadBest(); });
      if (clash) {
        if (this.calm) this.button('Show the other one', function () { self.pairAt++; self.sync(); });
        if (this.checked.groups.length > 1) this.button('Another pair', function () { self.checked.at++; self.pairAt = 0; self.sync(); });
        this.button('Back to the grid', function () { self.checked = null; self.sync(); });
      }
      if (size) this.button('Clear', function () { self.S.fill(0); self.checked = null; self.shown = self.given = false; self.note = ''; self.sync(); });
    } else {
      if (done) this.button('Another rectangle', function () { self.deal(); }, true);
      else this.button('Show me', function () { self.verdict = 'shown'; self.streak = 0; self.sync(); });
      this.button('Change the blackout', function () { self.mode = 'edit'; self.secret = -1; self.picks = []; self.verdict = null; self.note = ''; self.sync(); });
    }

    var grid = rows + ' × ' + cols, yours = ' You have ' + size + '.' + (mine ? ' Your best valid blackout on this size has ' + mine.size + '.' : '');
    if (f.exact) {
      this.hint.textContent = 'On a ' + grid + ' grid you can black out at most ' + most + ' points and still identify every rectangle' +
        '.' + (f.proved ? '' : ' This value comes from an exhaustive computer search.') +
        (f.ways ? ' There ' + (f.ways === 1 ? 'is exactly one way' : 'are ' + num(f.ways) + ' ways') + ' to do it.' : '') + yours;
    } else {
      this.hint.textContent = 'Nobody knows the most for a ' + grid + ' grid. It is at most ' + f.bound +
        ' (proved), the best blackout we know has ' + most + ' points, and we conjecture that ' + most + ' is the most.' + yours;
    }
    this.meter.style.setProperty('--fill', Math.min(1, size / most));
    this.meter.classList.toggle('is-over', size > (f.exact ? most : f.bound));
  };

  function mountAll() {
    if (!B) return;
    Array.prototype.forEach.call(document.querySelectorAll('[data-rectangle-game]'), function (node) { node.game = new Game(node); });
  }
  if (document.readyState === 'loading') document.addEventListener('DOMContentLoaded', mountAll); else mountAll();
})();

/* blackout.js
   The mathematics behind the game: Problem 001 of Peter Kagey's open problem collection.

   Take an R x C grid of points. A blackout S is a set of points that are hidden. A rectangle
   (four corners on grid points, tilted ones included, zero-area ones excluded) presents its
   visible corners, C(R) \ S. The blackout is valid when no two rectangles present the same set.

   Nothing here touches the page. Points are indexed k = y * C + x, with (0, 0) at the top left.
   S is a Uint8Array of length R * C, 1 = blacked out. Grids up to 10 x 10 (3,305 rectangles). */
(function (root) {
  'use strict';

  function gcd(a, b) { a = Math.abs(a); b = Math.abs(b); while (b) { var t = a % b; a = b; b = t; } return a; }

  function now() { return root.performance && root.performance.now ? root.performance.now() : Date.now(); }

  function shuffled(list, random) {
    var out = list.slice();
    for (var k = out.length - 1; k > 0; k--) {
      var j = Math.floor(random() * (k + 1)), t = out[k];
      out[k] = out[j]; out[j] = t;
    }
    return out;
  }

  /* How many rectangles there are: OEIS A289832, and A085582 when R = C.
     Fix one side u = (a, b) pointing into the first quadrant (a >= 1, b >= 0); exactly one of a
     rectangle's four side directions does. The other side is k times the primitive perpendicular. */
  function countRectangles(R, C) {
    var total = 0;
    for (var a = 1; a < C; a++) {
      for (var b = 0; b < R; b++) {
        var g = gcd(a, b), pa = a / g, pb = b / g;
        for (var k = 1; ; k++) {
          var w = a + k * pb, h = b + k * pa;          // bounding box of the rectangle
          if (w >= C || h >= R) break;
          total += (C - w) * (R - h);
        }
      }
    }
    return total;
  }

  /* Every rectangle on the grid, each once, as [k0, k1, k2, k3] with the corners in order around it.
     Same bookkeeping as the count above. */
  function allRectangles(R, C) {
    var out = [];
    for (var a = 1; a < C; a++) {
      for (var b = 0; b < R; b++) {
        var g = gcd(a, b), pa = a / g, pb = b / g;
        for (var k = 1; ; k++) {
          var vx = -k * pb, vy = k * pa;                  // the second side: the first, turned a quarter turn
          if (a - vx >= C || b + vy >= R) break;
          for (var y = 0; y + b + vy < R; y++) {
            for (var x = -vx; x + a < C; x++) {
              out.push([y * C + x, (y + b) * C + x + a, (y + b + vy) * C + x + a + vx, (y + vy) * C + x + vx]);
            }
          }
        }
      }
    }
    return out;
  }

  /* What a rectangle presents under S, as one number: the visible corners in increasing order,
     seven bits each (there are at most 100 points), with the count on top so that sets of
     different sizes never share a key. */
  function lookKey(rect, S) {
    var v = [], n;
    for (n = 0; n < 4; n++) if (!S[rect[n]]) v.push(rect[n]);
    v.sort(function (p, q) { return p - q; });
    var key = v.length;
    for (n = 0; n < v.length; n++) key = key * 128 + v[n];
    return key;
  }

  /* The corners of a rectangle as one number, whatever order they come in. */
  function cornerKey(rect) {
    var v = rect.slice().sort(function (p, q) { return p - q; });
    return ((v[0] * 128 + v[1]) * 128 + v[2]) * 128 + v[3];
  }

  /* Group the rectangles by what they present under S. Returns the groups with more than one member:
     the sets of rectangles that cannot be told apart. Straight from the definition: one pass,
     one hash per rectangle. */
  function confusable(rects, S) {
    var groups = new Map(), out = [];
    for (var n = 0; n < rects.length; n++) {
      var key = lookKey(rects[n], S), g = groups.get(key);
      if (g) g.push(n); else groups.set(key, [n]);
    }
    groups.forEach(function (g) { if (g.length > 1) out.push(g); });
    return out;
  }

  /* Every rectangle that has grid points p and q among its corners, as fn(k0, k1, k2, k3) with the
     corners in order around the rectangle. A rectangle may be reported more than once. */
  function rectanglesThrough(R, C, p, q, fn) {
    var px = p % C, py = (p - px) / C, qx = q % C, qy = (q - qx) / C;
    var ux = qx - px, uy = qy - py, g = gcd(ux, uy);

    // p and q as neighbouring corners: slide the side pq along its perpendicular, both ways.
    var wx = -uy / g, wy = ux / g;
    for (var sign = 1; sign >= -1; sign -= 2) {
      for (var t = 1; ; t++) {
        var ax = px + sign * t * wx, ay = py + sign * t * wy;
        var bx = qx + sign * t * wx, by = qy + sign * t * wy;
        if (ax < 0 || ay < 0 || ax >= C || ay >= R || bx < 0 || by < 0 || bx >= C || by >= R) break;
        fn(p, q, by * C + bx, ay * C + ax);
      }
    }

    // p and q as opposite corners: the other two lie on the circle with diameter pq.
    // (x - px)(x - qx) + (y - py)(y - qy) = 0 is a quadratic in y for each x.
    var sx = px + qx, sy = py + qy, reach = Math.sqrt(ux * ux + uy * uy);
    var x0 = Math.max(0, Math.ceil((sx - reach) / 2)), x1 = Math.min(C - 1, Math.floor((sx + reach) / 2));
    for (var x = x0; x <= x1; x++) {
      var disc = sy * sy - 4 * (py * qy + (x - px) * (x - qx));
      if (disc < 0) continue;
      var rootD = Math.round(Math.sqrt(disc));
      if (rootD * rootD !== disc || ((sy + rootD) & 1)) continue;
      for (var n = rootD === 0 ? 1 : 2, y = (sy + rootD) / 2; n > 0; n--, y = (sy - rootD) / 2) {
        var ox = sx - x, oy = sy - y;                      // the corner opposite (x, y)
        if (y < 0 || y >= R || oy < 0 || oy >= R || ox < 0 || ox >= C) continue;
        if ((x === px && y === py) || (x === qx && y === qy)) continue;
        fn(p, y * C + x, q, oy * C + ox);
      }
    }
  }

  /* Is S valid? Returns null if it is, or a pair of rectangles that present identically.

     Three corners pin a rectangle down (they form a right triangle, and the fourth corner is
     forced), so two rectangles can only be confused if each shows at most two corners, that is,
     if each has at least two corners in S. It is enough to list the rectangles through every
     pair of hidden points and look for a repeated presentation among them. Much faster than
     confusable() when few points are hidden, which is what the searches below need. */
  function findCollision(R, C, S) {
    var hidden = [], i, j, clash = null;
    for (i = 0; i < S.length; i++) if (S[i]) hidden.push(i);
    var seen = new Set(), looks = new Map();
    var examine = function (a, b, c, d) {
      if (clash) return;
      var rect = [a, b, c, d], id = cornerKey(rect);
      if (seen.has(id)) return;
      seen.add(id);
      var look = lookKey(rect, S);
      if (looks.has(look)) clash = [looks.get(look), rect]; else looks.set(look, rect);
    };
    for (i = 0; i < hidden.length && !clash; i++) {
      for (j = i + 1; j < hidden.length && !clash; j++) rectanglesThrough(R, C, hidden[i], hidden[j], examine);
    }
    return clash;
  }

  function isValid(R, C, S) { return findCollision(R, C, S) === null; }

  /* A valid blackout of exactly `target` points, or null if the search runs out of time.

     Validity is hereditary: every subset of a valid blackout is valid. So the sets of size target
     can be reached by adding one point at a time, never passing through an invalid set, and a
     depth-first walk that keeps the set valid at every step will find one if it exists. The points
     are offered in a random order, so repeated calls turn up different maxima. Small grids only. */
  function findMaximum(R, C, target, random, budgetMs) {
    var N = R * C, order = [], S = new Uint8Array(N), k;
    var deadline = now() + (budgetMs || 1500);
    for (k = 0; k < N; k++) order.push(k);
    order = shuffled(order, random);
    var found = null, checks = 0;
    (function walk(from, count) {
      if (count === target) { found = S.slice(); return true; }
      for (var i = from; i <= N - (target - count); i++) {
        if ((++checks & 15) === 0 && now() > deadline) return true;   // out of time: unwind
        S[order[i]] = 1;
        if (!findCollision(R, C, S) && walk(i + 1, count + 1)) return true;
        S[order[i]] = 0;
      }
      return false;
    })(0, 0);
    return found;
  }

  /* A staircase plus one point: R + C blacked out. The 5 x 5 maximum has this shape, and on every
     grid from 5 x 5 to 10 x 10 each monotone staircase from one corner to the opposite one is valid
     and many of them take one more point. Pick a random staircase, offer the other points in a
     random order, keep the first that leaves the blackout valid. Null if time runs out. */
  function staircasePlusOne(R, C, random, budgetMs) {
    var deadline = now() + (budgetMs || 300), N = R * C;
    while (now() < deadline) {
      var steps = [], k, S = new Uint8Array(N), flip = random() < 0.5;
      for (k = 0; k < R - 1; k++) steps.push(1);
      for (k = 0; k < C - 1; k++) steps.push(0);
      steps = shuffled(steps, random);
      var x = 0, y = 0;
      S[flip ? C - 1 : 0] = 1;
      for (k = 0; k < steps.length; k++) {
        if (steps[k]) y++; else x++;
        S[y * C + (flip ? C - 1 - x : x)] = 1;
      }
      if (findCollision(R, C, S)) continue;
      var rest = [];
      for (k = 0; k < N; k++) if (!S[k]) rest.push(k);
      rest = shuffled(rest, random);
      for (k = 0; k < rest.length; k++) {
        S[rest[k]] = 1;
        if (!findCollision(R, C, S)) return S;
        S[rest[k]] = 0;
        if ((k & 7) === 7 && now() > deadline) return null;
      }
    }
    return null;
  }

  root.Blackout = {
    countRectangles: countRectangles,
    allRectangles: allRectangles,
    cornerKey: cornerKey,
    confusable: confusable,
    rectanglesThrough: rectanglesThrough,
    findCollision: findCollision,
    isValid: isValid,
    findMaximum: findMaximum,
    staircasePlusOne: staircasePlusOne
  };
})(typeof window !== 'undefined' ? window : this);

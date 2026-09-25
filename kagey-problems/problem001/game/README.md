# The rectangle game

A playable version of Problem 001 on grids from 2 x 2 up to 10 x 10. Open `index.html` in a
browser. It runs from the file system with no server and no build step.

Select points to black them out. **Check this blackout** tests it against every rectangle on the
grid, and if two rectangles show the same visible corners it draws them in turn. **Play** picks a
rectangle in secret and shows you its visible corners, and you find the hidden ones. The hint says
what is known for the current size.

## What the page knows

Here n is the smaller side and m the larger.

- For n = 2 the maximum is m+1 (4 on 2 x 2), with m*2^(m-1) optima. Proved.
- For n = 3 it is m+2. Proved.
- For n = 4 it is 7 on 4 x 4, 8 on 4 x 5, and m+4 from m = 6 on. Proved.
- On 5 x 5 it is 10 (8 optima, one orbit), on 5 x 6 it is 11, on 5 x 7 it is 12, and on 6 x 6 it
  is 12. These come from an exhaustive computer search.
- Every other size with n >= 5 is open. The page gives the upper bound m + floor(n^2/4) and the
  best blackout it has, which has n+m points, a monotone staircase from one corner to the opposite
  one plus one more point. We conjecture that n+m is the maximum.

**Show a maximum** uses the constructions from the paper in every orientation, a random choice
among the two-row optima, a short random search on small grids, and the 5 x 5 orbit. On the
larger grids it becomes **Show the best known** and searches for a staircase plus one point, with
one stored example per size in case the search fails. Every blackout it offers is checked against
all rectangles before it is shown.

Your best valid blackout on each size is saved in the browser's local storage. If you find one
with more than n+m points on an open size, the conjecture is false.

## Files

- `index.html`: the page.
- `blackout.js`: rectangle enumeration, the validity checks and the searches.
- `game.js`: the game, the table of known values and the stored examples.
- `style.css`: light and dark themes. It follows the system's reduced-motion setting.

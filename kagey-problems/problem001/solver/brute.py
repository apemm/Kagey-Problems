"""Exhaustive oracle.

For tiny grids: test every blackout S by computing all presentations C(R) \ S,
hashing them, and checking for collisions (injectivity). ~30 lines.
Must agree with engine.py on every grid up to 2x4 and on 3x3.
"""

def max_blackout_brute(rows, cols):
    raise NotImplementedError

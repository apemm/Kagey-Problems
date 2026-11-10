import json, time
from rectlib import *
words = ["27,25,3,36,6,6,47,1,67,16,6,1,12,1,14,1,1,23,34,45,56",
         "16,36,5,25,2,2,14,7,12,27,2,7,67,7,47,7,7,56,45,34,23"]
for w in words:
    c = parse_word(w); t = time.time()
    a = check_board(7, c); b = check_board_plain(7, c)
    print(a, b, count_rectangles_by_sides(7, 21), round(time.time() - t, 2))
bad = parse_word("16,36,5,25,2,2,14,7,12,27,2,7,67,7,47,7,7,56,45,34,23"); bad[4] = [1]
print(check_board(7, bad)['valid'], check_board_plain(7, bad)['valid'])

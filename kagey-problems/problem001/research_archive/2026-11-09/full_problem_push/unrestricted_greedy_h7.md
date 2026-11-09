# Unrestricted greedy extension can leave the recurrent component

9 November 2026. A complete pass over the certified height-seven parity graph gives a counterexample to unrestricted minimum-row extension. This differs from the earlier rule that minimizes only among successors remaining in the recurrent component.

The graph has \(17,463,676\) states, including \(248,064\) states of outdegree zero. Choosing the least available row at every step gives:

* \(1,484,306\) states whose greedy path ends at an outdegree-zero state;
* \(15,979,370\) states whose greedy path reaches the constant-row-one fixed point;
* no other functional cycle.

The unique recurrent component has \(16,886,304\) states. Of these, \(1,190,878\) have an unrestricted greedy path that eventually leaves that component and terminates.

A short witness starts with the word
\[
 (3,3,6,4).
\]
It reaches state \(1147\), which lies in the recurrent component. Its successive least valid rows are
\[
 (1,3,1,1).
\]
The resulting normalized-language prefix \((3,3,6,4,1,3,1,1)\) has no valid next row. The statement uses the exact residual-pattern language and fixed final parity row-pair set. It does not identify that language with all rectangle-contained finite prefixes.

More precisely, the first three appended rows remain in the recurrent component. The word \((3,3,6,4,1,3,1)\) reaches state \(28511\), whose valid next rows are \(1,2,3,5,6,7\). Row one leads directly to the dead state \(100274\); all the other listed rows remain in the recurrent component. The internal greedy rule therefore chooses row two at this point.

The complete pass is implemented in [SeaUnrestrictedGreedy.cs](SeaUnrestrictedGreedy.cs), with results in [sea_h7_unrestricted_greedy.json](sea_h7_unrestricted_greedy.json). It reads every labeled transition, partitions the resulting functional graph into terminal basins and cycles, checks total basin coverage, and separately reads the certified component labels. The prefix witness is recovered from earlier BFS parents. The source graph SHA256 is

    3264bc24053b20adf7b44ee2631905aa75987306e99dd2f781fc9394a0141e2b

The pass took \(3.21\) seconds and used about \(309\) MiB. It is a finite graph result, not a claim about greedy behavior at every height.

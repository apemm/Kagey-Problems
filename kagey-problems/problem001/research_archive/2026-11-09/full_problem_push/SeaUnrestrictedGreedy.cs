using System;
using System.IO;
using System.Collections.Generic;
using System.Diagnostics;
using System.Text.Json;
using System.Security.Cryptography;

public static class SeaUnrestrictedGreedy {
    public static void Run(string graph, string output) {
        var watch = Stopwatch.StartNew();
        using var source = new BinaryReader(File.OpenRead(graph));
        if (source.ReadInt32() != 0x53454731) throw new Exception("Graph format");
        int h = source.ReadInt32(), n = source.ReadInt32();
        if (source.BaseStream.Length != 12L + 4L * h * n) throw new Exception("Graph length");
        var next = new int[n];
        var letter = new byte[n];
        Array.Fill(next, -1);
        var degreeCounts = new long[h + 1];
        var deadPrefix = new List<int>();
        for (int i = 0; i < n; i++) {
            int degree = 0;
            for (int r = 1; r <= h; r++) {
                int j = source.ReadInt32();
                if (j < -1 || j >= n) throw new Exception("Invalid transition");
                if (j >= 0) {
                    degree++;
                    if (next[i] < 0) { next[i] = j; letter[i] = (byte)r; }
                }
            }
            degreeCounts[degree]++;
            if (degree == 0 && deadPrefix.Count < 20) deadPrefix.Add(i);
        }
        var visit = new int[n];
        var path = new List<int>();
        var cycles = new List<object>();
        var basinSizes = new List<long>();
        long deadBasin = 0;
        int walk = 0, maximumWalk = 0;
        for (int start = 0; start < n; start++) {
            if (visit[start] != 0) continue;
            walk++; path.Clear(); int j = start;
            while (j >= 0 && visit[j] == 0) {
                visit[j] = walk; path.Add(j); j = next[j];
            }
            maximumWalk = Math.Max(maximumWalk, path.Count);
            int finalMark;
            if (j < 0) finalMark = -1;
            else if (visit[j] < 0) finalMark = visit[j];
            else {
                if (visit[j] != walk) throw new Exception("Unfinished prior walk");
                int begin = path.IndexOf(j);
                if (begin < 0) throw new Exception("Cycle anchor");
                int length = path.Count - begin;
                var word = new int[Math.Min(length, 100)];
                for (int k = 0; k < word.Length; k++) word[k] = letter[path[begin + k]];
                int id = cycles.Count;
                cycles.Add(new { id, length, state = j, word_prefix = word });
                basinSizes.Add(0);
                finalMark = -id - 2;
            }
            foreach (int state in path) visit[state] = finalMark;
            if (finalMark == -1) deadBasin += path.Count;
            else basinSizes[-finalMark - 2] += path.Count;
        }
        long total = deadBasin;
        foreach (long count in basinSizes) total += count;
        if (total != n) throw new Exception("Basin coverage");
        int canonicalComponent = -1, firstRecurrentDead = -1;
        long recurrentStates = 0, recurrentDeadBasin = 0;
        var recurrentDeadWord = new List<int>();
        var prefixToFirstRecurrentDead = new List<int>();
        if (File.Exists(graph + ".components")) {
            using var components = new BinaryReader(File.OpenRead(graph + ".components"));
            if (components.ReadInt32() != n) throw new Exception("Component size");
            int rowOneState = -1;
            for (int i = 0; i < n; i++)
                if (next[i] == i && letter[i] == 1) { rowOneState = i; break; }
            if (rowOneState < 0) throw new Exception("Missing row-one fixed state");
            components.BaseStream.Position = 4L + 4L * rowOneState;
            canonicalComponent = components.ReadInt32();
            components.BaseStream.Position = 4;
            for (int i = 0; i < n; i++) {
                if (components.ReadInt32() != canonicalComponent) continue;
                recurrentStates++;
                if (visit[i] == -1) {
                    recurrentDeadBasin++;
                    if (firstRecurrentDead < 0) firstRecurrentDead = i;
                }
            }
            for (int i = firstRecurrentDead; i >= 0 && next[i] >= 0; i = next[i])
                recurrentDeadWord.Add(letter[i]);
            int target = firstRecurrentDead;
            while (target > 0) {
                source.BaseStream.Position = 12;
                int parent = -1, row = -1;
                for (int i = 0; i < target && parent < 0; i++)
                    for (int r = 1; r <= h; r++)
                        if (source.ReadInt32() == target) { parent = i; row = r; break; }
                if (parent < 0) throw new Exception("Missing earlier BFS parent");
                prefixToFirstRecurrentDead.Add(row); target = parent;
            }
            prefixToFirstRecurrentDead.Reverse();
        }
        string hash;
        using (var hashSource = File.OpenRead(graph))
            hash = Convert.ToHexString(SHA256.HashData(hashSource)).ToLowerInvariant();
        var result = new {
            graph = Path.GetFileName(graph), sha256 = hash, height = h, states = n,
            outdegree_counts = degreeCounts, dead_end_prefix = deadPrefix,
            greedy_dead_end_basin = deadBasin, cycles, cycle_basin_sizes = basinSizes,
            canonical_component = canonicalComponent, canonical_states = recurrentStates,
            canonical_dead_end_basin = recurrentDeadBasin,
            first_canonical_dead_basin_state = firstRecurrentDead,
            prefix_to_first_canonical_dead_basin_state = prefixToFirstRecurrentDead,
            first_canonical_dead_basin_greedy_word = recurrentDeadWord,
            maximum_new_walk = maximumWalk, seconds = watch.Elapsed.TotalSeconds,
            peak_memory_mb = Process.GetCurrentProcess().PeakWorkingSet64 / 1048576.0
        };
        string json = JsonSerializer.Serialize(result, new JsonSerializerOptions { WriteIndented = true });
        File.WriteAllText(output, json + "\n");
        Console.WriteLine(json);
    }
}

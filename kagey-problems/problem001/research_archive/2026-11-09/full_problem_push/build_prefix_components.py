"""Copy the audited SCC routine into a standalone graph-file reader."""
from pathlib import Path

HERE = Path(__file__).resolve().parent
source = (HERE/'SeaGraphSparse.cs').read_text()
start = source.index('    private static object Components(')
end = source.index('    public static void Run(',start)
method = source[start:end]
method = method.replace('Components(Graph graph,string binary)',
                        'Components(int h,int n,int[] edges,string binary)',1)
begin_body = method.index('        int h=graph.Height,n=graph.Count;')
gc = method.index('        GC.Collect();',begin_body)
method = method[:begin_body] + method[gc:]
prefix = '''using System;
using System.IO;
using System.Linq;
using System.Collections.Generic;
using System.Diagnostics;
using System.Text.Json;

public static class SeaPrefixComponents {
'''
suffix = '''
    public static void Run(string graphPath,string output) {
        var watch=Stopwatch.StartNew();
        int h,n; int[] edges;
        using(var reader=new BinaryReader(File.OpenRead(graphPath))) {
            if(reader.ReadInt32()!=0x53454731) throw new Exception("Graph magic");
            h=reader.ReadInt32();n=reader.ReadInt32();
            if(reader.BaseStream.Length!=12L+4L*h*n) throw new Exception("Graph size");
            edges=new int[checked(h*n)];
            for(int i=0;i<edges.Length;i++) {
                edges[i]=reader.ReadInt32();
                if(edges[i]<-1 || edges[i]>=n) throw new Exception("Target range");
            }
        }
        var info=Components(h,n,edges,graphPath);
        var result=new {
            height=h,states=n,complete=true,full_graph_complete=false,
            scope="Complete SCC analysis of an induced prefix, not of the full sea graph",
            components=info,elapsed_seconds=watch.Elapsed.TotalSeconds,
            peak_memory_mb=Process.GetCurrentProcess().PeakWorkingSet64/1048576.0
        };
        string json=JsonSerializer.Serialize(result,new JsonSerializerOptions{WriteIndented=true});
        File.WriteAllText(output,json+"\\\\n");Console.WriteLine(json);
    }
}
'''
# Preserve actual C# newline escape, not a literal backslash in the JSON file.
suffix = suffix.replace('json+"\\\\n"','json+"\\n"')
(HERE/'SeaPrefixComponents.cs').write_text(prefix+method+suffix)
print('Wrote SeaPrefixComponents.cs from the unchanged SCC routine.')

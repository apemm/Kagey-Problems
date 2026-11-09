using System;
using System.IO;
using System.Linq;
using System.Collections.Generic;
using System.Diagnostics;
using System.Text.Json;

public static class SeaPrefixComponents {
    private static object Components(int h,int n,int[] edges,string binary)
    {
        GC.Collect(); GC.WaitForPendingFinalizers(); GC.Collect();
        var visited=new bool[n]; var nextEdge=new byte[n];
        var stack=new int[n]; var order=new int[n]; int orderSize=0;
        for(int start=0;start<n;start++)
        {
            if(visited[start]) continue;
            int top=0; stack[top++]=start; visited[start]=true;
            while(top>0)
            {
                int v=stack[top-1];
                if(nextEdge[v]==h) { order[orderSize++]=v; top--; continue; }
                int w=edges[v*h+nextEdge[v]++];
                if(w>=0 && !visited[w]) { visited[w]=true; stack[top++]=w; }
            }
        }
        var counts=new int[n];
        foreach(int w in edges) if(w>=0) counts[w]++;
        var offsets=new int[n+1];
        for(int i=0;i<n;i++) offsets[i+1]=offsets[i]+counts[i];
        var reverse=new int[offsets[n]];
        Array.Copy(offsets,counts,n);
        for(int v=0;v<n;v++)
            for(int k=0;k<h;k++)
            { int w=edges[v*h+k]; if(w>=0) reverse[counts[w]++]=v; }
        var component=new int[n]; Array.Fill(component,-1);
        var sizes=new List<int>();
        for(int oi=n-1;oi>=0;oi--)
        {
            int start=order[oi]; if(component[start]>=0) continue;
            int cid=sizes.Count,size=0,top=0;
            stack[top++]=start; component[start]=cid;
            while(top>0)
            {
                int v=stack[--top]; size++;
                for(int j=offsets[v];j<offsets[v+1];j++)
                {
                    int w=reverse[j];
                    if(component[w]<0) { component[w]=cid; stack[top++]=w; }
                }
            }
            sizes.Add(size);
        }
        var cyclic=new HashSet<int>();
        if(!String.IsNullOrEmpty(binary))
        {
            using(var stream=new FileStream(binary+".components",FileMode.Create,FileAccess.Write))
            using(var writer=new BinaryWriter(stream))
            {
                writer.Write(n);
                foreach(int value in component) writer.Write(value);
            }
        }
        for(int i=0;i<sizes.Count;i++) if(sizes[i]>1) cyclic.Add(i);
        for(int v=0;v<n;v++)
            for(int k=0;k<h;k++) if(edges[v*h+k]==v) cyclic.Add(component[v]);
        var constants=new int[h];
        for(int r=0;r<h;r++)
        {
            int v=0;
            // The graph alphabet may be a relabelled subset of physical rows.
            // Follow a constant letter to its fixed state instead of deriving
            // the geometric memory length from the alphabet size.
            for(int j=0;j<=n;j++)
            {
                int w=edges[v*h+r];
                if(w<0 || w==v) { v=w; break; }
                v=w;
                if(j==n) throw new Exception("Constant orbit did not stabilize");
            }
            if(v>=0 && edges[v*h+r]!=v) throw new Exception("Constant did not stabilize");
            constants[r]=v;
        }
        return new {
            edges=offsets[n],scc_count=sizes.Count,
            scc_size_histogram=sizes.GroupBy(x=>x).ToDictionary(x=>x.Key,x=>x.Count()),
            constant_states=constants,
            constant_components=constants.Select(x=>x<0?-1:component[x]).ToArray(),
            cyclic_components=cyclic.OrderByDescending(c=>sizes[c]).Select(c=>new {
                id=c,size=sizes[c],
                constant_rows=Enumerable.Range(0,h).Where(r=>constants[r]>=0 &&
                                                           component[constants[r]]==c)
                                        .Select(r=>r+1).ToArray() }).ToArray()
        };
    }

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
        File.WriteAllText(output,json+"\n");Console.WriteLine(json);
    }
}

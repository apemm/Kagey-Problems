using System;
using System.IO;
using System.Linq;
using System.Collections.Generic;
using System.Diagnostics;
using System.Security.Cryptography;
using System.Text.Json;

// Independent iterative Tarjan check; the builder uses two-pass Kosaraju.
public static class SeaPrefixTarjanCheck {
    public static void Run(string graphPath,string reportPath,string output) {
        var watch=Stopwatch.StartNew();
        int h,n; int[] edges;
        using(var reader=new BinaryReader(File.OpenRead(graphPath))) {
            if(reader.ReadInt32()!=0x53454731) throw new Exception("Graph magic");
            h=reader.ReadInt32();n=reader.ReadInt32();
            if(reader.BaseStream.Length!=12L+4L*h*n) throw new Exception("Graph size");
            edges=new int[checked(h*n)];
            for(int i=0;i<edges.Length;i++) {
                edges[i]=reader.ReadInt32();
                if(edges[i]<-1 || edges[i]>=n) throw new Exception("Target");
            }
        }
        var index=new int[n];Array.Fill(index,-1);
        var low=new int[n];var parent=new int[n];Array.Fill(parent,-1);
        var dfs=new int[n];var active=new int[n];
        var next=new byte[n];var onStack=new bool[n];
        var component=new int[n];Array.Fill(component,-1);
        var sizes=new List<int>();
        int clock=0,activeTop=0;
        for(int start=0;start<n;start++) {
            if(index[start]>=0) continue;
            int top=0;dfs[top++]=start;
            index[start]=low[start]=clock++;onStack[start]=true;active[activeTop++]=start;
            while(top>0) {
                int v=dfs[top-1];
                if(next[v]<h) {
                    int w=edges[v*h+next[v]++];
                    if(w<0) continue;
                    if(index[w]<0) {
                        parent[w]=v;dfs[top++]=w;
                        index[w]=low[w]=clock++;onStack[w]=true;active[activeTop++]=w;
                    } else if(onStack[w] && index[w]<low[v]) low[v]=index[w];
                    continue;
                }
                top--;
                if(parent[v]>=0 && low[v]<low[parent[v]]) low[parent[v]]=low[v];
                if(low[v]==index[v]) {
                    int count=0,w;
                    do {
                        if(activeTop<=0) throw new Exception("Tarjan stack");
                        w=active[--activeTop];onStack[w]=false;
                        component[w]=sizes.Count;count++;
                    } while(w!=v);
                    sizes.Add(count);
                }
            }
        }
        if(clock!=n || activeTop!=0 || component.Any(c=>c<0))
            throw new Exception("Tarjan coverage");
        using var doc=JsonDocument.Parse(File.ReadAllText(reportPath));
        if(doc.RootElement.GetProperty("height").GetInt32()!=h ||
           doc.RootElement.GetProperty("states").GetInt32()!=n)
            throw new Exception("Report dimensions");
        int claimedCount=doc.RootElement.GetProperty("components").GetProperty("scc_count").GetInt32();
        if(claimedCount!=sizes.Count) throw new Exception("SCC count");
        var forward=new int[claimedCount];Array.Fill(forward,-1);
        var reverse=new int[sizes.Count];Array.Fill(reverse,-1);
        using(var reader=new BinaryReader(File.OpenRead(graphPath+".components"))) {
            if(reader.ReadInt32()!=n || reader.BaseStream.Length!=4L+4L*n)
                throw new Exception("Component file");
            for(int i=0;i<n;i++) {
                int a=reader.ReadInt32(),b=component[i];
                if(a<0 || a>=claimedCount) throw new Exception("Claimed component range");
                if(forward[a]<0) forward[a]=b;
                else if(forward[a]!=b) throw new Exception("Claimed component splits");
                if(reverse[b]<0) reverse[b]=a;
                else if(reverse[b]!=a) throw new Exception("Claimed components merge");
            }
        }
        if(forward.Any(c=>c<0) || reverse.Any(c=>c<0)) throw new Exception("Component bijection");
        int checkedCycles=0;
        var cycleIds=new HashSet<int>();
        foreach(var item in doc.RootElement.GetProperty("components").GetProperty("cyclic_components").EnumerateArray()) {
            int id=item.GetProperty("id").GetInt32(),size=item.GetProperty("size").GetInt32();
            if(id<0 || id>=claimedCount || !cycleIds.Add(id))
                throw new Exception("Duplicate or invalid cyclic component");
            if(sizes[forward[id]]!=size) throw new Exception("Cyclic component size");
            if(size==1) {
                int vertex=Array.FindIndex(component,c=>c==forward[id]);
                if(!Enumerable.Range(0,h).Any(r=>edges[vertex*h+r]==vertex))
                    throw new Exception("Claimed singleton cycle");
            }
            checkedCycles++;
        }
        int actualCycles=sizes.Count(s=>s>1);
        for(int i=0;i<n;i++) if(sizes[component[i]]==1)
            for(int r=0;r<h;r++) if(edges[i*h+r]==i) {actualCycles++;break;}
        if(actualCycles!=checkedCycles) throw new Exception("Missing cyclic component");
        string hash;
        using(var stream=File.OpenRead(graphPath))
            hash=Convert.ToHexString(SHA256.HashData(stream)).ToLowerInvariant();
        var result=new {status="PASS",graph=Path.GetFileName(graphPath),height=h,states=n,
            scc_count=sizes.Count,cyclic_components=actualCycles,
            algorithm="Independent iterative Tarjan; complete partition bijection checked",
            graph_sha256=hash,seconds=watch.Elapsed.TotalSeconds,
            peak_memory_mb=Process.GetCurrentProcess().PeakWorkingSet64/1048576.0};
        string json=JsonSerializer.Serialize(result,new JsonSerializerOptions{WriteIndented=true});
        File.WriteAllText(output,json+"\n");Console.WriteLine(json);
    }
}

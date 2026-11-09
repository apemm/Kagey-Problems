using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.IO;
using System.Linq;
using System.Numerics;
using System.Text.Json;

public sealed class SeaResidualData
{
    public int height { get; set; }
    public int count { get; set; }
    public int[] successor { get; set; }
    public int[][] supersets { get; set; }
    public int[][] subsets { get; set; }
    public int[] wildcard { get; set; }
    public int[][] match { get; set; }
    public int[][] reject { get; set; }
    public int[][] starts { get; set; }
}

public static class SeaGraphExact
{
    private sealed class Engine
    {
        public SeaResidualData D;
        public int H, W;
        private ulong[] Wild;
        private ulong[][] Match, Reject, Starts;
        private ulong[] Addition;
        public Engine(SeaResidualData d)
        {
            D=d; H=d.height; W=(d.count+63)/64;
            Wild=Mask(d.wildcard);
            Match=d.match.Select(Mask).ToArray();
            Reject=d.reject.Select(Mask).ToArray();
            Starts=d.starts.Select(Mask).ToArray();
            Addition=new ulong[W];
        }
        private ulong[] Mask(int[] ids)
        {
            var result=new ulong[W];
            foreach(int i in ids) result[i>>6]|=1UL<<(i&63);
            return result;
        }
        public bool Step(ulong[] state, int letter, ulong[] output)
        {
            for(int w=0;w<W;w++)
                if((state[w]&Reject[letter][w])!=0) return false;
            Array.Copy(Starts[letter],Addition,W);
            for(int w=0;w<W;w++)
            {
                output[w]=(state[w]&Wild[w])>>1;
                if(w+1<W) output[w]|=(state[w+1]&Wild[w+1])<<63;
                ulong bits=state[w]&Match[letter][w];
                while(bits!=0)
                {
                    int bit=BitOperations.TrailingZeroCount(bits);
                    bits&=bits-1;
                    int j=D.successor[(w<<6)+bit];
                    Addition[j>>6]|=1UL<<(j&63);
                }
            }
            for(int w=0;w<W;w++)
            {
                while(Addition[w]!=0)
                {
                    int bit=BitOperations.TrailingZeroCount(Addition[w]);
                    int i=(w<<6)+bit;
                    Addition[w]&=Addition[w]-1;
                    bool redundant=false;
                    foreach(int j in D.subsets[i])
                        if((output[j>>6]&(1UL<<(j&63)))!=0)
                        { redundant=true; break; }
                    if(redundant) continue;
                    foreach(int j in D.supersets[i])
                    {
                        ulong mask=~(1UL<<(j&63));
                        output[j>>6]&=mask;
                        Addition[j>>6]&=mask;
                    }
                    output[w]|=1UL<<bit;
                }
            }
            return true;
        }
    }
    private sealed class Graph
    {
        public int Height, Count, Processed;
        public List<int> Edges;
        public bool Complete;
        public string Reason;
        public double Seconds, MemoryMB;
    }
    private static ulong Hash(ulong[] a)
    {
        ulong result=14695981039346656037UL;
        foreach(ulong value in a)
        {
            ulong z=value+0x9e3779b97f4a7c15UL;
            z=(z^(z>>30))*0xbf58476d1ce4e5b9UL;
            z=(z^(z>>27))*0x94d049bb133111ebUL;
            result=(result^(z^(z>>31)))*1099511628211UL;
        }
        return result;
    }
    private static int CountBits(ulong[] a)
    {
        int count=0;
        foreach(ulong value in a) count+=BitOperations.PopCount(value);
        return count;
    }
    private static byte[] Sparse(ulong[] a,int count)
    {
        int length=2,previous=0;
        for(int w=0;w<a.Length;w++)
        {
            ulong bits=a[w];
            while(bits!=0)
            {
                int i=(w<<6)+BitOperations.TrailingZeroCount(bits);
                int delta=i-previous; previous=i;
                length+=delta<128?1:delta<16384?2:3;
                bits&=bits-1;
            }
        }
        var result=new byte[length]; int cursor=2;
        result[0]=(byte)(count&255); result[1]=(byte)(count>>8);
        previous=0;
        for(int w=0;w<a.Length;w++)
        {
            ulong bits=a[w];
            while(bits!=0)
            {
                int i=(w<<6)+BitOperations.TrailingZeroCount(bits);
                int delta=i-previous; previous=i;
                while(delta>=128)
                { result[cursor++]=(byte)((delta&127)|128); delta>>=7; }
                result[cursor++]=(byte)delta;
                bits&=bits-1;
            }
        }
        return result;
    }
    private static void Dense(byte[] a,ulong[] result)
    {
        Array.Clear(result,0,result.Length);
        int cursor=2,i=0;
        while(cursor<a.Length)
        {
            int delta=0,shift=0,value;
            do { value=a[cursor++]; delta|=(value&127)<<shift; shift+=7; }
            while((value&128)!=0);
            i+=delta; result[i>>6]|=1UL<<(i&63);
        }
    }
    private static bool Equal(byte[] a,ulong[] b,int count)
    {
        if((a[0]|(a[1]<<8))!=count) return false;
        int cursor=2,i=0;
        while(cursor<a.Length)
        {
            int delta=0,shift=0,value;
            do { value=a[cursor++]; delta|=(value&127)<<shift; shift+=7; }
            while((value&128)!=0);
            i+=delta;
            if((b[i>>6]&(1UL<<(i&63)))==0) return false;
        }
        return true;
    }
    private static double MemoryMB()
    {
        long result=GC.GetTotalMemory(false);
        try { result=Math.Max(result,Process.GetCurrentProcess().WorkingSet64); }
        catch { }
        return result/(1024.0*1024.0);
    }
    private static void SaveCheckpoint(string path,Engine e,List<byte[]> states,
                                       List<int> edges,int cursor)
    {
        using(var stream=new FileStream(path,FileMode.Create,FileAccess.Write))
        using(var writer=new BinaryWriter(stream))
        {
            writer.Write(0x53454133); writer.Write(e.H); writer.Write(e.W);
            writer.Write(states.Count); writer.Write(cursor); writer.Write(edges.Count);
            foreach(var state in states)
            {
                writer.Write(state.Length);
                writer.Write(state);
            }
            foreach(int value in edges) writer.Write(value);
        }
    }
    private static Graph Build(SeaResidualData data,double seconds,int stateCap,
                               double memoryCap,string checkpoint,bool resume)
    {
        var watch=Stopwatch.StartNew();
        var e=new Engine(data);
        if(data.count>=65536) throw new Exception("Sparse state count exceeds ushort");
        var states=new List<byte[]>();
        var next=new List<int>();
        var index=new Dictionary<ulong,int>();
        var edges=new List<int>();
        var stateBuffer=new ulong[e.W];
        int cursor=0;
        if(resume && File.Exists(checkpoint))
        {
            using(var stream=new FileStream(checkpoint,FileMode.Open,FileAccess.Read))
            using(var reader=new BinaryReader(stream))
            {
                int magic=reader.ReadInt32();
                if((magic!=0x53454131 && magic!=0x53454132 && magic!=0x53454133)
                   || reader.ReadInt32()!=e.H
                   || reader.ReadInt32()!=e.W) throw new Exception("Checkpoint mismatch");
                int n=reader.ReadInt32(); cursor=reader.ReadInt32();
                int nEdges=reader.ReadInt32();
                for(int i=0;i<n;i++)
                {
                    byte[] state;
                    if(magic==0x53454131)
                    {
                        for(int w=0;w<e.W;w++) stateBuffer[w]=reader.ReadUInt64();
                        state=Sparse(stateBuffer,CountBits(stateBuffer));
                    }
                    else if(magic==0x53454132)
                    {
                        Array.Clear(stateBuffer,0,stateBuffer.Length);
                        int count=reader.ReadInt32();
                        for(int j=0;j<count;j++)
                        { int b=reader.ReadUInt16(); stateBuffer[b>>6]|=1UL<<(b&63); }
                        state=Sparse(stateBuffer,count);
                    }
                    else
                    {
                        int count=reader.ReadInt32();
                        state=reader.ReadBytes(count);
                        if(state.Length!=count) throw new EndOfStreamException();
                        Dense(state,stateBuffer);
                    }
                    ulong hash=Hash(stateBuffer);
                    int old; next.Add(index.TryGetValue(hash,out old)?old:-1);
                    index[hash]=states.Count; states.Add(state);
                }
                for(int i=0;i<nEdges;i++) edges.Add(reader.ReadInt32());
                if(nEdges!=cursor*e.H) throw new Exception("Partial state in checkpoint");
            }
        }
        else
        {
            states.Add(new byte[2]); next.Add(-1); index.Add(Hash(stateBuffer),0);
        }
        var output=new ulong[e.W];
        string reason="complete";
        double memory=MemoryMB();
        while(cursor<states.Count)
        {
            Dense(states[cursor],stateBuffer);
            for(int letter=1;letter<=e.H;letter++)
            {
                if(!e.Step(stateBuffer,letter,output)) { edges.Add(-1); continue; }
                ulong hash=Hash(output);
                int bits=CountBits(output);
                int head, found=-1;
                if(index.TryGetValue(hash,out head))
                {
                    for(int j=head;j>=0;j=next[j])
                        if(Equal(states[j],output,bits)) { found=j; break; }
                }
                else head=-1;
                if(found<0)
                {
                    found=states.Count;
                    states.Add(Sparse(output,bits)); next.Add(head); index[hash]=found;
                }
                edges.Add(found);
            }
            cursor++;
            if(cursor%10000==0)
            {
                memory=MemoryMB();
                Console.WriteLine(JsonSerializer.Serialize(new {
                    phase="bfs",height=e.H,processed=cursor,discovered=states.Count,
                    memory_mb=Math.Round(memory,1),seconds=Math.Round(watch.Elapsed.TotalSeconds,2)}));
                if(states.Count>stateCap) { reason="state cap"; break; }
                if(memory>memoryCap) { reason="memory cap"; break; }
                if(watch.Elapsed.TotalSeconds>seconds) { reason="time cap"; break; }
            }
        }
        bool complete=cursor==states.Count;
        if(!complete && !String.IsNullOrEmpty(checkpoint))
        {
            Console.WriteLine("{\"phase\":\"saving checkpoint\"}");
            SaveCheckpoint(checkpoint,e,states,edges,cursor);
        }
        return new Graph { Height=e.H,Count=states.Count,Processed=cursor,
            Edges=edges,Complete=complete,Reason=reason,MemoryMB=memory,
            Seconds=watch.Elapsed.TotalSeconds };
    }
    private static object Components(Graph graph,string binary)
    {
        int h=graph.Height,n=graph.Count;
        int[] edges=graph.Edges.ToArray();
        graph.Edges=null;
        if(!String.IsNullOrEmpty(binary))
        {
            using(var stream=new FileStream(binary,FileMode.Create,FileAccess.Write))
            using(var writer=new BinaryWriter(stream))
            {
                writer.Write(0x53454731); writer.Write(h); writer.Write(n);
                foreach(int value in edges) writer.Write(value);
            }
        }
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
    public static void Run(string input,string output,double seconds,int stateCap,
                           double memoryCap,string checkpoint,bool resume,string binary)
    {
        var total=Stopwatch.StartNew();
        var data=JsonSerializer.Deserialize<SeaResidualData>(File.ReadAllText(input));
        var graph=Build(data,seconds,stateCap,memoryCap,checkpoint,resume);
        object components=null;
        if(graph.Complete) components=Components(graph,binary);
        var result=new {
            height=data.height,residuals=data.count,complete=graph.Complete,
            states=graph.Count,processed_states=graph.Processed,
            stop_reason=graph.Reason,bfs_seconds=graph.Seconds,
            memory_mb=graph.MemoryMB,components=components,
            elapsed_seconds=total.Elapsed.TotalSeconds
        };
        var options=new JsonSerializerOptions { WriteIndented=true };
        File.WriteAllText(output,JsonSerializer.Serialize(result,options)+"\n");
        Console.WriteLine(JsonSerializer.Serialize(result));
    }
}

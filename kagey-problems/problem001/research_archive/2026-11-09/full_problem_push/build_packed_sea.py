"""Generate the packed graph driver, retaining the audited transition/SCC code."""
from pathlib import Path

root = Path(__file__).resolve().parent
source = (root / 'SeaGraphExact.cs').read_text()
source = source.replace('public static class SeaGraphExact', 'public static class SeaGraphPacked')
source = source.replace('public List<int> Edges;', 'public SeaIntSlab Edges;')
start = source.index('    private static void SaveCheckpoint(')
end = source.index('    private static object Components(', start)
replacement = r'''
    private static void SavePacked(string path,Engine e,SeaPackedStates states,
                                   SeaIntSlab edges,int cursor,byte[] fingerprint)
    {
        using(var stream=new FileStream(path,FileMode.Create,FileAccess.Write))
        using(var writer=new BinaryWriter(stream))
        {
            writer.Write(0x53454134); writer.Write(e.H); writer.Write(e.W);
            writer.Write(fingerprint);
            writer.Write(states.Count); writer.Write(cursor); writer.Write(edges.Count);
            states.Write(writer); edges.Write(writer);
        }
    }
    private static Graph Build(SeaResidualData data,double seconds,int stateCap,
                               double memoryCap,string checkpoint,bool resume,
                               byte[] fingerprint,string legacy)
    {
        var watch=Stopwatch.StartNew(); var e=new Engine(data);
        if(data.count>=65536) throw new Exception("Residual universe too large");
        var states=new SeaPackedStates(e.W); var edges=new SeaIntSlab();
        var stateBuffer=new ulong[e.W]; int cursor=0;
        string loadPath=resume && File.Exists(checkpoint)?checkpoint:legacy;
        if(resume && !String.IsNullOrEmpty(loadPath) && File.Exists(loadPath))
        {
            using(var stream=new FileStream(loadPath,FileMode.Open,FileAccess.Read))
            using(var reader=new BinaryReader(stream))
            {
                int magic=reader.ReadInt32();
                if(magic<0x53454131 || magic>0x53454134 || reader.ReadInt32()!=e.H
                   || reader.ReadInt32()!=e.W) throw new Exception("Checkpoint mismatch");
                if(magic==0x53454134)
                {
                    if(!reader.ReadBytes(32).SequenceEqual(fingerprint))
                        throw new Exception("Residual-table fingerprint mismatch");
                }
                else Console.WriteLine("{\"phase\":\"importing legacy checkpoint; caller must verify input identity\"}");
                int n=reader.ReadInt32(); cursor=reader.ReadInt32();
                int nEdges=reader.ReadInt32();
                if(magic==0x53454134) states.Read(reader,n);
                else for(int i=0;i<n;i++)
                {
                    if(magic==0x53454131)
                        for(int w=0;w<e.W;w++) stateBuffer[w]=reader.ReadUInt64();
                    else if(magic==0x53454132)
                    {
                        Array.Clear(stateBuffer,0,stateBuffer.Length);
                        int count=reader.ReadInt32();
                        for(int j=0;j<count;j++)
                        { int b=reader.ReadUInt16(); stateBuffer[b>>6]|=1UL<<(b&63); }
                    }
                    else
                    {
                        int count=reader.ReadInt32(); byte[] state=reader.ReadBytes(count);
                        if(state.Length!=count) throw new EndOfStreamException();
                        Dense(state,stateBuffer);
                    }
                    if(states.Intern(stateBuffer,Hash(stateBuffer))!=i)
                        throw new Exception("Duplicate legacy state");
                    if(i%500000==0) Console.WriteLine(JsonSerializer.Serialize(new {
                        phase="import",loaded=i,states=n,blocks=states.Pool.Count,
                        memory_mb=Math.Round(MemoryMB(),1),seconds=watch.Elapsed.TotalSeconds }));
                }
                for(int i=0;i<nEdges;i++) edges.Add(reader.ReadInt32());
                if(nEdges!=checked(cursor*e.H)) throw new Exception("Partial state in checkpoint");
                if(stream.Position!=stream.Length) throw new Exception("Trailing checkpoint data");
            }
        }
        else states.Intern(stateBuffer,Hash(stateBuffer));
        var output=new ulong[e.W]; string reason="complete"; double memory=MemoryMB();
        while(cursor<states.Count)
        {
            states.Dense(cursor,stateBuffer);
            for(int letter=1;letter<=e.H;letter++)
            {
                if(!e.Step(stateBuffer,letter,output)) { edges.Add(-1); continue; }
                edges.Add(states.Intern(output,Hash(output)));
            }
            cursor++;
            if(cursor%10000==0)
            {
                memory=MemoryMB();
                Console.WriteLine(JsonSerializer.Serialize(new {
                    phase="bfs",height=e.H,processed=cursor,discovered=states.Count,
                    blocks=states.Pool.Count,memory_mb=Math.Round(memory,1),
                    seconds=Math.Round(watch.Elapsed.TotalSeconds,2)}));
                if(states.Count>stateCap) { reason="state cap"; break; }
                if(memory>memoryCap) { reason="memory cap"; break; }
                if(watch.Elapsed.TotalSeconds>seconds) { reason="time cap"; break; }
            }
        }
        bool complete=cursor==states.Count;
        if(!complete && !String.IsNullOrEmpty(checkpoint))
        {
            Console.WriteLine("{\"phase\":\"saving packed checkpoint\"}");
            SavePacked(checkpoint,e,states,edges,cursor,fingerprint);
        }
        return new Graph { Height=e.H,Count=states.Count,Processed=cursor,
            Edges=edges,Complete=complete,Reason=reason,MemoryMB=memory,
            Seconds=watch.Elapsed.TotalSeconds };
    }
'''
source = source[:start] + replacement + source[end:]
source = source.replace('double memoryCap,string checkpoint,bool resume,string binary)',
                        'double memoryCap,string checkpoint,bool resume,string binary,string legacy)')
source = source.replace('var graph=Build(data,seconds,stateCap,memoryCap,checkpoint,resume);',
    'var fingerprint=System.Security.Cryptography.SHA256.HashData(File.ReadAllBytes(input));\n'
    '        var graph=Build(data,seconds,stateCap,memoryCap,checkpoint,resume,fingerprint,legacy);')
(root / 'SeaGraphPacked.cs').write_text(source)


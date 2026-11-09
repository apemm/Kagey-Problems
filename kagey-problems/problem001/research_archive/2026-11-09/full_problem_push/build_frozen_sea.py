"""Generate the frozen engine from the exact, unchanged residual transition."""
from pathlib import Path
root=Path(__file__).resolve().parent
source=(root/'SeaGraphSparse.cs').read_text()
header=source[:source.index('public static class SeaGraphSparse')]
engine=source[source.index('    private sealed class Engine'):source.index('    private sealed class Graph')]
hashcode=source[source.index('    private static ulong Hash'):source.index('    private static int CountBits')]
body=r'''
    private static double MemoryMB()
    {
        long result=GC.GetTotalMemory(false);
        try {result=Math.Max(result,Process.GetCurrentProcess().WorkingSet64);} catch {}
        return result/(1024.0*1024.0);
    }
    private static byte[] Digest(string path)
    {
        using(var stream=File.OpenRead(path))
            return System.Security.Cryptography.SHA256.HashData(stream);
    }
    private static void SaveStatus(string path,FileStream stream,BinaryWriter writer,
                                   string checkpoint,string raw,byte[] sourceHash,byte[] residualHash,
                                   int h,int n,int original,int cursor,string reason,
                                   double seconds,double memory,long missing)
    {
        writer.Flush();stream.Flush(true);
        var result=new {
            scope="Frozen known-state induced model; full sea graph unresolved",
            full_graph_complete=false,frozen_graph_complete=cursor==n,
            checkpoint=Path.GetFileName(checkpoint),
            checkpoint_sha256=Convert.ToHexString(sourceHash).ToLowerInvariant(),
            residual_sha256=Convert.ToHexString(residualHash).ToLowerInvariant(),
            raw_graph=Path.GetFileName(raw),height=h,states=n,
            original_processed=original,processed_sources=cursor,
            committed_bytes=80L+4L*h*cursor,stop_reason=reason,
            missing_fixed_set_targets=missing,elapsed_seconds=seconds,memory_mb=memory
        };
        string json=JsonSerializer.Serialize(result,new JsonSerializerOptions {WriteIndented=true});
        File.WriteAllText(path+".pending",json+"\n");
        File.Move(path+".pending",path,true);
        Console.WriteLine(JsonSerializer.Serialize(result));
    }
    public static void Run(string input,string checkpoint,string raw,string status,
                           double seconds,double memoryCap,string endUtc,int maxProcessed)
    {
        var watch=Stopwatch.StartNew();
        var deadline=DateTimeOffset.Parse(endUtc).UtcDateTime;
        var data=JsonSerializer.Deserialize<SeaResidualData>(File.ReadAllText(input));
        var e=new Engine(data);
        var residualHash=Digest(input);var sourceHash=Digest(checkpoint);
        Console.WriteLine(JsonSerializer.Serialize(new {phase="loading frozen state set",
            checkpoint,seconds=watch.Elapsed.TotalSeconds}));
        var states=new SeaFrozenStates(e.W);
        int n,original,nEdges,cursor;long missing=0;
        bool resume=File.Exists(status);
        using(var source=new FileStream(checkpoint,FileMode.Open,FileAccess.Read,FileShare.Read,1<<20))
        using(var reader=new BinaryReader(source))
        {
            if(reader.ReadInt32()!=0x53454135 || reader.ReadInt32()!=e.H || reader.ReadInt32()!=e.W)
                throw new Exception("Frozen input header mismatch");
            if(!reader.ReadBytes(32).SequenceEqual(residualHash))
                throw new Exception("Residual fingerprint mismatch");
            n=reader.ReadInt32();original=reader.ReadInt32();nEdges=reader.ReadInt32();
            if(original<0 || original>n || nEdges!=checked(original*e.H))
                throw new Exception("Frozen input source boundary");
            states.Read(reader,n);
            if(source.Position+4L*nEdges!=source.Length)
                throw new Exception("Frozen input length mismatch");
            cursor=original;
            if(resume)
            {
                using(var doc=JsonDocument.Parse(File.ReadAllText(status)))
                {
                    var root=doc.RootElement;
                    if(root.GetProperty("checkpoint_sha256").GetString()!=Convert.ToHexString(sourceHash).ToLowerInvariant() ||
                       root.GetProperty("residual_sha256").GetString()!=Convert.ToHexString(residualHash).ToLowerInvariant() ||
                       root.GetProperty("height").GetInt32()!=e.H || root.GetProperty("states").GetInt32()!=n ||
                       root.GetProperty("original_processed").GetInt32()!=original)
                        throw new Exception("Frozen resume metadata mismatch");
                    cursor=root.GetProperty("processed_sources").GetInt32();
                    missing=root.GetProperty("missing_fixed_set_targets").GetInt64();
                    if(cursor<original || cursor>n) throw new Exception("Bad resume boundary");
                }
                using(var old=new BinaryReader(File.OpenRead(raw)))
                {
                    if(old.ReadInt32()!=0x53454631 || old.ReadInt32()!=e.H ||
                       old.ReadInt32()!=n || old.ReadInt32()!=original ||
                       !old.ReadBytes(32).SequenceEqual(sourceHash) ||
                       !old.ReadBytes(32).SequenceEqual(residualHash))
                        throw new Exception("Frozen raw header mismatch");
                    if(old.BaseStream.Length<80L+4L*e.H*cursor)
                        throw new Exception("Committed frozen edges truncated");
                }
            }
            else
            {
                if(File.Exists(raw)) throw new Exception("Untracked frozen output exists");
                using(var initial=new FileStream(raw,FileMode.CreateNew,FileAccess.Write,FileShare.Read,1<<20))
                using(var writer=new BinaryWriter(initial))
                {
                    writer.Write(0x53454631);writer.Write(e.H);writer.Write(n);writer.Write(original);
                    writer.Write(sourceHash);writer.Write(residualHash);
                    var buffer=new byte[1<<20];long remaining=4L*nEdges;
                    while(remaining>0)
                    {
                        int take=(int)Math.Min(remaining,buffer.Length);
                        source.ReadExactly(buffer.AsSpan(0,take));
                        foreach(int target in System.Runtime.InteropServices.MemoryMarshal.Cast<byte,int>(buffer.AsSpan(0,take)))
                            if(target < -1 || target>=n) throw new Exception("Bad checkpoint edge target");
                        writer.Write(buffer,0,take);remaining-=take;
                    }
                    SaveStatus(status,initial,writer,checkpoint,raw,sourceHash,residualHash,
                               e.H,n,original,cursor,"initialized",watch.Elapsed.TotalSeconds,MemoryMB(),missing);
                }
            }
        }
        GC.Collect();GC.WaitForPendingFinalizers();GC.Collect();
        var state=new ulong[e.W];var output=new ulong[e.W];var row=new int[e.H];
        string reason="complete";double memory=MemoryMB();
        int stop=maxProcessed>0?Math.Min(maxProcessed,n):n;
        if(stop<cursor) throw new Exception("Source limit below committed boundary");
        Console.WriteLine(JsonSerializer.Serialize(new {phase="frozen loaded",states=n,
            processed_sources=cursor,blocks=states.Pool.Count,sparse_bytes=states.Data.Bytes,
            memory_mb=memory,seconds=watch.Elapsed.TotalSeconds}));
        using(var stream=new FileStream(raw,FileMode.Open,FileAccess.Write,FileShare.Read,1<<20))
        using(var writer=new BinaryWriter(stream))
        {
            stream.SetLength(80L+4L*e.H*cursor);stream.Position=stream.Length;
            while(cursor<stop)
            {
                if(cursor%1000==0 &&
                   (DateTime.UtcNow>=deadline || watch.Elapsed.TotalSeconds>=seconds || memory>memoryCap))
                {
                    reason=memory>memoryCap?"memory cap":"time cap";break;
                }
                states.Dense(cursor,state);
                for(int letter=1;letter<=e.H;letter++)
                {
                    int target=-1;
                    if(e.Step(state,letter,output))
                    {
                        target=states.Find(output,Hash(output));
                        if(target<0) missing++;
                    }
                    row[letter-1]=target;
                }
                foreach(int target in row) writer.Write(target);
                cursor++;
                if(cursor%10000==0)
                {
                    memory=MemoryMB();
                    Console.WriteLine(JsonSerializer.Serialize(new {phase="frozen transitions",
                        processed_sources=cursor,states=n,missing_fixed_set_targets=missing,
                        memory_mb=Math.Round(memory,1),seconds=Math.Round(watch.Elapsed.TotalSeconds,2)}));
                }
                if(cursor%50000==0)
                    SaveStatus(status,stream,writer,checkpoint,raw,sourceHash,residualHash,
                               e.H,n,original,cursor,"running",watch.Elapsed.TotalSeconds,memory,missing);
            }
            if(cursor==stop && cursor<n) reason="source cap";
            SaveStatus(status,stream,writer,checkpoint,raw,sourceHash,residualHash,
                       e.H,n,original,cursor,reason,watch.Elapsed.TotalSeconds,MemoryMB(),missing);
        }
        if(states.Count!=n) throw new Exception("Frozen state set changed");
    }
'''
(root/'SeaGraphFrozen.cs').write_text(header+'public static class SeaGraphFrozen\n{\n'+engine+hashcode+body+'\n}\n')
print('Generated frozen engine with unchanged residual transition and hash.')

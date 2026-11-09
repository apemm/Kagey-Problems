using System;
using System.Diagnostics;
using System.IO;
using System.Numerics;
using System.Security.Cryptography;
using System.Text.Json;

// Reads original graph rows directly; does not reuse the compressed power graph.
public static class SeaPerronWideCheck {
    static string Digest(string path) {
        using var stream=File.OpenRead(path);
        return Convert.ToHexString(SHA256.HashData(stream)).ToLowerInvariant();
    }
    public static void Run(string graphPath,string weightsPath,string output) {
        var watch=Stopwatch.StartNew();
        int n,count,component,h,bytes;long scale,lower,upper;
        int[] local;BigInteger[] weights;
        using(var reader=new BinaryReader(File.OpenRead(weightsPath))) {
            if(reader.ReadInt32()!=0x53505732) throw new Exception("Weight magic");
            n=reader.ReadInt32();count=reader.ReadInt32();component=reader.ReadInt32();
            h=reader.ReadInt32();bytes=reader.ReadInt32();
            scale=reader.ReadInt64();lower=reader.ReadInt64();upper=reader.ReadInt64();
            if(n<=0 || count<=0 || count>n || h<=0 || bytes<=0 || bytes>1024 || scale<=0 || lower>upper)
                throw new Exception("Weight header");
            if(reader.BaseStream.Length!=48L+(4L+bytes)*count) throw new Exception("Weight length");
            local=new int[n];Array.Fill(local,-1);weights=new BigInteger[count];
            int previous=-1;
            for(int k=0;k<count;k++) {
                int id=reader.ReadInt32();
                if(id<=previous || id>=n) throw new Exception("Weight vertex order");
                previous=id;local[id]=k;
                weights[k]=new BigInteger(reader.ReadBytes(bytes),true,false);
                if(weights[k]<=0) throw new Exception("Nonpositive weight");
            }
        }
        using(var reader=new BinaryReader(File.OpenRead(graphPath+".components"))) {
            if(reader.ReadInt32()!=n || reader.BaseStream.Length!=4L+4L*n)
                throw new Exception("Component length");
            for(int i=0;i<n;i++) if((reader.ReadInt32()==component)!=(local[i]>=0))
                throw new Exception("Component coverage");
        }
        int checkedRows=0;long checkedEdges=0;
        BigInteger minSlackLower=-1,minSlackUpper=-1;
        using(var reader=new BinaryReader(File.OpenRead(graphPath))) {
            if(reader.ReadInt32()!=0x53454731 || reader.ReadInt32()!=h || reader.ReadInt32()!=n)
                throw new Exception("Graph header");
            if(reader.BaseStream.Length!=12L+4L*h*n) throw new Exception("Graph length");
            for(int i=0;i<n;i++) {
                BigInteger total=0;
                for(int r=0;r<h;r++) {
                    int target=reader.ReadInt32();
                    if(target < -1 || target>=n) throw new Exception("Graph target");
                    if(local[i]>=0 && target>=0 && local[target]>=0) {
                        total+=weights[local[target]];checkedEdges++;
                    }
                }
                if(local[i]<0) continue;
                BigInteger slackLower=scale*total-lower*weights[local[i]];
                BigInteger slackUpper=upper*weights[local[i]]-scale*total;
                if(slackLower<0 || slackUpper<0) throw new Exception("Collatz inequality");
                if(minSlackLower<0 || slackLower<minSlackLower) minSlackLower=slackLower;
                if(minSlackUpper<0 || slackUpper<minSlackUpper) minSlackUpper=slackUpper;
                checkedRows++;
            }
        }
        if(checkedRows!=count) throw new Exception("Row coverage");
        var result=new {status="PASS",graph=Path.GetFileName(graphPath),height=h,states=n,
            component,component_size=count,checked_rows=checkedRows,checked_internal_edges=checkedEdges,
            scale,lower_numerator=lower,upper_numerator=upper,
            lower=(double)lower/scale,upper=(double)upper/scale,
            minimum_lower_slack=minSlackLower.ToString(),minimum_upper_slack=minSlackUpper.ToString(),
            graph_sha256=Digest(graphPath),component_sha256=Digest(graphPath+".components"),
            weights_sha256=Digest(weightsPath),elapsed_seconds=watch.Elapsed.TotalSeconds,
            peak_memory_mb=Process.GetCurrentProcess().PeakWorkingSet64/1048576.0};
        string json=JsonSerializer.Serialize(result,new JsonSerializerOptions{WriteIndented=true});
        File.WriteAllText(output,json+"\n");Console.WriteLine(json);
    }
}

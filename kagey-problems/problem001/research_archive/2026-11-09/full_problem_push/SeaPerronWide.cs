using System;
using System.Diagnostics;
using System.IO;
using System.Linq;
using System.Numerics;
using System.Security.Cryptography;
using System.Text.Json;

public static class SeaPerronWide {
    static string Hash(string path) {
        using var stream=File.OpenRead(path);
        return Convert.ToHexString(SHA256.HashData(stream)).ToLowerInvariant();
    }
    public static void Run(string graphPath,int componentId,int iterations,
                           double seconds,string output,string weightsPath) {
        var watch=Stopwatch.StartNew();
        int h,n;
        using(var reader=new BinaryReader(File.OpenRead(graphPath))) {
            if(reader.ReadInt32()!=0x53454731) throw new Exception("Graph magic");
            h=reader.ReadInt32();n=reader.ReadInt32();
            if(reader.BaseStream.Length!=12L+4L*h*n) throw new Exception("Graph length");
        }
        var map=new int[n];Array.Fill(map,-1);
        int count=0;
        using(var reader=new BinaryReader(File.OpenRead(graphPath+".components"))) {
            if(reader.ReadInt32()!=n || reader.BaseStream.Length!=4L+4L*n)
                throw new Exception("Component length");
            for(int i=0;i<n;i++) if(reader.ReadInt32()==componentId) map[i]=count++;
        }
        if(count==0) throw new Exception("Empty component");
        var vertices=new int[count];
        for(int i=0;i<n;i++) if(map[i]>=0) vertices[map[i]]=i;
        var edges=new int[checked(count*h)];
        using(var reader=new BinaryReader(File.OpenRead(graphPath))) {
            reader.BaseStream.Position=12;
            for(int i=0;i<n;i++) for(int r=0;r<h;r++) {
                int target=reader.ReadInt32();
                if(target < -1 || target>=n) throw new Exception("Edge target");
                if(map[i]>=0) edges[map[i]*h+r]=target<0?-1:map[target];
            }
        }
        map=null;
        var v=new double[count];Array.Fill(v,1.0);
        var w=new double[count];
        int completed=0;double low=0,high=h;
        for(int it=0;it<iterations;it++) {
            double norm=0;low=Double.PositiveInfinity;high=0;
            for(int i=0;i<count;i++) {
                double sum=v[i];
                for(int r=0;r<h;r++) {int j=edges[i*h+r];if(j>=0) sum+=v[j];}
                w[i]=sum;norm=Math.Max(norm,sum);
                double ratio=sum/v[i]-1;
                low=Math.Min(low,ratio);high=Math.Max(high,ratio);
            }
            for(int i=0;i<count;i++) w[i]/=norm;
            var swap=v;v=w;w=swap;completed=it+1;
            if(completed%10==0) {
                Console.WriteLine(JsonSerializer.Serialize(new {phase="power_wide",iteration=completed,
                    low,high,minimum=v.Min(),elapsed_seconds=watch.Elapsed.TotalSeconds}));
                if(high-low<1e-10 || watch.Elapsed.TotalSeconds>seconds) break;
            }
        }
        const long scale=1000000;
        var weights=new BigInteger[count];
        BigInteger minimum=BigInteger.Pow(10,60);
        for(int i=0;i<count;i++) {
            if(!Double.IsFinite(v[i]) || v[i]<=0) throw new Exception("Nonpositive iterate");
            weights[i]=BigInteger.Max(BigInteger.One,new BigInteger(v[i]*1e60));
            minimum=BigInteger.Min(minimum,weights[i]);
        }
        long lower=(long)Math.Floor(scale*low),upper=(long)Math.Ceiling(scale*high);
        for(int i=0;i<count;i++) {
            BigInteger sum=0;
            for(int r=0;r<h;r++) {int j=edges[i*h+r];if(j>=0) sum+=weights[j];}
            if(lower*weights[i]>scale*sum) lower=(long)(scale*sum/weights[i]);
            if(upper*weights[i]<scale*sum) upper=(long)((scale*sum+weights[i]-1)/weights[i]);
        }
        const int bytes=32;
        using(var writer=new BinaryWriter(File.Open(weightsPath,FileMode.CreateNew))) {
            writer.Write(0x53505732);writer.Write(n);writer.Write(count);
            writer.Write(componentId);writer.Write(h);writer.Write(bytes);
            writer.Write(scale);writer.Write(lower);writer.Write(upper);
            var buffer=new byte[bytes];
            for(int i=0;i<count;i++) {
                Array.Clear(buffer);
                if(!weights[i].TryWriteBytes(buffer,out int written,true,false))
                    throw new Exception("Weight overflow");
                writer.Write(vertices[i]);writer.Write(buffer);
            }
        }
        var result=new {status="EXACT_GENERATED",graph=Path.GetFileName(graphPath),height=h,states=n,
            component=componentId,component_size=count,iterations=completed,
            minimum_weight=minimum.ToString(),weight_scale="1e60",weight_bytes=bytes,
            scale,lower_numerator=lower,upper_numerator=upper,
            lower=(double)lower/scale,upper=(double)upper/scale,
            weights_file=Path.GetFileName(weightsPath),weights_sha256=Hash(weightsPath),
            graph_sha256=Hash(graphPath),component_sha256=Hash(graphPath+".components"),
            elapsed_seconds=watch.Elapsed.TotalSeconds,
            peak_memory_mb=Process.GetCurrentProcess().PeakWorkingSet64/1048576.0};
        string json=JsonSerializer.Serialize(result,new JsonSerializerOptions{WriteIndented=true});
        File.WriteAllText(output,json+"\n");Console.WriteLine(json);
    }
}

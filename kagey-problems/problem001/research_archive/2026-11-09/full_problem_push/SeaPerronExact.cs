using System;
using System.Diagnostics;
using System.IO;
using System.Linq;
using System.Text.Json;

public static class SeaPerronExact
{
    public static void Run(string graphPath,int componentId,int iterations,
                           double seconds,string output,string weightsPath)
    {
        var watch=Stopwatch.StartNew(); int h,n; int[] edges,component;
        using(var reader=new BinaryReader(File.OpenRead(graphPath)))
        {
            if(reader.ReadInt32()!=0x53454731) throw new Exception("Bad graph magic");
            h=reader.ReadInt32(); n=reader.ReadInt32();
            edges=new int[checked(h*n)];
            for(int i=0;i<edges.Length;i++) edges[i]=reader.ReadInt32();
            if(reader.BaseStream.Position!=reader.BaseStream.Length)
                throw new Exception("Trailing graph data");
        }
        using(var reader=new BinaryReader(File.OpenRead(graphPath+".components")))
        {
            if(reader.ReadInt32()!=n) throw new Exception("Component count mismatch");
            component=new int[n];
            for(int i=0;i<n;i++) component[i]=reader.ReadInt32();
            if(reader.BaseStream.Position!=reader.BaseStream.Length)
                throw new Exception("Trailing component data");
        }
        int count=component.Count(c=>c==componentId);
        if(count==0) throw new Exception("Empty component");
        var v=new double[n]; var w=new double[n];
        for(int i=0;i<n;i++) if(component[i]==componentId) v[i]=1;
        int completed=0; double low=0,high=h;
        for(int it=0;it<iterations;it++)
        {
            double norm=0; low=Double.PositiveInfinity; high=0;
            for(int i=0;i<n;i++)
            {
                if(component[i]!=componentId) continue;
                double sum=v[i]; int start=i*h;
                for(int r=0;r<h;r++)
                { int j=edges[start+r]; if(j>=0) sum+=v[j]; }
                w[i]=sum; if(sum>norm) norm=sum;
                double ratio=sum/v[i]-1;
                if(ratio<low) low=ratio;
                if(ratio>high) high=ratio;
            }
            for(int i=0;i<n;i++) if(component[i]==componentId) w[i]/=norm;
            var swap=v; v=w; w=swap; completed=it+1;
            if(completed%10==0)
            {
                Console.WriteLine(JsonSerializer.Serialize(new {
                    phase="power",iteration=completed,low=low,high=high,
                    elapsed_seconds=watch.Elapsed.TotalSeconds }));
                if(high-low<1e-10 || watch.Elapsed.TotalSeconds>seconds) break;
            }
        }
        const long weightScale=1000000000000L, boundScale=1000000L;
        var weights=new long[n]; long minimumWeight=weightScale;
        for(int i=0;i<n;i++) if(component[i]==componentId)
        {
            weights[i]=Math.Max(1L,(long)Math.Round(weightScale*v[i]));
            minimumWeight=Math.Min(minimumWeight,weights[i]);
        }
        long minN=0,minD=1,maxN=0,maxD=1; bool first=true;
        for(int i=0;i<n;i++)
        {
            if(component[i]!=componentId) continue;
            long sum=0; int start=i*h;
            for(int r=0;r<h;r++)
            { int j=edges[start+r]; if(j>=0) sum=checked(sum+weights[j]); }
            long denominator=weights[i];
            if(first || (Int128)sum*minD<(Int128)minN*denominator)
            { minN=sum; minD=denominator; }
            if(first || (Int128)sum*maxD>(Int128)maxN*denominator)
            { maxN=sum; maxD=denominator; }
            first=false;
        }
        long lower=(long)((Int128)minN*boundScale/minD);
        long upper=(long)(((Int128)maxN*boundScale+maxD-1)/maxD);
        for(int i=0;i<n;i++) if(component[i]==componentId)
        {
            long sum=0;
            for(int r=0;r<h;r++)
            { int j=edges[i*h+r]; if(j>=0) sum+=weights[j]; }
            if((Int128)lower*weights[i]>(Int128)boundScale*sum ||
               (Int128)upper*weights[i]<(Int128)boundScale*sum)
                throw new Exception("Exact Collatz verification failed");
        }
        using(var writer=new BinaryWriter(File.Open(weightsPath,FileMode.Create)))
        {
            writer.Write(0x53505731); writer.Write(n); writer.Write(componentId);
            foreach(long value in weights) writer.Write(value);
        }
        var result=new {
            graph=Path.GetFileName(graphPath),height=h,states=n,component=componentId,
            component_size=count,iterations=completed,minimum_weight=minimumWeight,
            scale=boundScale,lower_numerator=lower,upper_numerator=upper,
            lower=(double)lower/boundScale,upper=(double)upper/boundScale,
            exact_min_numerator=minN,exact_min_denominator=minD,
            exact_max_numerator=maxN,exact_max_denominator=maxD,
            weights_file=Path.GetFileName(weightsPath),
            graph_sha256=Convert.ToHexString(System.Security.Cryptography.SHA256.HashData(File.ReadAllBytes(graphPath))),
            elapsed_seconds=watch.Elapsed.TotalSeconds
        };
        File.WriteAllText(output,JsonSerializer.Serialize(result,new JsonSerializerOptions { WriteIndented=true })+"\n");
        Console.WriteLine(JsonSerializer.Serialize(result));
    }
}

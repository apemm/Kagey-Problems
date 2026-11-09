using System;
using System.IO;
using System.Collections.Generic;
using System.Text.Json;

public static class SeaGreedyCycles {
    public static void Run(string graph, int cid, string output) {
        using var source = new BinaryReader(File.OpenRead(graph));
        if(source.ReadInt32()!=0x53454731) throw new Exception("Graph format");
        int h=source.ReadInt32(), n=source.ReadInt32();
        var components=new int[n];
        using(var reader=new BinaryReader(File.OpenRead(graph+".components"))) {
            if(reader.ReadInt32()!=n) throw new Exception("Component size");
            for(int i=0;i<n;i++) components[i]=reader.ReadInt32();
        }
        var next=new int[n]; var letter=new byte[n];
        Array.Fill(next,-1);
        for(int i=0;i<n;i++) for(int r=1;r<=h;r++) {
            int j=source.ReadInt32();
            if(components[i]==cid && j>=0 && components[j]==cid && next[i]<0) {
                next[i]=j; letter[i]=(byte)r;
            }
        }
        var visit=new int[n]; var depth=new int[n]; var basin=new int[n];
        Array.Fill(basin,-1);
        var path=new List<int>();
        var cycles=new List<object>();
        var basinSizes=new List<int>();
        int walk=0, maximumWalk=0;
        for(int i=0;i<n;i++) {
            if(components[i]!=cid || visit[i]!=0) continue;
            walk++; path.Clear(); int j=i;
            while(visit[j]==0) {
                visit[j]=walk; depth[j]=path.Count; path.Add(j);
                if(next[j]<0) throw new Exception("Recurrent state without internal successor");
                j=next[j];
            }
            maximumWalk=Math.Max(maximumWalk,path.Count);
            int b;
            if(visit[j]==walk) {
                int begin=depth[j], length=path.Count-begin;
                b=cycles.Count;
                var word=new int[Math.Min(length,100)];
                for(int k=0;k<word.Length;k++) word[k]=letter[path[begin+k]];
                cycles.Add(new {id=b,length=length,state=j,word_prefix=word});
                basinSizes.Add(0);
            } else b=basin[j];
            foreach(int state in path) { basin[state]=b; basinSizes[b]++; }
        }
        var result=new {graph=Path.GetFileName(graph),component=cid,
            cycles=cycles,basin_sizes=basinSizes,maximum_new_walk=maximumWalk};
        string json=JsonSerializer.Serialize(result,new JsonSerializerOptions{WriteIndented=true});
        File.WriteAllText(output,json+"\n");
        Console.WriteLine(json);
    }
}

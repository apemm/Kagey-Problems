using System;
using System.IO;

public static class SeaFrozenCollisionCheck
{
    public static void Run()
    {
        const int words=465,n=256;
        var source=new SeaSparseStates(words);
        var all=new ulong[n][];
        for(int i=0;i<n;i++)
        {
            all[i]=new ulong[words];all[i][i%words]=(ulong)i+1;
            all[i][words-1]=(ulong)(i+1)*123456789UL;
            if(source.Intern(all[i],42UL)!=i) throw new Exception("Collision setup");
        }
        using(var stream=new MemoryStream())
        {
            using(var writer=new BinaryWriter(stream,System.Text.Encoding.UTF8,true))
                source.Write(writer);
            stream.Position=0;
            var copy=new SeaFrozenStates(words);
            using(var reader=new BinaryReader(stream,System.Text.Encoding.UTF8,true))
                copy.Read(reader,n);
            if(stream.Position!=stream.Length) throw new Exception("Trailing frozen bytes");
            int blocks=copy.Pool.Count;long bytes=copy.Data.Bytes;
            var dense=new ulong[words];
            for(int i=0;i<n;i++)
            {
                if(copy.Find(all[i],42UL)!=i) throw new Exception("Wrong collision lookup");
                copy.Dense(i,dense);
                for(int w=0;w<words;w++)
                    if(dense[w]!=all[i][w]) throw new Exception("Wrong dense state");
            }
            var absent=new ulong[words];absent[0]=777;
            if(copy.Find(absent,42UL)!=-1) throw new Exception("False collision equality");
            if(copy.Count!=n || copy.Pool.Count!=blocks || copy.Data.Bytes!=bytes)
                throw new Exception("Frozen query mutated the state set");
        }
        Console.WriteLine("PASS: 256 forced equal hashes, absent query, and immutable store.");
    }
}

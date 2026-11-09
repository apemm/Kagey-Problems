using System;
using System.IO;

public static class SeaSparseCollisionCheck
{
    public static void Run()
    {
        const int words=465,n=256;
        var store=new SeaSparseStates(words);
        var all=new ulong[n][];
        for(int i=0;i<n;i++)
        {
            all[i]=new ulong[words];
            all[i][i%words]=(ulong)i+1;
            all[i][words-1]=(ulong)(i+1)*123456789UL;
            if(store.Intern(all[i],42UL)!=i) throw new Exception("Collapsed equal hashes");
        }
        var output=new ulong[words];
        for(int i=0;i<n;i++)
        {
            if(store.Intern(all[i],42UL)!=i) throw new Exception("Wrong collision lookup");
            store.Dense(i,output);
            for(int j=0;j<words;j++) if(output[j]!=all[i][j])
                throw new Exception("Wrong collision reconstruction");
        }
        using(var stream=new MemoryStream())
        {
            using(var writer=new BinaryWriter(stream,System.Text.Encoding.UTF8,true))
                store.Write(writer);
            stream.Position=0;
            var copy=new SeaSparseStates(words);
            using(var reader=new BinaryReader(stream,System.Text.Encoding.UTF8,true))
                copy.Read(reader,n);
            if(stream.Position!=stream.Length) throw new Exception("Trailing data");
            for(int i=0;i<n;i++)
                if(copy.Intern(all[i],42UL)!=i)
                    throw new Exception("Wrong deserialized collision lookup");
        }
    }
}

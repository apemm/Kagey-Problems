using System;
using System.Collections.Generic;
using System.IO;

// These stores change representation only. Both hash tables compare complete
// keys after a hash match, so collisions never identify different states.
public sealed class SeaIntSlab
{
    private const int Shift=20, Size=1<<Shift, Mask=Size-1;
    private readonly List<int[]> chunks=new List<int[]>();
    public int Count { get; private set; }
    public int this[int i] { get { return chunks[i>>Shift][i&Mask]; } }
    public void Add(int value)
    {
        if((Count&Mask)==0) chunks.Add(new int[Size]);
        chunks[Count>>Shift][Count&Mask]=value; Count++;
    }
    public int[] ToArray()
    {
        var result=new int[Count];
        for(int i=0;i<chunks.Count;i++)
            Array.Copy(chunks[i],0,result,i*Size,Math.Min(Size,Count-i*Size));
        return result;
    }
    public void Write(BinaryWriter writer)
    {
        for(int i=0;i<Count;i++) writer.Write(this[i]);
    }
}

public sealed class SeaLongSlab
{
    private const int Shift=19, Size=1<<Shift, Mask=Size-1;
    private readonly List<ulong[]> chunks=new List<ulong[]>();
    public int Count { get; private set; }
    public ulong this[int i] { get { return chunks[i>>Shift][i&Mask]; } }
    public void Add(ulong value)
    {
        if((Count&Mask)==0) chunks.Add(new ulong[Size]);
        chunks[Count>>Shift][Count&Mask]=value; Count++;
    }
}

public struct SeaBlock256
{
    public ulong A,B,C,D;
    public SeaBlock256(ulong a,ulong b,ulong c,ulong d) { A=a; B=b; C=c; D=d; }
    public bool Same(SeaBlock256 b) { return A==b.A && B==b.B && C==b.C && D==b.D; }
    public ulong Hash()
    {
        ulong x=Mix(A+0x9e3779b97f4a7c15UL);
        x=Mix(x^B); x=Mix(x^C); return Mix(x^D);
    }
    private static ulong Mix(ulong z)
    {
        z=(z^(z>>30))*0xbf58476d1ce4e5b9UL;
        z=(z^(z>>27))*0x94d049bb133111ebUL;
        return z^(z>>31);
    }
}

public sealed class SeaBlockPool
{
    private const int Shift=17, Size=1<<Shift, Mask=Size-1;
    private readonly List<SeaBlock256[]> chunks=new List<SeaBlock256[]>();
    private int[] table=new int[1024];
    public int Count { get; private set; }
    public SeaBlock256 this[int i] { get { return chunks[i>>Shift][i&Mask]; } }
    private void Grow()
    {
        var replacement=new int[checked(table.Length*2)];
        int mask=replacement.Length-1;
        for(int i=0;i<Count;i++)
        {
            int slot=(int)(this[i].Hash()&(uint)mask);
            while(replacement[slot]!=0) slot=(slot+1)&mask;
            replacement[slot]=i+1;
        }
        table=replacement;
    }
    public int Intern(SeaBlock256 value)
    {
        if(Count+1>table.Length*0.72) Grow();
        int mask=table.Length-1,slot=(int)(value.Hash()&(uint)mask);
        while(table[slot]!=0)
        {
            int id=table[slot]-1;
            if(this[id].Same(value)) return id;
            slot=(slot+1)&mask;
        }
        int result=Count;
        if((Count&Mask)==0) chunks.Add(new SeaBlock256[Size]);
        chunks[Count>>Shift][Count&Mask]=value; Count++;
        table[slot]=result+1; return result;
    }
    public void Write(BinaryWriter writer)
    {
        writer.Write(Count);
        for(int i=0;i<Count;i++)
        { var b=this[i]; writer.Write(b.A);writer.Write(b.B);writer.Write(b.C);writer.Write(b.D); }
    }
    public void Read(BinaryReader reader)
    {
        int n=reader.ReadInt32();
        for(int i=0;i<n;i++)
        {
            int id=Intern(new SeaBlock256(reader.ReadUInt64(),reader.ReadUInt64(),
                                         reader.ReadUInt64(),reader.ReadUInt64()));
            if(id!=i) throw new Exception("Duplicate block in checkpoint");
        }
    }
}

public sealed class SeaPackedStates
{
    public readonly SeaBlockPool Pool=new SeaBlockPool();
    public readonly SeaIntSlab Blocks=new SeaIntSlab();
    public readonly SeaLongSlab Hashes=new SeaLongSlab();
    private int[] table=new int[1024];
    public int Words { get; private set; }
    public int Width { get; private set; }
    public int Count { get { return Hashes.Count; } }
    public SeaPackedStates(int words) { Words=words; Width=(words+3)/4; }
    private void Grow()
    {
        var replacement=new int[checked(table.Length*2)];
        int mask=replacement.Length-1;
        for(int i=0;i<Count;i++)
        {
            int slot=(int)(Hashes[i]&(uint)mask);
            while(replacement[slot]!=0) slot=(slot+1)&mask;
            replacement[slot]=i+1;
        }
        table=replacement;
    }
    private static SeaBlock256 Block(ulong[] value,int w)
    {
        return new SeaBlock256(value[w],w+1<value.Length?value[w+1]:0,
                               w+2<value.Length?value[w+2]:0,w+3<value.Length?value[w+3]:0);
    }
    private bool Equal(int id,ulong[] value)
    {
        int start=checked(id*Width);
        for(int j=0;j<Width;j++)
            if(!Pool[Blocks[start+j]].Same(Block(value,j*4))) return false;
        return true;
    }
    public int Intern(ulong[] value,ulong hash)
    {
        if(Count+1>table.Length*0.72) Grow();
        int mask=table.Length-1,slot=(int)(hash&(uint)mask);
        while(table[slot]!=0)
        {
            int id=table[slot]-1;
            if(Hashes[id]==hash && Equal(id,value)) return id;
            slot=(slot+1)&mask;
        }
        int result=Count;
        for(int j=0;j<Width;j++) Blocks.Add(Pool.Intern(Block(value,j*4)));
        Hashes.Add(hash); table[slot]=result+1; return result;
    }
    public void Dense(int id,ulong[] value)
    {
        int start=checked(id*Width);
        for(int j=0;j<Width;j++)
        {
            var b=Pool[Blocks[start+j]]; int w=j*4;
            value[w]=b.A;
            if(w+1<Words) value[w+1]=b.B;
            if(w+2<Words) value[w+2]=b.C;
            if(w+3<Words) value[w+3]=b.D;
        }
    }
    public void Write(BinaryWriter writer)
    {
        Pool.Write(writer); Blocks.Write(writer);
        for(int i=0;i<Count;i++) writer.Write(Hashes[i]);
    }
    public void Read(BinaryReader reader,int n)
    {
        Pool.Read(reader);
        for(int i=0;i<checked(n*Width);i++)
        {
            int id=reader.ReadInt32();
            if(id<0 || id>=Pool.Count) throw new Exception("Bad block identifier");
            Blocks.Add(id);
        }
        while(n>table.Length*0.72) table=new int[checked(table.Length*2)];
        int mask=table.Length-1;
        for(int i=0;i<n;i++)
        {
            ulong hash=reader.ReadUInt64(); Hashes.Add(hash);
            int slot=(int)(hash&(uint)mask);
            while(table[slot]!=0) slot=(slot+1)&mask;
            table[slot]=i+1;
        }
    }
}

using System;
using System.Collections.Generic;
using System.IO;
using System.Numerics;
using System.Runtime.InteropServices;

// No interning operation is exposed: this pool can only read and retrieve.
public sealed class SeaFrozenBlockPool
{
    private const int Shift=17, Size=1<<Shift, Mask=Size-1;
    private readonly List<SeaBlock256[]> chunks=new List<SeaBlock256[]>();
    public int Count {get; private set;}
    public SeaBlock256 this[int i] {
        get {
            if((uint)i>=(uint)Count) throw new Exception("Bad frozen block ID");
            return chunks[i>>Shift][i&Mask];
        }
    }
    public void Read(BinaryReader reader)
    {
        if(Count!=0) throw new Exception("Frozen pool already loaded");
        int n=reader.ReadInt32();
        if(n<=0 || Marshal.SizeOf<SeaBlock256>()!=32 || !BitConverter.IsLittleEndian)
            throw new Exception("Invalid frozen pool format");
        int remaining=n;
        while(remaining>0)
        {
            var block=new SeaBlock256[Size];
            int take=Math.Min(remaining,Size);
            reader.BaseStream.ReadExactly(MemoryMarshal.AsBytes(block.AsSpan(0,take)));
            chunks.Add(block);remaining-=take;
        }
        Count=n;
        if(!this[0].Same(new SeaBlock256(0,0,0,0)))
            throw new Exception("Missing zero block");
    }
}

// Immutable state set. Hash matches are resolved by complete 256-bit blocks.
public sealed class SeaFrozenStates
{
    public readonly SeaFrozenBlockPool Pool=new SeaFrozenBlockPool();
    public readonly SeaByteSlabs Data=new SeaByteSlabs();
    public readonly SeaLongSlab Offsets=new SeaLongSlab();
    public readonly SeaLongSlab Hashes=new SeaLongSlab();
    private int[] table;
    private readonly int maskBytes;
    public int Words {get; private set;}
    public int Width {get; private set;}
    public int Count {get {return Hashes.Count;}}
    public SeaFrozenStates(int words)
    {
        Words=words;Width=(words+3)/4;maskBytes=(Width+7)/8;
    }
    private static SeaBlock256 Block(ulong[] value,int w)
    {
        return new SeaBlock256(value[w],w+1<value.Length?value[w+1]:0,
                               w+2<value.Length?value[w+2]:0,w+3<value.Length?value[w+3]:0);
    }
    private bool Equal(int state,ulong[] value)
    {
        int at;byte[] data=Data.Get(Offsets[state],out at);
        int bits=data[at],cursor=at+1+maskBytes,used=0;
        ulong pending=0,mask=(1UL<<bits)-1;
        for(int j=0;j<Width;j++)
        {
            int id=0;
            if((data[at+1+(j>>3)]&(1<<(j&7)))!=0)
            {
                while(used<bits)
                {pending|=(ulong)data[cursor++]<<used;used+=8;}
                id=(int)(pending&mask);pending>>=bits;used-=bits;
            }
            if(!Pool[id].Same(Block(value,j*4))) return false;
        }
        return true;
    }
    public int Find(ulong[] value,ulong hash)
    {
        int mask=table.Length-1,slot=(int)(hash&(uint)mask);
        while(table[slot]!=0)
        {
            int id=table[slot]-1;
            if(Hashes[id]==hash && Equal(id,value)) return id;
            slot=(slot+1)&mask;
        }
        return -1;
    }
    public void Dense(int state,ulong[] value)
    {
        int at;byte[] data=Data.Get(Offsets[state],out at);
        int bits=data[at],cursor=at+1+maskBytes,used=0;
        ulong pending=0,mask=(1UL<<bits)-1;
        for(int j=0;j<Width;j++)
        {
            int id=0;
            if((data[at+1+(j>>3)]&(1<<(j&7)))!=0)
            {
                while(used<bits)
                {pending|=(ulong)data[cursor++]<<used;used+=8;}
                id=(int)(pending&mask);pending>>=bits;used-=bits;
            }
            var b=Pool[id];int w=j*4;
            value[w]=b.A;
            if(w+1<Words) value[w+1]=b.B;
            if(w+2<Words) value[w+2]=b.C;
            if(w+3<Words) value[w+3]=b.D;
        }
    }
    public void Read(BinaryReader reader,int n)
    {
        Pool.Read(reader);Data.Read(reader);
        for(int i=0;i<n;i++)
        {
            ulong offset=reader.ReadUInt64();
            int at;byte[] data=Data.Get(offset,out at);
            int bits=data[at];
            if(bits<1 || bits>31 || at+1+maskBytes>data.Length)
                throw new Exception("Bad sparse record header");
            int present=0;
            for(int j=0;j<maskBytes;j++) present+=BitOperations.PopCount((uint)data[at+1+j]);
            int length=1+maskBytes+(present*bits+7)/8;
            if(at+length>data.Length || offset+(ulong)length>(ulong)Data.Bytes)
                throw new Exception("Truncated sparse record");
            Offsets.Add(offset);
        }
        int capacity=1024;
        while(n>capacity*0.72) capacity=checked(capacity*2);
        table=new int[capacity];
        int mask=capacity-1;
        for(int i=0;i<n;i++)
        {
            ulong hash=reader.ReadUInt64();Hashes.Add(hash);
            int slot=(int)(hash&(uint)mask);
            while(table[slot]!=0) slot=(slot+1)&mask;
            table[slot]=i+1;
        }
    }
}

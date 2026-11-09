using System;
using System.Collections.Generic;
using System.IO;
using System.Numerics;

// Variable records use 64-bit byte offsets. A record never straddles a slab.
public sealed class SeaByteSlabs
{
    private const int Shift=24, Size=1<<Shift, Mask=Size-1;
    private readonly List<byte[]> chunks=new List<byte[]>();
    public long Bytes { get; private set; }
    public ulong Add(byte[] value,int length)
    {
        if(length<1 || length>Size) throw new ArgumentOutOfRangeException();
        int within=(int)(Bytes&Mask);
        if(within+length>Size) {Bytes=(Bytes+Mask)&~(long)Mask;within=0;}
        int slab=checked((int)(Bytes>>Shift));
        while(chunks.Count<=slab) chunks.Add(new byte[Size]);
        ulong offset=(ulong)Bytes;
        Array.Copy(value,0,chunks[slab],within,length);
        Bytes+=length;return offset;
    }
    public byte[] Get(ulong offset,out int within)
    {
        if(offset>=(ulong)Bytes) throw new Exception("Bad sparse record offset");
        within=(int)(offset&Mask);
        return chunks[checked((int)(offset>>Shift))];
    }
    public void Write(BinaryWriter writer)
    {
        writer.Write(Bytes);
        long remaining=Bytes;
        foreach(byte[] chunk in chunks)
        {
            int length=(int)Math.Min(remaining,Size);
            writer.Write(chunk,0,length);remaining-=length;
        }
        if(remaining!=0) throw new Exception("Byte slab length");
    }
    public void Read(BinaryReader reader)
    {
        if(Bytes!=0 || chunks.Count!=0) throw new Exception("Nonempty byte store");
        long size=reader.ReadInt64();
        if(size<0) throw new Exception("Negative byte size");
        long remaining=size;
        while(remaining>0)
        {
            var block=new byte[Size];
            int length=(int)Math.Min(remaining,Size),at=0;
            while(at<length)
            {
                int got=reader.Read(block,at,length-at);
                if(got==0) throw new EndOfStreamException();
                at+=got;
            }
            chunks.Add(block);remaining-=length;
        }
        Bytes=size;
    }
}

// Exact state interning: hash matches always compare all original 256-bit
// blocks. Sparse records change representation, never the state equivalence.
public sealed class SeaSparseStates
{
    public readonly SeaBlockPool Pool=new SeaBlockPool();
    public readonly SeaByteSlabs Data=new SeaByteSlabs();
    public readonly SeaLongSlab Offsets=new SeaLongSlab();
    public readonly SeaLongSlab Hashes=new SeaLongSlab();
    private int[] table=new int[1024];
    private readonly int[] ids;
    private readonly byte[] encoded;
    private readonly int maskBytes;
    public int Words {get; private set;}
    public int Width {get; private set;}
    public int Count {get {return Hashes.Count;}}
    public SeaSparseStates(int words)
    {
        Words=words;Width=(words+3)/4;maskBytes=(Width+7)/8;
        ids=new int[Width];encoded=new byte[1+maskBytes+4*Width];
    }
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
    private ulong AddIds()
    {
        int largest=0;
        foreach(int id in ids) if(id>largest) largest=id;
        int bits=Math.Max(1,32-BitOperations.LeadingZeroCount((uint)largest));
        Array.Clear(encoded,0,1+maskBytes);
        encoded[0]=(byte)bits;
        int cursor=1+maskBytes,used=0;ulong pending=0;
        for(int j=0;j<Width;j++)
        {
            uint id=(uint)ids[j];
            if(id==0) continue;
            encoded[1+(j>>3)]|=(byte)(1<<(j&7));
            pending|=(ulong)id<<used;used+=bits;
            while(used>=8)
            {encoded[cursor++]=(byte)pending;pending>>=8;used-=8;}
        }
        if(used>0) encoded[cursor++]=(byte)pending;
        return Data.Add(encoded,cursor);
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
        // Pool identifier zero is reserved for the zero block.
        if(Pool.Count==0 && Pool.Intern(new SeaBlock256(0,0,0,0))!=0)
            throw new Exception("Zero block initialization");
        for(int j=0;j<Width;j++) ids[j]=Pool.Intern(Block(value,j*4));
        int result=Count;
        Offsets.Add(AddIds());Hashes.Add(hash);table[slot]=result+1;
        return result;
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
    private void CheckZero()
    {
        if(Pool.Count==0 || !Pool[0].Same(new SeaBlock256(0,0,0,0)))
            throw new Exception("Checkpoint has no canonical zero block");
    }
    private void ReadHashes(BinaryReader reader,int n)
    {
        while(n>table.Length*0.72) table=new int[checked(table.Length*2)];
        int mask=table.Length-1;
        for(int i=0;i<n;i++)
        {
            ulong hash=reader.ReadUInt64();Hashes.Add(hash);
            int slot=(int)(hash&(uint)mask);
            while(table[slot]!=0) slot=(slot+1)&mask;
            table[slot]=i+1;
        }
    }
    // Import old format four sequentially. No flat n*Width vector is allocated.
    public void ReadPacked(BinaryReader reader,int n,Action<int> progress)
    {
        Pool.Read(reader);CheckZero();
        var row=new byte[4*Width];
        for(int i=0;i<n;i++)
        {
            int at=0;
            while(at<row.Length)
            {
                int got=reader.Read(row,at,row.Length-at);
                if(got==0) throw new EndOfStreamException();
                at+=got;
            }
            Buffer.BlockCopy(row,0,ids,0,row.Length);
            foreach(int id in ids)
                if(id<0 || id>=Pool.Count) throw new Exception("Bad packed block ID");
            Offsets.Add(AddIds());
            if(progress!=null && (i+1)%500000==0) progress(i+1);
        }
        ReadHashes(reader,n);
    }
    public void Write(BinaryWriter writer)
    {
        Pool.Write(writer);Data.Write(writer);
        for(int i=0;i<Count;i++) writer.Write(Offsets[i]);
        for(int i=0;i<Count;i++) writer.Write(Hashes[i]);
    }
    public void Read(BinaryReader reader,int n)
    {
        Pool.Read(reader);CheckZero();Data.Read(reader);
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
        ReadHashes(reader,n);
    }
}

using System;
using System.IO;
using System.Diagnostics;
using System.Numerics;
using System.Text.Json;

// A representation-only probe. Every stored record is decoded and compared
// against its complete original vector; no hash collision assumption is used.
public static class SeaSparseRecordProbe
{
    private static int Encode(int[] input, int start, int width, byte[] output)
    {
        int maskBytes=(width+7)/8, max=0;
        for(int i=0;i<width;i++) if(input[start+i]>max) max=input[start+i];
        int bits=Math.Max(1,32-BitOperations.LeadingZeroCount((uint)max));
        Array.Clear(output,0,output.Length);
        output[0]=(byte)bits;
        int cursor=1+maskBytes,used=0; ulong pending=0;
        for(int i=0;i<width;i++)
        {
            uint id=(uint)input[start+i];
            if(id==0) continue;
            output[1+(i>>3)]|=(byte)(1<<(i&7));
            pending|=(ulong)id<<used; used+=bits;
            while(used>=8)
            { output[cursor++]=(byte)pending; pending>>=8; used-=8; }
        }
        if(used>0) output[cursor++]=(byte)pending;
        return cursor;
    }
    private static void Decode(byte[] data,long at,int width,int[] output)
    {
        int bits=data[at],cursor=checked((int)(at+1+(width+7)/8)),used=0;
        ulong pending=0,mask=(1UL<<bits)-1;
        for(int i=0;i<width;i++)
        {
            if((data[at+1+(i>>3)]&(1<<(i&7)))==0) {output[i]=0;continue;}
            while(used<bits)
            {pending|=(ulong)data[cursor++]<<used;used+=8;}
            output[i]=(int)(pending&mask);pending>>=bits;used-=bits;
        }
    }
    public static string Run(string path,int requested,string mode,int repeats)
    {
        var all=Stopwatch.StartNew();
        int h,words,n,processed,edgeCount,pool;
        byte[] fingerprint;
        using(var r=new BinaryReader(File.OpenRead(path)))
        {
            if(r.ReadInt32()!=0x53454134) throw new Exception("Not a packed checkpoint");
            h=r.ReadInt32();words=r.ReadInt32();fingerprint=r.ReadBytes(32);
            n=r.ReadInt32();processed=r.ReadInt32();edgeCount=r.ReadInt32();pool=r.ReadInt32();
            for(int j=0;j<4;j++) if(r.ReadUInt64()!=0)
                throw new Exception("Pool identifier zero is not the zero block");
        }
        int width=(words+3)/4,count=Math.Min(requested,n);
        long stateStart=60L+32L*pool;
        if(new FileInfo(path).Length!=stateStart+4L*width*n+8L*n+4L*edgeCount)
            throw new Exception("Checkpoint dimensions");
        int[] flat=new int[checked(count*width)];
        byte[] bytes=new byte[4*width];
        using(var f=File.OpenRead(path))
            for(int i=0;i<count;i++)
            {
                int id=mode=="last"?n-count+i:
                       mode=="first"?i:(int)((long)i*(n-1)/Math.Max(1,count-1));
                f.Position=stateStart+4L*width*id;
                f.ReadExactly(bytes);
                Buffer.BlockCopy(bytes,0,flat,4*i*width,4*width);
            }
        var blob=new MemoryStream();
        var offsets=new long[count];
        var work=new byte[4*width+1+(width+7)/8];
        var bitWidths=new int[33];
        var timer=Stopwatch.StartNew();
        for(int i=0;i<count;i++)
        {
            offsets[i]=blob.Position;
            int length=Encode(flat,i*width,width,work);
            bitWidths[work[0]]++;
            blob.Write(work,0,length);
        }
        double encodeSeconds=timer.Elapsed.TotalSeconds;
        byte[] packed=blob.GetBuffer();
        var restored=new int[width];
        for(int i=0;i<count;i++)
        {
            Decode(packed,offsets[i],width,restored);
            for(int j=0;j<width;j++)
                if(restored[j]!=flat[i*width+j]) throw new Exception("Round-trip mismatch");
        }
        ulong checksum=0;
        timer.Restart();
        for(int repeat=0;repeat<repeats;repeat++)
            for(int i=0;i<count;i++)
            {Decode(packed,offsets[i],width,restored);checksum+=(uint)restored[i%width];}
        double decodeSeconds=timer.Elapsed.TotalSeconds;
        timer.Restart();
        for(int repeat=0;repeat<repeats;repeat++)
            for(int i=0;i<count;i++)
            {Array.Copy(flat,i*width,restored,0,width);checksum+=(uint)restored[i%width];}
        double flatCopySeconds=timer.Elapsed.TotalSeconds;
        return JsonSerializer.Serialize(new{
            checkpoint=Path.GetFileName(path),input_sha256=Convert.ToHexString(fingerprint).ToLowerInvariant(),
            height=h,width,total_states=n,sample_size=count,mode,
            flat_bytes=4L*width*count,packed_record_bytes=blob.Length,
            packed_plus_offsets_bytes=blob.Length+8L*count,
            bytes_per_state=(blob.Length+8.0*count)/count,
            memory_stream_allocated_capacity=blob.Capacity,bit_width_counts=bitWidths,
            encode_seconds=encodeSeconds,decode_repeats=repeats,decode_seconds=decodeSeconds,
            flat_copy_seconds=flatCopySeconds,checksum,
            roundtrip="PASS: every original block identifier compared",
            seconds=all.Elapsed.TotalSeconds,
            peak_working_set_mb=Process.GetCurrentProcess().PeakWorkingSet64/1048576.0
        });
    }
}

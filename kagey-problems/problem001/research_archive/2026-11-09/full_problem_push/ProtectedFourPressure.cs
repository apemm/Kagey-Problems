using System;
using System.Diagnostics;
using System.IO;
using System.Text.Json;

// Exact geometric count of compatible hidden and mixed four-cell supports.
// All counts are summed over four horizontal phases, before division by four.
public static class ProtectedFourPressure
{
    private static readonly ushort[][] Masks=MakeMasks();
    private static int Q(int r) { return (r&3)>=2?1:0; }
    private static bool Allowed(int phase,int x,int y)
    {
        if(phase==0) return (y&1)==0;
        if(phase==1) return ((x+y)&1)==0;
        return (Q(x)^Q(y))==0;
    }
    private static ushort[][] MakeMasks()
    {
        var result=new ushort[3][];
        for(int phase=0;phase<3;phase++)
        {
            result[phase]=new ushort[65536];
            for(int key=0;key<65536;key++)
            {
                int mask=0;
                for(int rx=0;rx<4;rx++) for(int ry=0;ry<4;ry++)
                {
                    bool ok=true;
                    for(int j=0;j<4;j++)
                    {
                        int p=(key>>(4*j))&15;
                        if(!Allowed(phase,rx+(p&3),ry+(p>>2))) { ok=false; break; }
                    }
                    if(ok) mask|=1<<(rx*4+ry);
                }
                result[phase][key]=(ushort)mask;
            }
        }
        return result;
    }
    private static int Point(int x,int y) { return (x&3)|((y&3)<<2); }
    private static void Add(long[] total,int h,int low,int high,
                            int x0,int y0,int x1,int y1,int x2,int y2,int x3,int y3)
    {
        if(x0==x1 || x0==x2 || x0==x3 || x1==x2 || x1==x3 || x2==x3) return;
        int first=1-low,last=h-high;
        if(first>last) return;
        int key=Point(x0,y0)|(Point(x1,y1)<<4)|(Point(x2,y2)<<8)|(Point(x3,y3)<<12);
        for(int phase=0;phase<3;phase++)
        {
            int mask=Masks[phase][key];
            for(int ry=0;ry<4;ry++)
            {
                int r0=first+((ry-first)&3);
                if(r0>last) continue;
                int multiplicity=0;
                for(int rx=0;rx<4;rx++) multiplicity+=(mask>>(4*rx+ry))&1;
                total[phase]+=(long)multiplicity*(1+(last-r0)/4);
            }
        }
    }
    private static int Gcd(int a,int b)
    { while(b!=0) { int t=a%b; a=b; b=t; } return a; }
    private static long Root(long n)
    {
        long z=(long)Math.Sqrt(n);
        while(z*z>n) z--;
        while((z+1)*(z+1)<=n) z++;
        return z;
    }
    private static void Mixed(long[] total,int h,int ux,int uy,int vx,int vy,int tx,int ty)
    {
        int c=(ux+vx)/2,d=(ux-vx)/2;
        int cy=(uy+vy)/2,dy=(uy-vy)/2;
        int low=Math.Min(Math.Min(0,uy),Math.Min(Math.Min(ty,ty+uy),Math.Min(cy,dy)));
        int high=Math.Max(Math.Max(0,uy),Math.Max(Math.Max(ty,ty+uy),Math.Max(cy,dy)));
        Add(total,h,low,high,tx,ty,tx+ux,ty+uy,c,cy,d,dy);
    }
    public static void Run(int h,string output)
    {
        if(h<4 || (h&3)!=0) throw new Exception("This probability report requires h divisible by four");
        var watch=Stopwatch.StartNew(); int H=h-1;
        var hidden=new long[3]; var mixed=new long[3];
        for(int a=1;a<=H;a++) for(int b=1;b<=H;b++) if(Gcd(a,b)==1)
        {
            for(int k=1;k*b<=H;k++) for(int l=1;k*b+l*a<=H;l++)
                Add(hidden,h,0,k*b+l*a,0,0,k*a,k*b,-l*b,l*a,k*a-l*b,k*b+l*a);
        }
        for(int a=1;a<=H;a++)
        {
            for(int b=-H;b<=H;b++) if(b!=0 && Gcd(a,Math.Abs(b))==1)
            for(int k=1;k*Math.Abs(b)<=H;k++)
            {
                int ux=k*a,uy=k*b; long norm=(long)ux*ux+(long)uy*uy;
                for(int vy=-H;vy<=H;vy++)
                {
                    if(((uy-vy)&1)!=0) continue;
                    long square=norm-(long)vy*vy;
                    if(square<=0) continue;
                    int vx=(int)Root(square);
                    if((long)vx*vx!=square || ((ux-vx)&1)!=0 || (vx==ux && vy==uy)) continue;
                    // With positive horizontal components, V=-U is impossible.
                    for(int l=-H/a;l<=H/a;l++) if(l!=0)
                        Mixed(mixed,h,ux,uy,vx,vy,-l*b,l*a);
                }
            }
            if(a%32==0) Console.WriteLine(JsonSerializer.Serialize(new {
                height=h,primitive_horizontal=a,seconds=watch.Elapsed.TotalSeconds }));
        }
        // Horizontal side. Enumerate (u-z)(u+z)=v_y^2 exactly.
        for(int vy=-H;vy<=H;vy++) if(vy!=0 && (vy&1)==0)
        {
            int square=vy*vy;
            for(int d=1;d*d<square;d++) if(square%d==0)
            {
                int e=square/d;
                if(((d+e)&1)!=0) continue;
                int ux=(d+e)/2,vx=(e-d)/2;
                if(((ux-vx)&1)!=0) continue;
                for(int ty=-H;ty<=H;ty++) if(ty!=0)
                    Mixed(mixed,h,ux,0,vx,vy,0,ty);
            }
        }
        double denominator=4*Math.Pow(h/2.0,4);
        var result=new {
            height=h,phases=new[]{"ordinary","checkerboard","quadratic"},
            four_times_hidden_count=hidden,four_times_mixed_count=mixed,
            hidden_mean=new[]{hidden[0]/denominator,hidden[1]/denominator,hidden[2]/denominator},
            mixed_mean=new[]{mixed[0]/denominator,mixed[1]/denominator,mixed[2]/denominator},
            seconds=watch.Elapsed.TotalSeconds
        };
        File.WriteAllText(output,JsonSerializer.Serialize(result,new JsonSerializerOptions {WriteIndented=true})+"\n");
        Console.WriteLine(JsonSerializer.Serialize(result));
    }
}

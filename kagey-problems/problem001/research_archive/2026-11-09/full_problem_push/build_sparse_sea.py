"""Create a separate sparse-record driver from the audited packed engine."""
from pathlib import Path

root = Path(__file__).resolve().parent
source = (root / "SeaGraphPacked.cs").read_text()
source = source.replace("public static class SeaGraphPacked", "public static class SeaGraphSparse")
source = source.replace("SeaPackedStates", "SeaSparseStates")
source = source.replace("writer.Write(0x53454134)", "writer.Write(0x53454135)")
start = source.index("                int magic=reader.ReadInt32();")
end = source.index("                for(int i=0;i<nEdges;i++)", start)
source = source[:start] + r'''
                int magic=reader.ReadInt32();
                if((magic!=0x53454134 && magic!=0x53454135) ||
                    reader.ReadInt32()!=e.H || reader.ReadInt32()!=e.W)
                    throw new Exception("Checkpoint mismatch");
                if(!reader.ReadBytes(32).SequenceEqual(fingerprint))
                    throw new Exception("Residual-table fingerprint mismatch");
                int n=reader.ReadInt32();cursor=reader.ReadInt32();
                int nEdges=reader.ReadInt32();
                if(magic==0x53454135) states.Read(reader,n);
                else states.ReadPacked(reader,n,loaded=>Console.WriteLine(
                    JsonSerializer.Serialize(new{
                        phase="streaming packed import",loaded,states=n,
                        sparse_bytes=states.Data.Bytes,blocks=states.Pool.Count,
                        memory_mb=Math.Round(MemoryMB(),1),
                        seconds=Math.Round(watch.Elapsed.TotalSeconds,2)})));
''' + source[end:]
source = source.replace('phase="saving packed checkpoint"', 'phase="saving sparse checkpoint"')
source = source.replace("blocks=states.Pool.Count,memory_mb=", "blocks=states.Pool.Count,sparse_bytes=states.Data.Bytes,memory_mb=")
source = source.replace("if(graph.Complete) components=Components(graph,binary);",
    "if(graph.Complete) { GC.Collect(); GC.WaitForPendingFinalizers(); GC.Collect(); components=Components(graph,binary); }")
# Preserve the preceding complete checkpoint if writing is interrupted.
source = source.replace("new FileStream(path,FileMode.Create,FileAccess.Write)",
                        'new FileStream(path+".pending",FileMode.Create,FileAccess.Write)', 1)
save_end = source.index("    private static Graph Build(")
before = source[:save_end]
needle = "        }\n    }\n"
at = before.rfind(needle)
assert at >= 0
before = before[:at] + '        }\n        File.Move(path+".pending",path,true);\n    }\n' + before[at+len(needle):]
source = before + source[save_end:]
(root / "SeaGraphSparse.cs").write_text(source)

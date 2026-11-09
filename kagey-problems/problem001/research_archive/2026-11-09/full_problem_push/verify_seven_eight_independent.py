"""Independent geometry, first-column coverage and symmetry audit at 7 by 8."""
from pathlib import Path
from hashlib import sha256
import importlib.util
import json

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[2]
H,W=7,8

def reflect_mask(mask):
    return sum(1<<(6-y) for y in range(H) if mask>>y&1)

def reflect_board(black):
    return sum(1<<((6-y)*W+x) for y in range(H) for x in range(W)
               if black>>(y*W+x)&1)

def main():
    complete={}
    hashes={}
    for path in sorted(HERE.glob("seven_eight_independent_*shard_*.jsonl")):
        data=path.read_bytes()
        hashes[path.name]=sha256(data).hexdigest()
        for line in data.splitlines():
            record=json.loads(line)
            if record["status"]!="complete":
                continue
            mask=record["mask"]
            models=set(map(lambda s:int(s,16),record["models"]))
            assert len(models)==record["count"]==len(record["models"])
            for black in models:
                assert black.bit_count()==16
                assert sum(1<<y for y in range(H) if black>>(y*W)&1)==mask
            if mask in complete:
                assert complete[mask]==models
            complete[mask]=models
    covered={}
    sources={}
    for mask in range(128):
        if mask.bit_count()<2 or mask.bit_count()>4:
            covered[mask]=set()
            sources[mask]="analytical boundary/large-column bound"
        if mask in complete:
            if mask in covered:
                assert not complete[mask]
            covered[mask]=complete[mask]
            sources[mask]="completed direct SAT"
        mirror=reflect_mask(mask)
        if mirror in complete:
            reflected={reflect_board(b) for b in complete[mirror]}
            if mask in covered:
                assert covered[mask]==reflected
            covered[mask]=reflected
            if mask not in complete:
                sources[mask]=f"vertical reflection of completed mask {mirror}"
    boards=set().union(*covered.values()) if covered else set()
    assert sum(map(len,covered.values()))==len(boards)
    source=ROOT/"jis/scripts/table_counts_search.py"
    spec=importlib.util.spec_from_file_location("independent_side_geometry",source)
    module=importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    rects=[sum(1<<(y*W+x) for x,y in rect)
           for rect in module.all_rectangles(H,W)]
    assert len(rects)==866
    for black in boards:
        assert len({r&~black for r in rects})==len(rects)
    oldpath=ROOT/"jis/data/table_counts/sat2split_7x8_16.json"
    old=json.loads(oldpath.read_text())[0]
    assert len(old["first_models"])==old["count"]==18
    oldboards={sum(1<<((y-1)*W+x-1) for x,y in model)
               for model in old["first_models"]}
    missing=sorted(set(range(128))-covered.keys())
    result=dict(status="PASS" if not missing else "PARTIAL",
                height=H,width=W,optimum=16,
                optimum_count=len(boards) if not missing else None,
                verified_count_lower_bound=len(boards),
                completed_direct_masks=len(complete),
                covered_masks=len(covered),missing_masks=missing,
                rectangles=len(rects),
                matches_old_board_set=(boards==oldboards),
                new_boards_not_in_old=sorted(hex(b) for b in boards-oldboards),
                boards=sorted(hex(b) for b in boards),
                coverage_sources=sources,source_sha256=hashes,
                scope="Independent 4/6-support encoding and equal-diagonal generation; "
                      "completed direct masks, exact vertical reflections, and proved "
                      "boundary/large-column exclusions. Board verification here uses "
                      "the independent perpendicular-vector rectangle generator. "
                      "SAT exhaustion has no separate DRAT certificate.")
    for path in (source,oldpath,HERE/"independent_seven_eight_count.py",
                 HERE/"verify_seven_eight_independent.py"):
        hashes[str(path.relative_to(ROOT))]=sha256(path.read_bytes()).hexdigest()
    (HERE/"seven_eight_independent_check.json").write_text(
        json.dumps(result,indent=2)+"\n",encoding="utf-8")
    print(json.dumps({k:v for k,v in result.items()
                      if k not in ("boards","coverage_sources","source_sha256")},
                     indent=2))

if __name__=="__main__":
    main()


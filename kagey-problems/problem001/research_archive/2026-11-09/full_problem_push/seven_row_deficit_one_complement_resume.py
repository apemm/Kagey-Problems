"""Resume independently completed cores or prioritize a known neighboring witness core."""
from pathlib import Path
import hashlib
import json
import multiprocessing as mp
import sys

import seven_row_deficit_one_complement_sat as base


def main():
    # First five arguments have the base runner's semantics. Remaining items
    # are completed result filenames; --first=N changes only search order.
    args=sys.argv[:6]
    if len(args)<6:raise SystemExit('width total per_core solver tag [result.json ...] [--first=N]')
    skipped=set();sources=[];first=None;only=None
    for arg in sys.argv[6:]:
        if arg.startswith('--indices='):
            only=set(map(int,arg.split('=',1)[1].split(',')));continue
        if arg.startswith('--first='):
            first=int(arg.split('=',1)[1]);continue
        path=Path(arg)
        if not path.is_absolute():path=base.HERE/path
        data=json.loads(path.read_text())
        assert data['height']==7 and data['width']==int(args[1])
        assert data['target']==int(args[1])+11 and data['cores']==base.catalog()
        skipped.update(r['index'] for r in data['results'] if r['status']=='UNSAT')
        sources.append({'file':path.name,'sha256':hashlib.sha256(path.read_bytes()).hexdigest()})
    original=base.priority
    def order(records):
        result=[i for i in original(records) if i not in skipped and (only is None or i in only)]
        if first is not None and first in result:result=[first]+[i for i in result if i!=first]
        return result
    base.priority=order;sys.argv=args;base.main()
    path=base.HERE/f'deficit_one_h7_w{args[1]}_{args[5]}_{args[4]}.json'
    data=json.loads(path.read_text())
    data['resume_sources']=sources;data['skipped_completed_unsat_indices']=sorted(skipped)
    data['source_sha256'][Path(__file__).name]=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    path.write_text(json.dumps(data,indent=2)+'\n')


if __name__=='__main__':mp.freeze_support();main()

"""Independently verify a complete reflection-reduced partition comparison."""
from concurrent.futures import ThreadPoolExecutor, as_completed
from itertools import combinations
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import time

HERE=Path(__file__).resolve().parent


def reflection(part):
    return tuple(sorted(8-r for r in part))


def verify(part):
    if part==(2,4,6):
        stem='sea_packed_h7'
    elif part in ((1,3,6),(1,4,6)):
        stem='sea_packed_h7_p'+''.join(map(str,part))
    else:
        stem='sea_packed_h7_p'+''.join(map(str,part))+'_s10'
    report_path=HERE/(stem+'.json')
    report=json.loads(report_path.read_text())
    assert report['complete']
    assert len(report['components']['cyclic_components'])==1
    cid=report['components']['cyclic_components'][0]['id']
    certificate=HERE/f'{stem}.perron.{cid}.json'
    spectral=json.loads(certificate.read_text())
    for script,argument in [('verify_sea_scc.py',report_path),
                            ('verify_sea_perron.py',certificate)]:
        result=subprocess.run([sys.executable,str(HERE/script),str(argument)],
                              capture_output=True,text=True)
        assert result.returncode==0,(script,stem,result.stdout,result.stderr)
    suffix=stem.removeprefix('sea_packed_h7')
    input_path=HERE/('sea_residuals_h7'+suffix+'.json')
    inputs=json.loads(input_path.read_text())
    # The first default-parity export predates the explicit metadata field.
    # Every nondefault export must identify its partition.
    if stem=='sea_packed_h7':
        given=tuple(inputs.get('partition',[1,3,5,7]))
    else:
        given=tuple(inputs['partition'])
    assert given==part or tuple(r for r in range(1,8) if r not in given)==part
    truncated=inputs['geometry'].get('truncation_span')
    if part in ((2,4,6),(1,3,6),(1,4,6)):
        assert truncated is None
    else:
        assert truncated==10
    return dict(part=list(part),reflection=list(reflection(part)),
                orbit_size=1 if reflection(part)==part else 2,
                graph=stem,full_graph=truncated is None,
                truncation_span=truncated,states=report['states'],
                component_size=spectral['component_size'],
                lower_numerator=spectral['lower_numerator'],
                upper_numerator=spectral['upper_numerator'],scale=spectral['scale'],
                lower=spectral['lower'],upper=spectral['upper'],
                graph_sha256=spectral['graph_sha256'],
                input_sha256=hashlib.sha256(input_path.read_bytes()).hexdigest(),
                independent_scc='PASS',independent_integer_spectral='PASS')


def main():
    started=time.monotonic()
    all_parts=list(combinations(range(1,8),3))
    representatives=sorted({min(part,reflection(part)) for part in all_parts})
    assert len(all_parts)==35 and len(representatives)==19
    records=[]
    with ThreadPoolExecutor(max_workers=2) as executor:
        jobs={executor.submit(verify,part):part for part in representatives}
        for job in as_completed(jobs):
            record=job.result()
            records.append(record)
            print(json.dumps({k:record[k] for k in ('part','full_graph','lower','upper')}),flush=True)
    records.sort(key=lambda r:r['part'])
    assert sum(r['orbit_size'] for r in records)==35
    candidates=[r for r in records if r['full_graph']]
    winners=[]
    for candidate in candidates:
        if all(candidate['lower_numerator']*other['scale']>
               other['upper_numerator']*candidate['scale']
               for other in records if other is not candidate):
            winners.append(candidate)
    assert len(winners)==1
    result=dict(status='PASS',height=7,balanced_partitions=35,
                reflection_classes=19,records=records,
                unique_maximizing_reflection_class=winners[0]['part'],
                maximizing_labeled_partitions=[winners[0]['part'],winners[0]['reflection']],
                seconds=time.monotonic()-started,
                scope='All balanced partitions. Truncated graphs omit longer true constraints and give upper bounds.')
    (HERE/'height_seven_partition_comparison.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='records'}),flush=True)


if __name__=='__main__':
    main()

// Exact candidate-permutation search. No hidden rectangle is rejected unless
// another rectangle has the same empty presentation.
const fs = require('fs');
const path = require('path');
const dataFile=process.argv[4] || 'seven_nine_search_data.json';
const data = JSON.parse(fs.readFileSync(path.join(__dirname,dataFile),'utf8'));
const capSeconds = Number(process.argv[2] || 120);
const startIndex = Number(process.argv[3] || 0);
const useHorizontalReflection = !process.argv.includes('--no-horizontal');
const started = Date.now(), deadline = started + 1000*capSeconds;
const columns = new Int32Array(9), seen = new Uint8Array(4160);
let nodes=0, leaves=0, timedOut=false, witness=null;
const completed=[];
let currentIndex=startIndex;

function runPattern(masks) {
  const adjacency = new Int32Array(7);
  const singletonRivals = new Int32Array(128);
  let tripleIndex=-1;
  for(let i=0;i<9;i++) {
    const mask=masks[i];
    if(mask.toString(2).split('1').length-1===3) tripleIndex=i;
    for(let r=0;r<7;r++) if(mask&(1<<r)) adjacency[r]|=mask&~(1<<r);
  }
  for(const mask of masks)
    for(let r=0;r<7;r++) if(mask&(1<<r)) singletonRivals[mask]|=adjacency[r];
  seen.fill(0);
  const before=nodes;

  function visit(x,used) {
    nodes++;
    if((nodes&4095)===0 && Date.now()>deadline) { timedOut=true; return false; }
    if(x===9) {
      leaves++;
      witness=Array.from(columns);
      return true;
    }
    for(let i=0;i<9;i++) {
      if(used&(1<<i)) continue;
      // Select the last triple in this sorted multiset. Horizontal reflection
      // places that column in positions 0..4, even if another triple exists.
      if(useHorizontalReflection && tripleIndex>=0 && x===4 && !(used&(1<<tripleIndex)) && i!==tripleIndex) continue;
      if(useHorizontalReflection && tripleIndex>=0 && x>4 && i===tripleIndex) continue;
      const mask=masks[i]; columns[x]=mask;
      const changed=[];
      let valid=true;
      for(const rect of data.templates_by_last_column[x]) {
        let whiteCount=0, x1=0,r1=0,x2=0,r2=0;
        for(let j=0;j<8;j+=2) {
          const cx=rect[j], row=rect[j+1];
          if(!(columns[cx]&(1<<row))) {
            if(whiteCount===0) {x1=cx;r1=row;}
            else if(whiteCount===1) {x2=cx;r2=row;}
            if(++whiteCount===3) break;
          }
        }
        if(whiteCount>=3) continue;
        let key=0;
        if(whiteCount===1) {
          if(singletonRivals[columns[x1]]&(1<<r1)) {valid=false;break;}
          key=1+r1*9+x1;
        } else if(whiteCount===2) {
          if(x1===x2) {
            if(adjacency[r1]&(1<<r2)) {valid=false;break;}
          } else if(r1===r2) {
            if(columns[x1]&columns[x2]) {valid=false;break;}
          } else if((columns[x1]&(1<<r2)) && (columns[x2]&(1<<r1))) {
            valid=false;break;
          }
          let p=r1*9+x1,q=r2*9+x2;
          if(p>q) [p,q]=[q,p];
          key=64+p*64+q;
        }
        if(seen[key]) {valid=false;break;}
        seen[key]=1; changed.push(key);
      }
      if(valid && visit(x+1,used|(1<<i))) return true;
      for(const key of changed) seen[key]=0;
      if(timedOut) return false;
    }
    return false;
  }
  const sat=visit(0,0);
  return {index:currentIndex,nodes:nodes-before,status:sat?'SAT':timedOut?'incomplete':'UNSAT'};
}

for(currentIndex=startIndex;currentIndex<data.patterns.length;currentIndex++) {
  const result=runPattern(data.patterns[currentIndex]);
  completed.push(result);
  if((currentIndex-startIndex)%50===0) console.log(JSON.stringify({pattern:currentIndex,nodes,seconds:(Date.now()-started)/1000,status:result.status}));
  if(witness || timedOut) break;
}
const output={
  status:witness?'SAT':timedOut?'incomplete':'UNSAT',
  start_index:startIndex,last_index:Math.min(currentIndex,data.patterns.length-1),
  total_representatives:data.patterns.length,
  nodes,leaves,seconds:(Date.now()-started)/1000,
  horizontal_reflection:useHorizontalReflection?'selected triple, if present, placed in first five columns':'none',
  completed_patterns:completed,
  witness_column_masks:witness,
  witness_one_based:witness?Array.from({length:9},(_,x)=>Array.from({length:7},(_,r)=>r).filter(r=>witness[x]&(1<<r)).map(r=>[x+1,r+1])).flat():null
};
fs.writeFileSync(path.join(__dirname,`${data.output_tag || 'seven_nine_search'}_${startIndex}${useHorizontalReflection?'':'_no_horizontal'}.json`),JSON.stringify(output,null,2)+'\n');
console.log(JSON.stringify({...output,completed_patterns:undefined}));

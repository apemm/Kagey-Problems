// Exact finite ordering search for supplied, axis-valid column multisets.
const fs=require('fs'),path=require('path');
const data=JSON.parse(fs.readFileSync(path.join(__dirname,process.argv[2]),'utf8'));
const cap=Number(process.argv[3]||300),start=Number(process.argv[4]||0);
const h=data.rows,w=data.columns,N=h*w,firstPair=N+1;
if(h>15||w>20)throw Error('This implementation requires h<=15 and w<=20');
const begin=Date.now(),deadline=begin+1000*cap;
const columns=new Uint16Array(w),seen=new Uint8Array(firstPair+N*N);
const prefixBlack=new Uint16Array(w+1),cropBounds=data.known_width_upper||null;
const cropLengths=cropBounds?Object.keys(cropBounds).map(Number).filter(x=>x>0):[];
const weights=new Uint8Array(1<<h);
for(let mask=1;mask<weights.length;mask++)weights[mask]=weights[mask>>1]+(mask&1);
let nodes=0,timedOut=false,witness=null,index=start;
const completed=[];

function solve(masks){
  const adj=new Uint16Array(h),single=new Uint16Array(1<<h);
  let selected=-1;
  for(let i=0;i<w;i++){
    const mask=masks[i];
    if(weights[mask]===3)selected=i;
    for(let r=0;r<h;r++)if(mask&(1<<r))adj[r]|=mask&~(1<<r);
  }
  for(const mask of masks)for(let r=0;r<h;r++)if(mask&(1<<r))single[mask]|=adj[r];
  const half=Math.floor((w-1)/2),before=nodes;
  seen.fill(0);
  function dfs(x,used){
    nodes++;
    if(!(nodes&8191)&&Date.now()>deadline){timedOut=true;return false;}
    if(x===w){witness=Array.from(columns);return true;}
    let previous=-1;
    for(let i=0;i<w;i++){
      if(used&(1<<i))continue;
      if(selected>=0&&x===half&&!(used&(1<<selected))&&i!==selected)continue;
      if(selected>=0&&x>half&&i===selected)continue;
      const mask=masks[i];
      if(mask===previous)continue;
      previous=mask;columns[x]=mask;
      if(cropBounds){
        prefixBlack[x+1]=prefixBlack[x]+weights[mask];
        const remaining=w-x-1;
        if(cropBounds[remaining]!==undefined &&
           data.black_points-prefixBlack[x+1]>cropBounds[remaining])continue;
        let cropAllowed=true;
        for(const length of cropLengths){
          if(length<=x+1 && prefixBlack[x+1]-prefixBlack[x+1-length]>cropBounds[length]){
            cropAllowed=false;break;
          }
        }
        if(!cropAllowed)continue;
      }
      const changed=[];
      let legal=true;
      for(const R of data.templates_by_last_column[x]){
        let count=0,c1=0,r1=0,c2=0,r2=0;
        for(let j=0;j<8;j+=2){
          const c=R[j],r=R[j+1];
          if(!(columns[c]&(1<<r))){
            if(!count){c1=c;r1=r;}else if(count===1){c2=c;r2=r;}
            if(++count===3)break;
          }
        }
        if(count>=3)continue;
        let key=0;
        if(count===1){
          if(single[columns[c1]]&(1<<r1)){legal=false;break;}
          key=1+r1*w+c1;
        }else if(count===2){
          if(c1===c2?!!(adj[r1]&(1<<r2)):
            r1===r2?!!(columns[c1]&columns[c2]):
            !!((columns[c1]&(1<<r2))&&(columns[c2]&(1<<r1)))){legal=false;break;}
          const p=r1*w+c1,q=r2*w+c2;
          key=firstPair+Math.min(p,q)*N+Math.max(p,q);
        }
        if(seen[key]){legal=false;break;}
        seen[key]=1;changed.push(key);
      }
      if(legal&&dfs(x+1,used|(1<<i)))return true;
      for(const key of changed)seen[key]=0;
      if(timedOut)return false;
    }
    return false;
  }
  const sat=dfs(0,0);
  return {index,nodes:nodes-before,status:sat?'SAT':timedOut?'incomplete':'UNSAT'};
}
for(index=start;index<data.patterns.length;index++){
  const result=solve(data.patterns[index]);completed.push(result);
  if((index-start)%500===0)console.log(JSON.stringify({index,nodes,seconds:(Date.now()-begin)/1000}));
  if(witness||timedOut)break;
}
const output={status:witness?'SAT':timedOut?'incomplete':'UNSAT',rows:h,columns:w,
  black_points:data.black_points,start_index:start,last_index:Math.min(index,data.patterns.length-1),
  representatives:data.patterns.length,nodes,seconds:(Date.now()-begin)/1000,
  cropped_subboard_bounds:cropBounds,
  witness_column_masks:witness,witness_column_word:witness?witness.map(mask=>
    Array.from({length:h},(_,r)=>r+1).filter(r=>mask&(1<<(r-1))).join('')).join(','):null,
  completed_patterns:completed};
fs.writeFileSync(path.join(__dirname,`${data.output_tag}_${start}.json`),JSON.stringify(output,null,2)+'\n');
console.log(JSON.stringify({...output,completed_patterns:undefined}));

// Independent upper-bound check using every rectangle, including axis rectangles.
// It uses no axis-rival lemma and no horizontal-reflection reduction.
const fs=require('fs'),path=require('path');
const patterns=JSON.parse(fs.readFileSync(path.join(__dirname,'seven_nine_eighteen_data.json'),'utf8')).patterns;
const rectangles=JSON.parse(fs.readFileSync(path.join(__dirname,'seven_nine_all_rectangles.json'),'utf8'));
const startIndex=Number(process.argv[3]||0),capSeconds=Number(process.argv[2]||480);
const begin=Date.now(),deadline=begin+capSeconds*1000;
const assigned=new Uint8Array(9),visibleKeys=new Uint8Array(4160);
let nodes=0,stopped=false,witness=null,index=startIndex;
const completed=[];

function search(word){
  visibleKeys.fill(0);
  const before=nodes;
  function extend(depth,unused){
    nodes++;
    if(!(nodes&8191) && Date.now()>deadline){stopped=true;return false;}
    if(depth===9){witness=Array.from(assigned);return true;}
    let previousMask=-1;
    for(let j=0;j<9;j++){
      if(!(unused&(1<<j)) || word[j]===previousMask)continue;
      previousMask=word[j];assigned[depth]=word[j];
      const fresh=[];
      let allowed=true;
      for(const corners of rectangles[depth]){
        let first=-1,second=-1,count=0;
        for(let k=0;k<8;k+=2){
          const c=corners[k],r=corners[k+1];
          if(!(assigned[c]&(1<<r))){
            if(!count)first=r*9+c;
            else if(count===1)second=r*9+c;
            if(++count>=3)break;
          }
        }
        if(count>=3)continue;
        let key;
        if(!count)key=0;
        else if(count===1)key=first+1;
        else key=64+64*Math.min(first,second)+Math.max(first,second);
        if(visibleKeys[key]){allowed=false;break;}
        visibleKeys[key]=1;fresh.push(key);
      }
      if(allowed && extend(depth+1,unused^(1<<j)))return true;
      for(const key of fresh)visibleKeys[key]=0;
      if(stopped)return false;
    }
    return false;
  }
  const sat=extend(0,511);
  return {index,nodes:nodes-before,status:sat?'SAT':stopped?'incomplete':'UNSAT'};
}
for(index=startIndex;index<patterns.length;index++){
  const result=search(patterns[index]);completed.push(result);
  if((index-startIndex)%1000===0)console.log(JSON.stringify({index,nodes,seconds:(Date.now()-begin)/1000}));
  if(stopped||witness)break;
}
const output={status:witness?'SAT':stopped?'incomplete':'UNSAT',start_index:startIndex,
  last_index:Math.min(index,patterns.length-1),representatives:patterns.length,
  nodes,seconds:(Date.now()-begin)/1000,horizontal_reflection:false,
  constraints:'direct distinct visible presentations of all 1113 rectangles',
  witness,completed_patterns:completed};
fs.writeFileSync(path.join(__dirname,`seven_nine_direct_${startIndex}.json`),JSON.stringify(output,null,2)+'\n');
console.log(JSON.stringify({...output,completed_patterns:undefined}));

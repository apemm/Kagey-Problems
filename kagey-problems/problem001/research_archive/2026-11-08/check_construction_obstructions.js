'use strict';
const assert = require('node:assert/strict');
const sub=(a,b)=>[a[0]-b[0],a[1]-b[1]];
const add=(a,b)=>[a[0]+b[0],a[1]+b[1]];
const dot=(a,b)=>a[0]*b[0]+a[1]*b[1];
const eq=(a,b)=>a[0]===b[0]&&a[1]===b[1];
const key=p=>p.join(',');
function mixed(A,B,C,D) {
  const U=sub(B,A), V=sub(D,C), delta=sub(add(A,B),add(C,D));
  assert.equal(dot(U,U),dot(V,V)); assert.equal(dot(delta,U),0);
  return [sub(add(C,D),U).map(x=>x/2),add(add(C,D),U).map(x=>x/2)];
}
function rightAngles(points) {
  const out=[];
  for(let j=0;j<points.length;j++) for(let i=0;i<points.length;i++)
    for(let k=i+1;k<points.length;k++) if(i!==j&&k!==j)
      if(dot(sub(points[i],points[j]),sub(points[k],points[j]))===0)
        out.push([points[i],points[j],points[k]]);
  return out;
}
const T=[[0,3],[4,11],[0,4],[8,8]];
assert.deepEqual(mixed(...T),[[2,2],[6,10]]);
assert.equal(rightAngles([...T,[4,2],[8,1]]).length,0);
const Q=[[0,9],[4,13],[8,5],[12,1]];
assert.deepEqual(mixed(...Q),[[8,1],[12,5]]);
assert.equal(rightAngles([...Q,[0,2],[4,4],[8,6],[12,8]]).length,0);
for(let d=1;d<=19;d+=2) {
  const r=d+2,i=7,h=r+8*d;
  const whites=mixed([4*i,r],[4*(i+d),r+8*d],[4*i,r+d],[4*(i+2*d),r+5*d]);
  assert.deepEqual(whites,[[4*i+2*d,r-d],[4*i+6*d,r+7*d]]);
  for(const [x,y] of whites) {assert.equal(x%4,2);assert(y>1&&y<h);}
}
const counts=[];
for(let h=3;h<=15;h++) {
  let feasible=0;
  for(let b=1;b<h;b++) for(let d=1;b+d<h;d++)
    for(let a=4;a<=b*d;a+=4) if(b*d%a===0) {
      const c=b*d/a;if(c%4)continue;
      const R=[[0,b+1],[a,1],[a+c,d+1],[c,b+d+1]];
      for(let t=0;t<4;t++) {
        const W=R[t],Z=R[(t+1)%4];
        const blacks=[R[(t+2)%4],R[(t+3)%4],[W[0],Z[1]],[Z[0],W[1]]];
        if(blacks.some(p=>eq(p,W)||eq(p,Z)))continue;
        const cols=new Map();
        for(const [x,y] of blacks) {if(!cols.has(x))cols.set(x,new Set());cols.get(x).add(y);}
        if([...cols.values()].some(s=>s.size>2||(s.size===2&&[...s][0]%2===[...s][1]%2)))continue;
        feasible++;
      }
    }
  counts.push({h,feasible});
}
assert.equal(counts.find(x=>x.feasible).h,13);
console.log(JSON.stringify({status:'passed',T_no_three_black_right_angle:true,Q_no_three_black_right_angle:true,scaled_mixed_cases:10,Q_shape_counts:counts},null,2));

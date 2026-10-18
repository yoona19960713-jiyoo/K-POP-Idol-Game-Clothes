/* K-POP Idol Game ・ 換裝組裝模組
   工坊與遊戲衣櫥間共用。輸入身體層、關鍵點與單品圖層,輸出組好的造型畫面。
   座標一律用 0~1 的比例(相對整張圖),所以不同解析度的圖也能共用。 */
(function(global){
"use strict";

/* 關鍵點:左右指「畫面上的左右」 */
const MARKS=[
  ["headTop","頭頂",.50,.06,"body"],["earL","左耳",.43,.15,"body"],["earR","右耳",.57,.15,"body"],["chin","下巴",.50,.20,"body"],
  ["neck","頸根",.50,.23,"body"],["shL","左肩",.37,.26,"body"],["shR","右肩",.63,.26,"body"],
  ["apL","左腋下",.40,.33,"body"],["apR","右腋下",.60,.33,"body"],["elL","左手肘",.32,.42,"body"],["elR","右手肘",.68,.42,"body"],
  ["wrL","左手腕",.30,.53,"body"],["wrR","右手腕",.70,.53,"body"],["waL","左腰",.41,.40,"body"],["waR","右腰",.59,.40,"body"],
  ["hiL","左臀側",.38,.48,"body"],["hiR","右臀側",.62,.48,"body"],["crotch","胯下",.50,.53,"body"],
  ["knL","左膝",.43,.70,"body"],["knR","右膝",.57,.70,"body"],["anL","左腳踝",.43,.88,"body"],["anR","右腳踝",.57,.88,"body"],
  ["toeL","左腳尖",.42,.95,"body"],["toeR","右腳尖",.58,.95,"body"],
  ["eyeL","左眼",.46,.13,"face"],["eyeR","右眼",.54,.13,"face"],["lips","嘴唇",.50,.18,"face"],["chL","左臉頰",.45,.16,"face"],["chR","右臉頰",.55,.16,"face"],
];
const BODY_KEYS=MARKS.filter(m=>m[4]==="body").map(m=>m[0]);
const BORDER=[[0,0],[.5,0],[1,0],[0,.25],[1,.25],[0,.5],[1,.5],[0,.75],[1,.75],[0,1],[.5,1],[1,1]];
function defaultMarks(){const o={};MARKS.forEach(([k,,x,y])=>o[k]={x,y});return o}
function fill(m){const d=defaultMarks();return Object.fromEntries(MARKS.map(([k])=>[k,m&&m[k]?m[k]:d[k]]))}

/* 圖層順序(數字大的在上面) */
const Z={long:80,mid:80,short:80,updo:80,special:72,
  hosiery:30,socks:32,shoes:34,pants:40,skirt:42,top:50,dress:52,outer:60,
  waist:62,neck:64,hand:66,ear:75,head:85,held:90};
const Z_BACK={long:10,mid:10,short:10,updo:10};
const Z_BODY=20, Z_MAKEUP=70;

/* 圖片快取 */
const imgCache=new Map();
function loadImage(src){
  if(!src) return Promise.resolve(null);
  if(imgCache.has(src)) return imgCache.get(src);
  const p=new Promise(ok=>{const im=new Image();im.onload=()=>ok(im);im.onerror=()=>ok(null);im.src=src});
  imgCache.set(src,p); return p;
}
let imgId=0; const ids=new WeakMap(); const idOf=o=>{if(!ids.has(o))ids.set(o,++imgId);return ids.get(o)};

/* Delaunay 三角化(Bowyer-Watson) */
function delaunay(pts){
  const big=[{x:-10,y:-10},{x:10,y:-10},{x:0,y:10}];
  const P=[...pts,...big]; const n=pts.length;
  let tris=[[n,n+1,n+2]];
  const circ=t=>{const [a,b,c]=t.map(i=>P[i]);const d=2*(a.x*(b.y-c.y)+b.x*(c.y-a.y)+c.x*(a.y-b.y));
    if(Math.abs(d)<1e-12) return {x:0,y:0,r:Infinity};
    const ux=((a.x*a.x+a.y*a.y)*(b.y-c.y)+(b.x*b.x+b.y*b.y)*(c.y-a.y)+(c.x*c.x+c.y*c.y)*(a.y-b.y))/d;
    const uy=((a.x*a.x+a.y*a.y)*(c.x-b.x)+(b.x*b.x+b.y*b.y)*(a.x-c.x)+(c.x*c.x+c.y*c.y)*(b.x-a.x))/d;
    return {x:ux,y:uy,r:(a.x-ux)**2+(a.y-uy)**2}};
  for(let i=0;i<n;i++){
    const p=P[i]; const bad=[],keep=[];
    for(const t of tris){const c=circ(t);((p.x-c.x)**2+(p.y-c.y)**2<c.r?bad:keep).push(t)}
    const edges=[];
    for(const t of bad) for(const [a,b] of [[t[0],t[1]],[t[1],t[2]],[t[2],t[0]]]){
      const j=edges.findIndex(e=>(e[0]===b&&e[1]===a)||(e[0]===a&&e[1]===b));
      j>=0?edges.splice(j,1):edges.push([a,b]);
    }
    tris=keep.concat(edges.map(([a,b])=>[a,b,i]));
  }
  return tris.filter(t=>t.every(i=>i<n));
}
const triCache=new Map();
function meshPoints(m){return BODY_KEYS.map(k=>m[k]).concat(BORDER.map(([x,y])=>({x,y})))}
function trianglesFor(src){
  const key=JSON.stringify(src); if(triCache.has(key)) return triCache.get(key);
  const t=delaunay(meshPoints(src)); triCache.set(key,t); return t;
}

/* 分片仿射變形:把在標準底模上畫的單品,對齊到成員身上 */
function warpTo(img,src,dst,W,H){
  const c=document.createElement("canvas"); c.width=W; c.height=H; const g=c.getContext("2d");
  const sp=meshPoints(src), dp=meshPoints(dst), iw=img.naturalWidth, ih=img.naturalHeight;
  for(const [i,j,k] of trianglesFor(src)){
    const s=[sp[i],sp[j],sp[k]].map(p=>[p.x*iw,p.y*ih]);
    const d=[dp[i],dp[j],dp[k]].map(p=>[p.x*W,p.y*H]);
    const [[x0,y0],[x1,y1],[x2,y2]]=s, [[u0,v0],[u1,v1],[u2,v2]]=d;
    const den=x0*(y1-y2)+x1*(y2-y0)+x2*(y0-y1); if(Math.abs(den)<1e-9) continue;
    const a=(u0*(y1-y2)+u1*(y2-y0)+u2*(y0-y1))/den, cc=(u0*(x2-x1)+u1*(x0-x2)+u2*(x1-x0))/den,
          e=(u0*(x1*y2-x2*y1)+u1*(x2*y0-x0*y2)+u2*(x0*y1-x1*y0))/den;
    const b=(v0*(y1-y2)+v1*(y2-y0)+v2*(y0-y1))/den, dd=(v0*(x2-x1)+v1*(x0-x2)+v2*(x1-x0))/den,
          f=(v0*(x1*y2-x2*y1)+v1*(x2*y0-x0*y2)+v2*(x0*y1-x1*y0))/den;
    const cx=(u0+u1+u2)/3, cy=(v0+v1+v2)/3;
    g.save(); g.beginPath();
    d.forEach(([u,v],n)=>{const l=Math.hypot(u-cx,v-cy)||1;const X=u+(u-cx)/l*1.2,Y=v+(v-cy)/l*1.2;n?g.lineTo(X,Y):g.moveTo(X,Y)});
    g.closePath(); g.clip(); g.setTransform(a,b,cc,dd,e,f); g.drawImage(img,0,0); g.restore();
  }
  return c;
}
function plain(img,W,H){const c=document.createElement("canvas");c.width=W;c.height=H;c.getContext("2d").drawImage(img,0,0,W,H);return c}
function bboxCenter(c){
  const s=4,w=Math.ceil(c.width/s),h=Math.ceil(c.height/s);
  const t=document.createElement("canvas");t.width=w;t.height=h;const g=t.getContext("2d");g.drawImage(c,0,0,w,h);
  const d=g.getImageData(0,0,w,h).data;let x0=w,y0=h,x1=-1,y1=-1;
  for(let y=0;y<h;y++)for(let x=0;x<w;x++)if(d[(y*w+x)*4+3]>16){if(x<x0)x0=x;if(x>x1)x1=x;if(y<y0)y0=y;if(y>y1)y1=y}
  return x1<0?{x:c.width/2,y:c.height/2}:{x:(x0+x1+1)/2*s,y:(y0+y1+1)/2*s};
}
const layerCache=new Map();
async function prepared(src,warp,srcMarks,dstMarks,W,H){
  const img=await loadImage(src); if(!img) return null;
  const key=idOf(img)+"|"+(warp?JSON.stringify([srcMarks,dstMarks]):"plain")+"|"+W+"x"+H;
  if(layerCache.has(key)) return layerCache.get(key);
  const c=warp?warpTo(img,srcMarks,dstMarks,W,H):plain(img,W,H);
  const v={c,center:bboxCenter(c)};
  if(layerCache.size>120) layerCache.delete(layerCache.keys().next().value);
  layerCache.set(key,v); return v;
}

/* 程式上色的妝容(預覽用初版) */
function drawMakeup(g,mk,m,W,H){
  const P=k=>({x:m[k].x*W,y:m[k].y*H});
  const eL=P("eyeL"),eR=P("eyeR"); const D=Math.hypot(eR.x-eL.x,eR.y-eL.y)||W*.08;
  const a=mk.adj||{}, s=a.s||1, ox=(a.dx||0)*W, oy=(a.dy||0)*H;
  g.save(); g.globalCompositeOperation="multiply"; g.fillStyle=mk.hex||"#d77a8a";
  const blob=(x,y,rx,ry,alpha)=>{const gr=g.createRadialGradient(0,0,0,0,0,1);
    gr.addColorStop(0,hexA(mk.hex,alpha));gr.addColorStop(1,hexA(mk.hex,0));
    g.save();g.translate(x+ox,y+oy);g.scale(rx*s,ry*s);g.fillStyle=gr;g.beginPath();g.arc(0,0,1,0,Math.PI*2);g.fill();g.restore()};
  if(mk.kind==="cheek"){const c1=P("chL"),c2=P("chR");blob(c1.x,c1.y,D*.34,D*.24,.38);blob(c2.x,c2.y,D*.34,D*.24,.38)}
  if(mk.kind==="eye"){blob(eL.x,eL.y-D*.1,D*.3,D*.14,.45);blob(eR.x,eR.y-D*.1,D*.3,D*.14,.45)}
  if(mk.kind==="lip"){const l=P("lips");blob(l.x,l.y,D*.3,D*.12,.6)}
  g.restore();
}
function hexA(h,a){h=(h||"#d77a8a").replace("#","");if(h.length===3)h=h.split("").map(c=>c+c).join("");
  const n=parseInt(h,16);return `rgba(${n>>16&255},${n>>8&255},${n&255},${a})`}

/* 去背:把純色背景(綠/洋紅/藍)轉成透明,並去掉邊緣色偏 */
function chromaKey(src,key,lo=30,hi=90){
  const c=document.createElement("canvas"); c.width=src.naturalWidth||src.width; c.height=src.naturalHeight||src.height;
  const g=c.getContext("2d"); g.drawImage(src,0,0); const im=g.getImageData(0,0,c.width,c.height), d=im.data;
  for(let i=0;i<d.length;i+=4){
    let r=d[i],gg=d[i+1],b=d[i+2],k;
    if(key==="magenta") k=Math.min(r,b)-gg; else if(key==="blue") k=b-Math.max(r,gg); else k=gg-Math.max(r,b);
    if(k<=lo) continue;
    const a=k>=hi?0:1-(k-lo)/(hi-lo);
    if(key==="magenta"){const m=Math.min(r,b)-gg;d[i]=r-m;d[i+2]=b-m}
    else if(key==="blue"){d[i+2]=Math.max(r,gg)}
    else{d[i+1]=Math.max(r,b)}
    d[i+3]=Math.round(d[i+3]*a);
  }
  g.putImageData(im,0,0); return c;
}
const keyedCache=new Map();
async function keyedImage(src,key){
  const id=src+"|"+key; if(keyedCache.has(id)) return keyedCache.get(id);
  const p=loadImage(src).then(im=>im?chromaKey(im,key):null); keyedCache.set(id,p); return p;
}

/* 主函式
   opts.body      身體層圖片(成員的組裝用底模);opts.bodyKey 給 "green" 等色時先去背
   opts.stdMarks  標準底模的關鍵點;opts.marks 成員的關鍵點
   opts.layers    [{front,back,z,zBack,warp,adj:{dx,dy,s,r}}]
   opts.makeup    [{kind:"eye"|"lip"|"cheek",hex,adj}]
   opts.width     輸出寬度(高度依身體層比例) */
async function compose(canvas,opts){
  const body=opts.bodyKey?await keyedImage(opts.body,opts.bodyKey):await loadImage(opts.body);
  const bw=body?(body.naturalWidth||body.width):2, bh=body?(body.naturalHeight||body.height):3;
  const W=opts.width||600, H=Math.round(W*bh/bw);
  const sm=fill(opts.stdMarks), dm=fill(opts.marks);
  const list=[];
  if(body) list.push({z:Z_BODY,draw:g=>g.drawImage(body,0,0,W,H)});
  for(const L of opts.layers||[]){
    for(const [src,z] of [[L.front,L.z],[L.back,L.zBack]]){
      if(!src) continue;
      const p=await prepared(src,!!L.warp,sm,dm,W,H); if(!p) continue;
      const a=L.adj||{};
      list.push({z,draw:g=>{g.save();g.translate(p.center.x+(a.dx||0)*W,p.center.y+(a.dy||0)*H);g.rotate((a.r||0)*Math.PI/180);
        g.scale(a.s||1,a.s||1);g.translate(-p.center.x,-p.center.y);g.drawImage(p.c,0,0);g.restore()}});
    }
  }
  for(const mk of opts.makeup||[]) list.push({z:Z_MAKEUP,draw:g=>drawMakeup(g,mk,dm,W,H)});
  list.sort((a,b)=>a.z-b.z);
  canvas.width=W; canvas.height=H; const g=canvas.getContext("2d"); g.clearRect(0,0,W,H);
  for(const it of list) it.draw(g);
  return canvas;
}

global.Wardrobe={MARKS,BODY_KEYS,Z,Z_BACK,Z_BODY,Z_MAKEUP,defaultMarks,fill,loadImage,chromaKey,compose};
})(window);

// Bucketed levelled closure: masks grouped by cost, so level k only pairs buckets summing to k-1.
// usage: ./closure2 <n> <kmax>        prints one line per level
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
typedef unsigned __int128 u128;
static u128 *key; static int32_t *cost; static uint64_t cap, used;
static u128 **bk; static uint64_t *bl, *bc;   // per-cost buckets
static inline uint64_t h(u128 x){uint64_t a=(uint64_t)x,b=(uint64_t)(x>>64);a^=b*0x9e3779b97f4a7c15ULL;a^=a>>29;a*=0xbf58476d1ce4e5b9ULL;a^=a>>32;return a;}
static uint64_t MAXM=12000000;
static int32_t* find(u128 x,int ins){
  uint64_t i=h(x)&(cap-1);
  while(cost[i]>=0){ if(key[i]==x) return &cost[i]; i=(i+1)&(cap-1); }
  if(!ins) return NULL;
  if(used>=MAXM) return NULL;            /* memory guard: stop growing rather than die */
  key[i]=x; cost[i]=-1; used++; return &cost[i];
}
static void push(int32_t c, u128 m){
  if(bl[c]==bc[c]){ bc[c]=bc[c]?bc[c]*2:64; bk[c]=realloc(bk[c],bc[c]*sizeof(u128)); }
  bk[c][bl[c]++]=m;
}
int main(int argc,char**argv){
  int n=argc>1?atoi(argv[1]):5, kmax=argc>2?atoi(argv[2]):9;
  if(getenv("CLOSURE_MAXM")) MAXM=strtoull(getenv("CLOSURE_MAXM"),0,10);
  int64_t N=1LL<<n; cap=1<<22; used=0;
  key=aligned_alloc(64,cap*sizeof(u128)); cost=malloc(cap*sizeof(int32_t));
  for(uint64_t i=0;i<cap;i++) cost[i]=-1;
  int C=64; bk=malloc(C*sizeof(u128*)); bl=calloc(C,sizeof(uint64_t)); bc=calloc(C,sizeof(uint64_t));
  for(int i=0;i<C;i++) bk[i]=NULL;
  for(int i=0;i<n;i++){ u128 m=0; for(int64_t idx=0;idx<N;idx++) if((idx>>i)&1) m|=(u128)1<<idx; int32_t*p=find(m,1); *p=0; push(0,m); }
  { int32_t*p=find(0,1); *p=1; push(1,0); }
  printf("n=%d k=0 total=%llu\n",n,(unsigned long long)used); fflush(stdout);
  for(int k=1;k<=kmax;k++){
    uint64_t before=used;
    for(int ca=0;ca<=k-1;ca++){ int cb=k-1-ca; if(cb>C-1) continue;
      for(uint64_t i=0;i<bl[ca];i++) for(uint64_t j=(ca==cb?i:0);j<bl[cb];j++){
        u128 a=bk[ca][i], b=bk[cb][j];
        for(int op=0;op<2;op++){ u128 r=op?(a|b):(a&b); int32_t*p=find(r,1); if(p&&*p<0){ *p=k; push(k,r); } }
      }
    }
    printf("n=%d k=%d new=%llu total=%llu\n",n,k,(unsigned long long)(used-before),(unsigned long long)used); fflush(stdout);
    if(used==before) break;
  }
  if(getenv("CLOSURE_DUMP")){
    FILE*f=fopen(getenv("CLOSURE_DUMP"),"w");
    for(uint64_t i=0;i<cap;i++) if(cost[i]>=0)
      fprintf(f,"%016llx%016llx %d\n",(unsigned long long)(key[i]>>64),(unsigned long long)key[i],cost[i]);
    fclose(f); fprintf(stderr,"dumped to %s\n",getenv("CLOSURE_DUMP"));
  }
  return 0;
}

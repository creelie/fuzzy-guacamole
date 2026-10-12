// Certificate streams for LiuCheck.run12: for each (t1,t2), the boxes (t3,t4) in the order of
// boxesOf, each written as a count followed by greedy-chosen k (base-2048 digits).
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <omp.h>
#define Q 1389
#define B 8
#define L 4096
#define W 64
static inline int wt(int k,int a1,int a2,int a3,int a4){ int r1=k*a1%Q,r2=k*a2%Q,r3=k*a3%Q,r4=k*a4%Q; return r1&&r2&&r3&&r4&&r1+r2+r3+r4<=Q-1; }
int main(int argc,char**argv){
  const char*dir=argv[1];
  #pragma omp parallel for schedule(dynamic,1)
  for(int t1=0;t1<87;t1++){
    char fn[512]; sprintf(fn,"%s/t1_%02d.txt",dir,t1); FILE*f=fopen(fn,"w");
    int *least=malloc(sizeof(int)*L); unsigned char *valid=malloc(L);
    uint64_t cov[W], *bs=malloc(8*W*(size_t)1400); int cand[1400]; char iscand[1400];
    int *dg=malloc(sizeof(int)*2000000);
    for(int t2=0;t2<=t1;t2++){
      int x1=1+B*t1,x2=1+B*t2; if(2*x1+x2+2>Q) continue;
      int nd=0;
      for(int t3=0;t3<=t2;t3++) for(int t4=0;t4<=t3;t4++){
        int x3=1+B*t3,x4=1+B*t4;
        if(2*x1+x2+x3+x4>Q) continue;
        int nv=0;
        for(int l=0;l<L;l++){
          int d1=l%B,d2=(l/B)%B,d3=(l/B/B)%B,d4=l/B/B/B;
          int a1=x1+d1,a2=x2+d2,a3=x3+d3,a4=x4+d4,a0=Q-a1-a2-a3-a4;
          valid[l]=(a1>=a2&&a2>=a3&&a3>=a4&&a0>=a1);
          if(!valid[l]) continue; nv++;
          int k; for(k=2;k<=Q-2;k++) if(wt(k,a1,a2,a3,a4)) break;
          if(k>Q-2){ fprintf(stderr,"NO WITNESS\n"); exit(1);} least[l]=k;
        }
        memset(iscand,0,1400); int nc=0;
        for(int l=0;l<L;l++) if(valid[l]&&!iscand[least[l]]){ iscand[least[l]]=1; cand[nc++]=least[l]; }
        for(int c=0;c<nc;c++){ int k=cand[c]; uint64_t*b=bs+(size_t)c*W; memset(b,0,8*W);
          for(int l=0;l<L;l++) if(valid[l]){
            int d1=l%B,d2=(l/B)%B,d3=(l/B/B)%B,d4=l/B/B/B;
            if(wt(k,x1+d1,x2+d2,x3+d3,x4+d4)) b[l>>6]|=1ULL<<(l&63); } }
        memset(cov,0,8*W); int need=nv; int ks[300], nk=0;
        while(need>0){ int best=-1,bc=-1;
          for(int c=0;c<nc;c++){ int cnt=0; uint64_t*b=bs+(size_t)c*W;
            for(int w=0;w<W;w++) cnt+=__builtin_popcountll(b[w]&~cov[w]); if(cnt>bc){bc=cnt;best=c;} }
          uint64_t*b=bs+(size_t)best*W; for(int w=0;w<W;w++) cov[w]|=b[w]; need-=bc; ks[nk++]=cand[best]; }
        if(nk>2047){ fprintf(stderr,"too many\n"); exit(1);} 
        dg[nd++]=nk; for(int i=0;i<nk;i++) dg[nd++]=ks[i];
      }
      fprintf(f,"%d %d %d",t1,t2,nd); for(int i=0;i<nd;i++) fprintf(f," %d",dg[i]); fprintf(f,"\n");
    }
    fclose(f);
  }
}

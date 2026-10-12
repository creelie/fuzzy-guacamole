#include <stdio.h>
#include <stdlib.h>
static int g(int a,int b){while(b){int t=a%b;a=b;b=t;}return a;}
int main(int argc,char**argv){
  int q=atoi(argv[1]); long long cnt=0,found=0;
  #pragma omp parallel for schedule(dynamic,1) reduction(+:cnt,found)
  for(int a1=q-4;a1>=1;a1--){
    for(int a2=a1;a2>=1;a2--){ int r2=q-a1-a2; if(r2<3) continue; if(a2*4<q-a1) break;
     for(int a3=(a2<r2-2?a2:r2-2);a3>=1;a3--){ int r3=r2-a3; if(r3<2) continue; if(a3*3<r2) break;
      for(int a4=(a3<r3-1?a3:r3-1);a4>=1;a4--){ int a5=r3-a4; if(a5>a4) break; if(a5<1) continue;
        cnt++;
        int a[5]={a1,a2,a3,a4,a5};
        /* well-formed */
        int ok=1;
        for(int i=0;i<5&&ok;i++){int G=0;for(int j=0;j<5;j++) if(j!=i) G=g(G,a[j]); if(G!=1) ok=0;}
        if(!ok) continue;
        for(int k=2;k<=q-2;k++){
          int s=0; for(int i=0;i<5;i++) s+=(int)(((long)k*a[i])/q);
          if(k-s==4){ok=0;break;}
        }
        if(ok){found++;
          #pragma omp critical
          printf("FOUND %d %d %d %d %d\n",a1,a2,a3,a4,a5);}
      }}}}
  printf("q=%d tuples=%lld found=%lld\n",q,cnt,found);
}

require import Int Array.

pragma Goals:printall.

lemma l1: forall n, 0 <= n => 1+1+n+1*1+1+1+n*1+1+1+1+1+1+n+1*1+1+1+1+1+1+1+n*1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1<=n*n*6*1+3*1+2*1+2*30.
    proof.
    move=> n n0.
simplify. admit.
qed.

lemma l2: forall x, true=>forall k,k<1/\0<k => x.[k-1]<=x.[k]/\0<=1.
    proof.
smt.
qed.

lemma l3: forall k i x n,i<k/\0<k =>
    x.[k-1]<=x.[k]/\n<i/\i=k=>forall k,i-1<k/\k<i=>x.[i]<x.[k]/\forall k1,forall k2,0<=k1/\k1<=k2/\k2<=i/\!k1=i-1/\!k2=i-1=>x.[k1]<=x.[k2]/\0<=i-i-1.
proof.
smt.
qed.

lemma l4: forall k i n x,i<k/\0<k=>x.[k-1]<=x.[k]/\!i<n=>0<=k/\k<n=>x.[k-1]<=x.[k].
proof.
    move=> k i n x a b k0.
smt.
qed.

lemma l5: forall k i x n,
    k<i/\0<k=>x.[k-1]<=x.[k]/\i<n=>i<=n.
proof.
smt.
qed.

lemma l6: forall k j i x key, j<k/\k<i => key<x.[k] /\ forall k1
    k2,0<=k1 /\
    k1<=k2/\k2<=i/\!k1=j/\!k2=j=>x.[k1]<=x.[k2]/\key<x.[j]/\0<=j/\i-j=k=>
    forall k, j-1<k /\ k<i => key<x.[k] /\forall k1,forall
    k2,0<=k1/\k1<=k2/\k2<=i/\!k1=j-1/\!k2=j-1=>x.[k1]<=x.[k2]/\k<i-j-1.
    proof.  move=> k j i x key s1.  left.  smt.  qed.

lemma l: forall k,j<k/\k<i=>x[k]>key/\forall k1,forall k2,0<=k1/\k1<=k2/\k2<=i/\!k1=j/\!k2=j=>x[k1]<=x[k2]/\!x[j]>key/\j>=0=>forall k,k<i+1/\k>0=>x[k]>=x[k-1].
proof.
smt.
qed.

lemma l: forall k,j<k/\k<i=>x[k]>key/\forall k1,forall k2,0<=k1/\k1<=k2/\k2<=i/\!k1=j/\!k2=j=>x[k1]<=x[k2]/\x[j]>key/\j>=0=>i-j<=n.
proof.
smt.
qed.


require import AllCore.

pragma Goals:printall.

lemma l: 1+1+n+1*1+1+1+1+1+n*1+1+1+1+1+1+n+1*1+1+1+n*1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1<=20*n*n+30*n+10.
proof.
smt.
qed.

lemma l: true=>forall k,k<0/\k>0=>x[k]>=x[k-1]/\0>=0.
proof.
smt.
qed.

lemma l: forall k,forall k,k<i/\k>0=>x[k]>=x[k-1]/\i<n-1/\i=k=>forall k,k<i+1=>i<=x[k]/\i+1>=0.
proof.
smt.
qed.

lemma l: forall k,k<i/\k>0=>x[k]>=x[k-1]/\!i<n-1=>forall k,k>=0/\k<n=>x[k]>=x[k-1].
proof.
smt.
qed.

lemma l: forall k,k<i/\k>0=>x[k]>=x[k-1]/\i<n-1=>i<=n.
proof.
smt.
qed.

lemma l: forall k,forall k,k<j=>min<=x[k]/\j<n/\j=k=>x[j]<x[min]=>forall k,k<j+1=>j<=x[k]/\j+1>k/\!x[j]<x[min]=>forall k,k<j+1=>min<=x[k]/\j+1>k.
proof.
smt.
qed.

lemma l: forall k,k<j=>min<=x[k]/\!j<n=>forall k,k<i+1/\k>0=>x[k]>=x[k-1]/\i+1<=k.
proof.
smt.
qed.

lemma l: forall k,k<j=>min<=x[k]/\j<n=>j<=n.
proof.
smt.
qed.


require import AllCore.

pragma Goals:printall.

lemma l: 1+1<=1.
proof.
smt.
qed.

lemma l: forall i1,forall i2,0<=i1/\i1<=i2/\i2<n=>a[i1]<=a[i2]=>0<=m/\result<n/\a[m]=v.
proof.
smt.
qed.


require import AllCore.

pragma Goals:printall.

lemma l: 1+1+1+1+1+1<=1.
proof.
smt.
qed.

lemma l: forall i1,forall i2,0<=i1/\i1<=i2/\i2<n=>a[i1]<=a[i2]=>0<=m/\result<n/\a[m]=v.
proof.
smt.
qed.


require import AllCore.

pragma Goals:printall.

lemma l: 1+1+n+1*1+1+1+n*1+1+1+1+1+1+n+1*1+1+1+1+1+1+1+n*1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1<=n*n*6*Assign+3*Sum+2*Arr+2*Sub.
proof.
smt.
qed.

lemma l: true=>forall k,k<1/\k>0=>x[k]>=x[k-1]/\1>=0.
proof.
smt.
qed.

lemma l: forall k,forall k,k<i/\k>0=>x[k]>=x[k-1]/\i<n/\i=k=>forall k,i-1<k/\k<i=>x[k]>x[i]/\forall k1,forall k2,0<=k1/\k1<=k2/\k2<=i/\!k1=i-1/\!k2=i-1=>x[k1]<=x[k2]/\i-i-1>=0.
proof.
smt.
qed.

lemma l: forall k,k<i/\k>0=>x[k]>=x[k-1]/\!i<n=>forall k,k>=0/\k<n=>x[k]>=x[k-1].
proof.
smt.
qed.

lemma l: forall k,k<i/\k>0=>x[k]>=x[k-1]/\i<n=>i<=n.
proof.
smt.
qed.

lemma l: forall k,forall k,j<k/\k<i=>x[k]>key/\forall k1,forall k2,0<=k1/\k1<=k2/\k2<=i/\!k1=j/\!k2=j=>x[k1]<=x[k2]/\x[j]>key/\j>=0/\i-j=k=>forall k,j-1<k/\k<i=>x[k]>key/\forall k1,forall k2,0<=k1/\k1<=k2/\k2<=i/\!k1=j-1/\!k2=j-1=>x[k1]<=x[k2]/\i-j-1>k.
proof.
smt.
qed.

lemma l: forall k,j<k/\k<i=>x[k]>key/\forall k1,forall k2,0<=k1/\k1<=k2/\k2<=i/\!k1=j/\!k2=j=>x[k1]<=x[k2]/\!x[j]>key/\j>=0=>forall k,k<i+1/\k>0=>x[k]>=x[k-1]/\i+1<=k.
proof.
smt.
qed.

lemma l: forall k,j<k/\k<i=>x[k]>key/\forall k1,forall k2,0<=k1/\k1<=k2/\k2<=i/\!k1=j/\!k2=j=>x[k1]<=x[k2]/\x[j]>key/\j>=0=>i-j<=n.
proof.
smt.
qed.
require import AllCore.

pragma Goals:printall.

lemma l: Assign+Cons+Assign+Sub+Var+Cons+logn+1*Le+Var+Var+<=20*logn+30.
proof.
smt.
qed.

lemma l: n>=0/\forall i1,forall i2,0<=i1/\i1<=i2/\i2<n=>a[i1]<=a[i2]=>0<=0/\n-1<n/\forall i,0<=i/\i<n=>a[i]=v=>0<=i/\i<=n-1/\n-1-0>=0.
proof.
smt.
qed.

lemma l: forall k,0<=l/\u<n/\forall i,0<=i/\i<n=>a[i]=v=>l<=i/\i<=u/\l<=u/\u-l=k=>a[m]>v=>0<=l+u-l/2+1/\u<n/\forall i,0<=i/\i<n=>a[i]=v=>l+u-l/2+1<=i/\i<=u/\u-l+u-l/2+1>k/\!a[m]>v=>a[m]>v=>0<=l/\l+u-l/2-1<n/\forall i,0<=i/\i<n=>a[i]=v=>l<=i/\i<=l+u-l/2-1/\l+u-l/2-1-l>k/\!a[m]>v=>0<=u+1/\u<n/\forall i,0<=i/\i<n=>a[i]=v=>u+1<=i/\i<=u/\u-u+1>k.
proof.
smt.
qed.

lemma l: forall k,40>=Assign+Sum+Var+Div+Sub+Var+Var+Cons+Assign+Sum+Var+Cons+Assign+Sub+Var+Cons+Assign+Var+Assign+Sum+Var+Cons+Gt+Arr+Var+Gt+Arr+Var.
proof.
smt.
qed.

lemma l: 0<=l/\u<n/\forall i,0<=i/\i<n=>a[i]=v=>l<=i/\i<=u/\!l<=u=>0<=m/\result<n/\a[m]=v.
proof.
smt.
qed.

lemma l: 0<=l/\u<n/\forall i,0<=i/\i<n=>a[i]=v=>l<=i/\i<=u/\l<=u=>u-l<=logn.
proof.
smt.
qed.


require import AllCore.

pragma Goals:printall.

lemma l: 1+1*Le+Var+Var+<=0.
proof.
smt.
qed.

lemma l: r=x/\q=0/\y>0/\x>=0=>true/\1>=0.
proof.
smt.
qed.

lemma l: forall k,true/\y<=r/\1=k=>true/\1>k.
proof.
smt.
qed.

lemma l: forall k,1>=Assign+Sub+Var+Var+Assign+Sum+Var+Cons.
proof.
smt.
qed.

lemma l: true/\!y<=r=>x=r+y*q/\r<y.
proof.
smt.
qed.

lemma l: true/\y<=r=>1<=1.
proof.
smt.
qed.


require import AllCore.

pragma Goals:printall.

lemma l: x+1*Le+Var+Var+<=0.
proof.
smt.
qed.

lemma l: r=x/\q=0/\y>0/\x>=0=>x=q*y+r/\y>=0/\r>=0/\x-r>=0.
proof.
smt.
qed.

lemma l: forall k,x=q*y+r/\y>=0/\r>=0/\y<=r/\x-r=k=>x=q+1*y+r-y/\y>=0/\r-y>=0/\x-r-y>k.
proof.
smt.
qed.

lemma l: forall k,10>=Assign+Sub+Var+Var+Assign+Sum+Var+Cons.
proof.
smt.
qed.

lemma l: x=q*y+r/\y>=0/\r>=0/\!y<=r=>x=r+y*q/\r<y.
proof.
smt.
qed.

lemma l: x=q*y+r/\y>=0/\r>=0/\y<=r=>x-r<=x.
proof.
smt.
qed.


require import AllCore.

pragma Goals:printall.

lemma l: Assign+Cons+n+1*Lt+Var+Var+<=n*n*6+3*Sum+2*Arr+2*Sub.
proof.
smt.
qed.

lemma l: true=>forall k,k<1/\k>0=>x[k]>=x[k-1]/\1>=0.
proof.
smt.
qed.

lemma l: forall k,forall k,k<i/\k>0=>x[k]>=x[k-1]/\i<n/\i=k=>forall k,i-1<k/\k<i=>x[k]>x[i]/\forall k1,forall k2,0<=k1/\k1<=k2/\k2<=i/\!k1=i-1/\!k2=i-1=>x[k1]<=x[k2]/\i-i-1>=0.
proof.
smt.
qed.

lemma l: forall k,9*k+15>=Assign+Arr+Assign+Sub+Var+Cons+n+1*And+Gt+Arr+Var+Ge+Var+Cons++Assign+Sum+Var+Cons+Var+Assign+Sum+Var+Cons.
proof.
smt.
qed.

lemma l: forall k,k<i/\k>0=>x[k]>=x[k-1]/\!i<n=>forall k,k>=0/\k<n=>x[k]>=x[k-1].
proof.
smt.
qed.

lemma l: forall k,k<i/\k>0=>x[k]>=x[k-1]/\i<n=>i<=n.
proof.
smt.
qed.

lemma l: forall k,forall k,j<k/\k<i=>x[k]>key/\forall k1,forall k2,0<=k1/\k1<=k2/\k2<=i/\!k1=j/\!k2=j=>x[k1]<=x[k2]/\x[j]>key/\j>=0/\i-j=k=>forall k,j-1<k/\k<i=>x[k]>key/\forall k1,forall k2,0<=k1/\k1<=k2/\k2<=i/\!k1=j-1/\!k2=j-1=>x[k1]<=x[k2]/\i-j-1>k.
proof.
smt.
qed.

lemma l: forall k,9>=Assign+Sum+Var+Cons+Arr+Assign+Sub+Var+Cons.
proof.
smt.
qed.

lemma l: forall k,j<k/\k<i=>x[k]>key/\forall k1,forall k2,0<=k1/\k1<=k2/\k2<=i/\!k1=j/\!k2=j=>x[k1]<=x[k2]/\!x[j]>key/\j>=0=>forall k,k<i+1/\k>0=>x[k]>=x[k-1]/\i+1<=k.
proof.
smt.
qed.

lemma l: forall k,j<k/\k<i=>x[k]>key/\forall k1,forall k2,0<=k1/\k1<=k2/\k2<=i/\!k1=j/\!k2=j=>x[k1]<=x[k2]/\x[j]>key/\j>=0=>i-j<=n.
proof.
smt.
qed.


require import AllCore.

pragma Goals:printall.

lemma l: Assign+Cons+Assign+Sub+Var+Cons+logn+1*Le+Var+Var+<=20*logn+30.
proof.
smt.
qed.

lemma l: n>=0/\forall i1,forall i2,0<=i1/\i1<=i2/\i2<n=>a[i1]<=a[i2]=>0<=0/\n-1<n/\forall i,0<=i/\i<n=>a[i]=v=>0<=i/\i<=n-1/\n-1-0>=0.
proof.
smt.
qed.

lemma l: forall k,0<=l/\u<n/\forall i,0<=i/\i<n=>a[i]=v=>l<=i/\i<=u/\l<=u/\u-l=k=>a[m]>v=>0<=l+u-l/2+1/\u<n/\forall i,0<=i/\i<n=>a[i]=v=>l+u-l/2+1<=i/\i<=u/\u-l+u-l/2+1>k/\!a[m]>v=>a[m]>v=>0<=l/\l+u-l/2-1<n/\forall i,0<=i/\i<n=>a[i]=v=>l<=i/\i<=l+u-l/2-1/\l+u-l/2-1-l>k/\!a[m]>v=>0<=u+1/\u<n/\forall i,0<=i/\i<n=>a[i]=v=>u+1<=i/\i<=u/\u-u+1>k.
proof.
smt.
qed.

lemma l: forall k,40>=Assign+Sum+Var+Div+Sub+Var+Var+Cons+Assign+Sum+Var+Cons+Assign+Sub+Var+Cons+Assign+Var+Assign+Sum+Var+Cons+Gt+Arr+Var+Gt+Arr+Var.
proof.
smt.
qed.

lemma l: 0<=l/\u<n/\forall i,0<=i/\i<n=>a[i]=v=>l<=i/\i<=u/\!l<=u=>0<=m/\result<n/\a[m]=v.
proof.
smt.
qed.

lemma l: 0<=l/\u<n/\forall i,0<=i/\i<n=>a[i]=v=>l<=i/\i<=u/\l<=u=>u-l<=logn.
proof.
smt.
qed.


require import AllCore.

pragma Goals:printall.

lemma l: x+1*Le+Var+Var+<=20*x+5.
proof.
smt.
qed.

lemma l: r=x/\q=0/\y>0/\x>=0=>x=q*y+r/\y>=0/\r>=0/\x-r>=0.
proof.
smt.
qed.

lemma l: forall k,x=q*y+r/\y>=0/\r>=0/\y<=r/\x-r=k=>x=q+1*y+r-y/\y>=0/\r-y>=0/\x-r-y>k.
proof.
smt.
qed.

lemma l: forall k,8>=Assign+Sub+Var+Var+Assign+Sum+Var+Cons.
proof.
smt.
qed.

lemma l: x=q*y+r/\y>=0/\r>=0/\!y<=r=>x=r+y*q/\r<y.
proof.
smt.
qed.

lemma l: x=q*y+r/\y>=0/\r>=0/\y<=r=>x-r<=x.
proof.
smt.
qed.


require import AllCore.

pragma Goals:printall.

lemma l: Assign+Sub+Var+Var+Assign+Sum+Var+Cons<=20*x+5.
proof.
smt.
qed.

lemma l: r=x/\q=0/\y>0/\x>=0=>x=r-y+y*q+1/\r-y<y.
proof.
smt.
qed.


require import AllCore.

pragma Goals:printall.

lemma l: x+1*Le+Var+Var+<=20*x+5.
proof.
smt.
qed.

lemma l: r=x/\q=0/\y>0/\x>=0=>x=q*y+r/\y>=0/\r>=0/\x-r>=0.
proof.
smt.
qed.

lemma l: forall k,x=q*y+r/\y>=0/\r>=0/\y<=r/\x-r=k=>x=q+1*y+r-y/\y>=0/\r-y>=0/\x-r-y>k.
proof.
smt.
qed.

lemma l: forall k,8>=Assign+Sub+Var+Var+Assign+Sum+Var+Cons.
proof.
smt.
qed.

lemma l: x=q*y+r/\y>=0/\r>=0/\!y<=r=>x=r+y*q/\r<y.
proof.
smt.
qed.

lemma l: x=q*y+r/\y>=0/\r>=0/\y<=r=>x-r<=x.
proof.
smt.
qed.


require import AllCore.

pragma Goals:printall.

lemma l: Assign+Cons+n+1*Lt+Var+Var+<=20*n*n+30*n+10.
proof.
smt.
qed.

lemma l: true=>forall k,k<1/\k>0=>x[k]>=x[k-1]/\1>=0.
proof.
smt.
qed.

lemma l: forall k,forall k,k<i/\k>0=>x[k]>=x[k-1]/\i<n/\i=k=>forall k,i-1<k/\k<i=>x[k]>x[i]/\forall k1,forall k2,0<=k1/\k1<=k2/\k2<=i/\!k1=i-1/\!k2=i-1=>x[k1]<=x[k2]/\i-i-1>=0.
proof.
smt.
qed.

lemma l: forall k,9*k+15>=Assign+Arr+Assign+Sub+Var+Cons+n+1*And+Gt+Arr+Var+Ge+Var+Cons++Assign+Sum+Var+Cons+Var+Assign+Sum+Var+Cons.
proof.
smt.
qed.

lemma l: forall k,k<i/\k>0=>x[k]>=x[k-1]/\!i<n=>forall k,k>=0/\k<n=>x[k]>=x[k-1].
proof.
smt.
qed.

lemma l: forall k,k<i/\k>0=>x[k]>=x[k-1]/\i<n=>i<=n.
proof.
smt.
qed.

lemma l: forall k,forall k,j<k/\k<i=>x[k]>key/\forall k1,forall k2,0<=k1/\k1<=k2/\k2<=i/\!k1=j/\!k2=j=>x[k1]<=x[k2]/\x[j]>key/\j>=0/\i-j=k=>forall k,j-1<k/\k<i=>x[k]>key/\forall k1,forall k2,0<=k1/\k1<=k2/\k2<=i/\!k1=j-1/\!k2=j-1=>x[k1]<=x[k2]/\i-j-1>k.
proof.
smt.
qed.

lemma l: forall k,9>=Assign+Sum+Var+Cons+Arr+Assign+Sub+Var+Cons.
proof.
smt.
qed.

lemma l: forall k,j<k/\k<i=>x[k]>key/\forall k1,forall k2,0<=k1/\k1<=k2/\k2<=i/\!k1=j/\!k2=j=>x[k1]<=x[k2]/\!x[j]>key/\j>=0=>forall k,k<i+1/\k>0=>x[k]>=x[k-1]/\i+1<=k.
proof.
smt.
qed.

lemma l: forall k,j<k/\k<i=>x[k]>key/\forall k1,forall k2,0<=k1/\k1<=k2/\k2<=i/\!k1=j/\!k2=j=>x[k1]<=x[k2]/\x[j]>key/\j>=0=>i-j<=n.
proof.
smt.
qed.


require import AllCore.

pragma Goals:printall.

lemma l: Assign+Cons+Assign+Sub+Var+Cons+logn+1*Le+Var+Var+<=43*logn+10.
proof.
smt.
qed.

lemma l: forall i,0<=i/\i<n=>a[i]<a[i+1]/\exists j,a[j]=v=>0<=0/\n-1<n/\forall i,0<=i/\i<n/\a[i]=v=>0<=i/\i<=n-1/\n-n-1+0>=0.
proof.
smt.
qed.

lemma l: forall k,0<=l/\u<n/\forall i,0<=i/\i<n/\a[i]=v=>l<=i/\i<=u/\l<=u/\n-u+l=k=>a[m]<v=>0<=l+u-l/2+1/\u<n/\forall i,0<=i/\i<n/\a[i]=v=>l+u-l/2+1<=i/\i<=u/\n-u+l+u-l/2+1>k/\!a[m]<v=>a[m]>v=>0<=l/\l+u-l/2-1<n/\forall i,0<=i/\i<n/\a[i]=v=>l<=i/\i<=l+u-l/2-1/\n-l+u-l/2-1+l>k/\!a[m]>v=>0<=u+1/\u<n/\forall i,0<=i/\i<n/\a[i]=v=>u+1<=i/\i<=u/\n-u+u+1>k.
proof.
smt.
qed.

lemma l: forall k,40>=Assign+Sum+Var+Div+Sub+Var+Var+Cons+Assign+Sum+Var+Cons+Assign+Sub+Var+Cons+Assign+Var+Assign+Sum+Var+Cons+Gt+Arr+Var+Lt+Arr+Var.
proof.
smt.
qed.

lemma l: 0<=l/\u<n/\forall i,0<=i/\i<n/\a[i]=v=>l<=i/\i<=u/\!l<=u=>0<=result/\result<n/\a[result]=v.
proof.
smt.
qed.

lemma l: 0<=l/\u<n/\forall i,0<=i/\i<n/\a[i]=v=>l<=i/\i<=u/\l<=u=>n-u+l<=logn.
proof.
smt.
qed.



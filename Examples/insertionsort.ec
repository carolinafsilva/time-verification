require import AllCore Array.
  pragma Goals:printall.

lemma l1 (n : int) : 0<= n => ((1 + 1) + (((n + 1) + (1 + (1 + 1))) + (n + (((((1 + 1) + (1 + (1 + (1 + 1)))) + (((n + 1) + (1 + ((1 + (1 + 1)) + (1 + (1 + 1))))) + (n + ((1 + ((1 + (1 + 1)) + 1)) + (1 + (1 + (1 + 1))))))) + (1 + ((1 + (1 + 1)) + 1))) + (1 + (1 + (1 + 1))))))) <= ((n + n) + ((((6 + 1) + (3 + 1)) + (2 + 1)) + (2 + 1))).
    proof.
      simplify.
    smt.
  qed
  
  lemma l2 (x : int array): true=>forall k,k<1/\0<k=>x.[k-1]<=x.[k]/\0<=1.
proof.
smt.
qed.


lemma l3 (i : int) (x : int array) (n:int): forall k', forall k,k<i/\0<k=>x.[k-1]<=x.[k]/\i<n/\i=k'=>forall k,i-1<k/\k<i=>x.[i]<x.[k]/\forall k1,forall k2,0<=k1/\k1<=k2/\k2<=i/\!k1=i-1/\!k2=i-1=>x.[k1]<=x.[k2]/\0<=i-i-1.
    proof.
smt.
  qed.

  
lemma l4 (i:int) (x : int array) (n :int): forall k,k<i/\0<=k=>x.[k-1]<=x.[k]/\!i<n=>forall k,0<=k/\k<n=>x.[k-1]<=x.[k].
    proof.
smt.
qed.

lemma l5 (i:int) (x: int array) (n : int): forall k,k<i/\0<k => x.[k-1]<=x.[k]/\i<n=>i<=n.
    proof.
smt.
  qed.
  
lemma l6 (i:int) (j:int) (x: int array) (n:int) (key:int) : forall k',forall k,j<k/\k<i=>key<x.[k]/\forall k1,forall k2,0<=k1/\k1<=k2/\k2<=i/\!k1=j/\!k2=j=>x.[k1]<=x.[k2]/\key<x.[j]/\0<=j/\i-j=k'=>forall k,j-1<k/\k<i=>key<x.[k]/\forall k1,forall k2,0<=k1/\k1<=k2/\k2<=i/\!k1=j-1/\!k2=j-1=>x.[k1]<=x.[k2]/\k'<i-j-1.
    proof.
smt.
  qed.
  
lemma l7 (i:int) (j:int) (x: int array) (n:int) (key:int): forall k,j<k/\k<i=>key<x.[k] /\ forall k1,forall k2,0<=k1/\k1<=k2/\k2<=i/\!k1=j/\!k2=j=>x.[k1]<=x.[k2]/\!key<x.[j]/\0<=j=>forall k,k<i+1/\0<k=>x.[k-1]<=x.[k].
    proof.
smt.
  qed.
  
lemma l8 (i:int) (j:int) (x: int array) (n:int) (key:int): forall k,j<k/\k<i=>key<x.[k]/\forall k1,forall k2,0<=k1/\k1<=k2/\k2<=i/\!k1=j/\!k2=j=>x.[k1]<=x.[k2]/\key<x.[j]/\0<=j=>i-j<=n.
    proof.
smt.
qed.


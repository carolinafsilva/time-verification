{ true }
i = 1;
while i < n do
(*
  inv: forall k. (0 < k and k < i) => (x[k] >= x[k-1])
  var: i
  N: n
*)
  key = x[i];
  j = i - 1;
  while x[j] > key and j >= 0 do
  (*
    inv: (forall k. (j < k and k < i) => x[k] > key) and (forall k1. forall k2.  0 <= k1 and k1 <= k2 and k2 <= i and not (k1 == j) and not (k2 == j) => x[k1] <= x[k2])
    var: i - j
    N: n
  *)
    x[j + 1] = x[j];
    j = j - 1
  end;
  x[j + 1] = key;
  i = i + 1
end
{ forall k. (k>=0 and k<n) => x[k] >= x[k-1] | 20*n*n + 30*n + 10 }

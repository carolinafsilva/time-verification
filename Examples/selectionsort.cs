{true}
i = 0;
while i < n-1 do
(*
    inv: forall k . (k < i and k > 0) => (x[k] >= x[k-1])
    var: i
    N: n
  *)
  min = i;
  j = i + 1;
  while j < n do
    (*
    inv: forall k. (k < j) => (min <= x[k])
    var: j
    N: n
  *)
    if x[j] < x[min] then
      min = j
    else
      skip
    end;
    j = j + 1
  end;
  (* Swap x[i] and x[min] *)
  tmp = x[i];
  x[i] = x[min];
  x[min] = tmp;
  i = i + 1
end
{ forall k. (k>=0 and k<n) => x[k] >= x[k-1] | 20 * n * n + 30 * n + 10}

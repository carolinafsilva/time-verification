{ 0 <= l and l < u and n >= 0}
j = 0;
for i=0 to n do
  if (l <= a[i] and a[i] <= u)
  then
    b[j] = a[i];
    j = j + 1
  else
    b[j] = b[j];
    j = j + 0
  end
end
{ forall i. (0<=i and i<n) => (l <= a[i] and a[i] <= u => exists j. B[j] == a[i] )
and (l > a[i] and a[i] > u => not (exists j. b[j] == a[i]) ) | 17*n + 22 }

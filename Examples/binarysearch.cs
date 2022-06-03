{(forall i. (0 <= i and i < n) => a[i] < a[i+1]) and (exists j. a[j] == v)}
l = 0;
u = n - 1;
while l <= u do
  m = l + ((u - l) / 2);
  if a[m] < v then
    l = m + 1
  else
    if a[m] > v then
      u = m - 1
    else
     result = m;
     l = u + 1
    end
  end
end
{0 <= result and result < n and a[result] == v | 43 * logn + 10}

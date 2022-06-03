{n == 32}
B[6];
size = 6;

(*Initialize the array*)
i = 0;
while i < size do
  B[i] = 0;
  i = i + 1
end;

(*Binary Counter*)
i = 0;
while i < n do
  j = 0;
  while B[j] == 1 do
    B[j] = 0;
    j = j + 1
  end;
  B[j] = 1;
  i = i + 1
end
{true | 20*n + 30}

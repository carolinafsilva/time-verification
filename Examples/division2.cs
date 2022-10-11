{ r == x and q == 0 and y > 0 and x >= 0}
x = 20;
y = 5;
r = x;
q = 0;
while y <= r do
(*
  inv: x == q * y + r and y>=0 and r>=0
  var: x - r
  n: x
*)
  r = r - y;
  q = q + 1
end
{ x == r + y * q and r < y | 20 * x + 5 }

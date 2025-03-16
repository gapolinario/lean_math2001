import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

--i asked chatGPT for 10 questions based on 1.4 (inequalities)

--this was false as formulated originally
example {x y : ℤ} (h1 : x + 5 ≤ 3 * y) (h2 : y ≤ 2) : x ≤ 6 := by
  calc
    x
    _ = (x+5) -5 := by ring
    _ ≤ 3*y-5 := by rel[h1]
    _ ≤ 3*2-5 := by rel[h2]
    _ ≤ 6 := by numbers

--problem 2 is false as well
--a=10,b=-5,then 2a+b=15
--example {a b : ℚ} (h1 : a ≥ 2) (h2 : a + b ≤ 7) : 2 * a + b ≤ 10 := by

-- original statement had (hx : x ≥ 4)
-- this was also false, this polynomial has a root at ≈4.3
-- so it's negative at x=4
example {x : ℤ} (hx : x ≥ 5) : x ^ 3 - 5 * x ^ 2 + 3 * x ≥ 0 := by
  have h2: x-5 ≥ 0 :=
    calc
      x-5
      _ ≥ 5-5 := by rel[hx]
      _ = 0 := by numbers
  calc
    x^3-5*x^2+3*x
    _ = x^2*(x-5) + 3*x := by ring
    _ ≥ x^2*(x-5) := by extra
    _ ≥ x^2*0 := by rel[h2]
    _ = 0 := by ring

-- this is correct
example {n : ℤ} (hn : n ≥ 6) : n ^ 4 - 3 * n ^ 2 > 4 * n ^ 3 := by
  calc
    n^4-3*n^2
    --_ = (n^4-3*n^2-4*n^3)+4*n^3 := by ring
    --_ = n^2*(n^2-4*n-3)+4*n^3 := by ring
    _ = n^2*(n*(n-6+2)-3)+4*n^3 := by ring
    _ ≥ n^2*(n*(6-6+2)-3)+4*n^3 := by rel[hn]
    _ = n^2*(2*n-3)+4*n^3 := by ring
    _ ≥ n^2*(2*6-3)+4*n^3 := by rel[hn]
    _ = 9*n^2 + 4*n^3 := by ring
    _ > 4*n^3 := by extra

--this is correct
example {n : ℤ} (h1 : n ≥ 8) : n ^ 2 - 3 * n + 4 > 20 := by
  calc
    n^2-3*n+4
    _ = n*(n-3)+4 := by ring
    _ ≥ 8*(8-3)+4 := by rel[h1]
    --_ = 44 := by numbers
    _ > 20 := by numbers


-- original formulation was false, with
-- ≥ -2
-- (3/2)^2 - 3 (3/2) = -9/4 <= -2
example {x : ℚ} : x ^ 2 - 3 * x ≥ -3 := by
  calc
    x^2-3*x
    _ = (x^2-3*x+9/4)-(9/4) := by ring
    _ = (x-3/2)^2-(9/4) := by ring
    _ ≥ -(9/4) := by extra
    _ ≥ -3 := by numbers

-- this is correct, but not interesting
example {a b : ℝ} : a ^ 2 + b ^ 2 ≥ 2 * a * b - 1 := by
  calc
    a ^ 2 + b ^ 2
    _ = a ^ 2 + b ^ 2 -2*a*b+2*a*b := by ring
    _ = (a-b)^2+2*a*b+1-1 := by ring
    _ ≥ 2*a*b+1-1 := by extra
    _ ≥ 2*a*b-1 := by extra

--this is correct and interesting
example {x y : ℝ} (h : x ^ 2 + y ^ 2 ≤ 2) : (x + y) ^ 2 < 5 := by
  calc
    (x+y)^2
    _ ≤ (x+y)^2 + (x-y)^2 := by extra
    _ = 2 * (x^2+y^2) := by ring
    _ ≤ 2*2 := by rel[h]
    _ < 5 := by numbers

-- this is correct and interesting,
-- but the solution provided is wrong,
-- and I haven't found a solution yet
example {a b : ℚ} (h1 : a ≥ 1) (h2 : b ≥ 2) (h3 : a + b ≤ 10) :
    4 * a * b + 2 * a ≤ 12 * b + 80 := by
    sorry

--correct, but immediate
example {m n : ℤ} (h : m ^ 2 + n ≤ 3) : n ≤ 3 := by
  calc
    n
    _ ≤ m^2+n := by extra
    _ ≤ 3 := by rel[h]

/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

example {x : ℚ} (hx : 3 * x = 2) : x ≠ 1 := by
  apply ne_of_lt
  calc
    x = 3 * x / 3 := by ring
    _ = 2 / 3 := by rw [hx]
    _ < 1 := by numbers

example {y : ℝ} : y ^ 2 + 1 ≠ 0 := by
  apply ne_of_gt
  --calc
  --  y^2+1 > 0 := by extra
  extra

example {a b : ℝ} (h1 : a ^ 2 + b ^ 2 = 0) : a ^ 2 = 0 := by
  apply le_antisymm
  calc
    a ^ 2 ≤ a ^ 2 + b ^ 2 := by extra
    _ = 0 := h1
  extra


/-! # Exercises -/


example {m : ℤ} (hm : m + 1 = 5) : 3 * m ≠ 6 := by
  have h: 3 * m > 6 :=
  calc
    3 * m
    _ = 3 * ((m+1)-1) := by ring
    _ = 12 := by rw[hm]; ring
    _ > 6 := by numbers
  apply ne_of_gt h

example {s : ℚ} (h1 : 3 * s ≤ -6) (h2 : 2 * s ≥ -4) : s = -2 := by
  have h3: s≤-2 :=
  calc
    s = (3*s)/3 := by ring
    _ ≤ -6/3 := by rel[h1]
    _ = -2 := by ring
  have h4: s≥-2 :=
  calc
    s = (2*s)/2 := by ring
    _ ≥ -4/2 := by rel[h2]
    _ = -2 := by ring
  apply le_antisymm h3 h4


/-! # Anki -/


example {x: ℝ} (h1: x≤2) (h2: x≥2) : x=2 := by
  apply le_antisymm h1 h2

example {x: ℝ} (h1: x>2) : x≠2 := by
  apply ne_of_gt h1

example {x: ℝ} (h1: x<2) : x≠2 := by
  apply ne_of_lt h1

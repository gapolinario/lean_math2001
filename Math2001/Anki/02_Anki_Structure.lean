import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

example {x: ℝ} (h1: x≤2) (h2: x≥2) : x=2 := by
  apply le_antisymm h1 h2

example {x: ℝ} (h1: x>2) : x≠2 := by
  apply ne_of_gt h1

example {x: ℝ} (h1: x<2) : x≠2 := by
  apply ne_of_lt h1

example {x : ℚ} (hx : 3 * x = 2) : x ≠ 1 := by
--How do we change the goal?
  apply ne_of_lt
  sorry

example {x y: ℝ} (h1: x-2=1) (h2: x+y=3) : y=0 := by
--Introduce an additional hypothesis
  have h3: x=3 := by addarith[h1]
  calc
    y
    _ = (x+y)-x := by ring
    _ = 3-3 := by rw[h2,h3]
    _ = 0 := by numbers


example {x y : ℝ} (h : x = 1 ∨ y = -1) : x * y + x = y + 1 := by
-- What do we do about `or` in the hypothesis?
  obtain hx | hy := h
  sorry
  sorry

example {x y : ℤ} (h : 2 * x - y = 4 ∧ y - x + 1 = 2) : x = 5 := by
-- What do we do about `and` in the hypothesis?
  obtain ⟨h1, h2⟩ := h
  sorry

example {a b : ℝ} (h1 : a - 5 * b = 4) (h2 : b + 2 = 3) : a = 9 ∧ b = 1 := by
-- What do we do about `and` in the hypothesis?
  constructor
  sorry
  sorry

example : ∃ n : ℤ, 5 * n = 35 := by
  use 7
  numbers

example {a : ℚ} (h : ∃ b : ℚ, a = b ^ 2 + 1) : a > 0 := by
  obtain ⟨b, hb⟩ := h
  calc
    a = b ^ 2 + 1 := hb
    _ > 0 := by extra

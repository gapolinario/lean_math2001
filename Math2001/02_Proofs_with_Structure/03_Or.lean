/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init


example {x y : ℝ} (h : x = 1 ∨ y = -1) : x * y + x = y + 1 := by
  obtain hx | hy := h
  calc
    x * y + x = 1 * y + 1 := by rw [hx]
    _ = y + 1 := by ring
  calc
    x * y + x = x * -1 + x := by rw [hy]
    _ = -1 + 1 := by ring
    _ = y + 1 := by rw [hy]

example {n : ℕ} : n ^ 2 ≠ 2 := by
  have hn := le_or_succ_le n 1
  obtain hn | hn := hn
  apply ne_of_lt
  calc
    n ^ 2 ≤ 1 ^ 2 := by rel [hn]
    _ < 2 := by numbers
  apply ne_of_gt
  calc
    n^2 ≥ 2^2 := by rel[hn]
    _ > 2 := by numbers

example {x : ℝ} (hx : 2 * x + 1 = 5) : x = 1 ∨ x = 2 := by
  right
  calc
    x = (2 * x + 1 - 1) / 2 := by ring
    _ = (5 - 1) / 2 := by rw [hx]
    _ = 2 := by numbers


example {x : ℝ} (hx : x ^ 2 - 3 * x + 2 = 0) : x = 1 ∨ x = 2 := by
  have h1 :=
    calc
    (x - 1) * (x - 2) = x ^ 2 - 3 * x + 2 := by ring
    _ = 0 := by rw [hx]
  have h2 := eq_zero_or_eq_zero_of_mul_eq_zero h1
  obtain h|h := h2
  left
  addarith[h]
  right
  addarith[h]

example {n : ℤ} : n ^ 2 ≠ 2 := by
  have hn0 := le_or_succ_le n 0
  obtain hn0 | hn0 := hn0
  · have : 0 ≤ -n := by addarith [hn0]
    have hn := le_or_succ_le (-n) 1
    obtain hn | hn := hn
    · apply ne_of_lt
      calc
        n ^ 2 = (-n) ^ 2 := by ring
        _ ≤ 1 ^ 2 := by rel [hn]
        _ < 2 := by numbers
    · apply ne_of_gt
      calc
        (2:ℤ) < 2 ^ 2 := by numbers
        _ ≤ (-n) ^ 2 := by rel [hn]
        _ = n ^ 2 := by ring
  · have hn := le_or_succ_le n 1
    obtain hn | hn := hn
    · apply ne_of_lt
      calc
        n ^ 2 ≤ 1 ^ 2 := by rel [hn]
        _ < 2 := by numbers
    · apply ne_of_gt
      calc
        (2:ℤ) < 2 ^ 2 := by numbers
        _ ≤ n ^ 2 := by rel [hn]


/-! # Exercises -/


example {x : ℚ} (h : x = 4 ∨ x = -4) : x ^ 2 + 1 = 17 := by
  obtain h4|h4 := h
  calc
    x^2+1 = 4^2+1 := by rw[h4]
    _ = 17 := by numbers
  calc
    x^2+1 = (-4)^2+1 := by rw[h4]
    _ = 17 := by numbers

example {x : ℝ} (h : x = 1 ∨ x = 2) : x ^ 2 - 3 * x + 2 = 0 := by
  obtain h1|h2 := h
  calc
    x^2-3*x+2 = 1^2-3*1+2 := by rw[h1]
    _ = 0 := by ring
  calc
    x^2-3*x+2 = 2^2-3*2+2 := by rw[h2]
    _ = 0 := by ring

example {t : ℚ} (h : t = -2 ∨ t = 3) : t ^ 2 - t - 6 = 0 := by
  obtain ht|ht := h
  calc
    t^2-t-6 = (-2)^2-(-2)-6 := by rw[ht]
    _ = 0 := by ring
  calc
    t^2-t-6 = (3)^2-(3)-6 := by rw[ht]
    _ = 0 := by ring

example {x y : ℝ} (h : x = 2 ∨ y = -2) : x * y + 2 * x = 2 * y + 4 := by
  obtain hx|hy := h
  calc
    x*y+2*x = 2*y+2*2 := by rw[hx]
    _ = 2*y+4 := by ring
  calc
    x*y+2*x = x*(-2)+2*x := by rw[hy]
    _ = 2*(-2) + 4 := by ring
    _ = 2*y+4 := by rw[hy]

example {s t : ℚ} (h : s = 3 - t) : s + t = 3 ∨ s + t = 5 := by
  left
  addarith[h]

example {a b : ℚ} (h : a + 2 * b < 0) : b < a / 2 ∨ b < - a / 2 := by
  right
  addarith[h]

example {x y : ℝ} (h : y = 2 * x + 1) : x < y / 2 ∨ x > y / 2 := by
  left
  addarith[h]

example {x : ℝ} (hx : x ^ 2 + 2 * x - 3 = 0) : x = -3 ∨ x = 1 := by
  have h1 :=
  calc
    (x+3)*(x-1) = x^2+2*x-3 := by ring
    _ = 0 := by rw[hx]
  have h2 := eq_zero_or_eq_zero_of_mul_eq_zero h1
  obtain h|h := h2
  left
  addarith[h]
  right
  addarith[h]

example {a b : ℝ} (hab : a ^ 2 + 2 * b ^ 2 = 3 * a * b) : a = b ∨ a = 2 * b := by
  have h :=
  calc
    (a-b)*(a-2*b)
    _ = a ^ 2 + 2 * b ^ 2 - 3 * a * b := by ring
    _ = 3*a*b-3*a*b := by rw[hab]
    _ = 0 := by ring
  have h2 := eq_zero_or_eq_zero_of_mul_eq_zero h
  obtain h3|h3 := h2
  left
  addarith[h3]
  right
  addarith[h3]


example {t : ℝ} (ht : t ^ 3 = t ^ 2) : t = 1 ∨ t = 0 := by
  have h:=
  calc
    (t-1)*(t*t) = t^3-t^2 := by ring
    _ = t^2-t^2 := by rw[ht]
    _ = 0 := by ring
  have h2 := eq_zero_or_eq_zero_of_mul_eq_zero h
  obtain h3|h3 := h2
  left
  addarith[h3]
  right
  have h4:= eq_zero_or_eq_zero_of_mul_eq_zero h3
  obtain h5|h5 := h4
  exact h5
  exact h5


example {n : ℕ} : n ^ 2 ≠ 7 := by
  have h2 := le_or_succ_le n 2
  obtain h|h := h2
  have h3 :=
  calc
    n^2
    _ ≤ 2^2 := by rel[h]
    _ = 4 := by ring
    _ < 7 := by numbers
  apply ne_of_lt h3
  have h3 :=
  calc
    n^2
    _ ≥ 3^2 := by rel[h]
    _ = 9 := by ring
    _ > 7 := by numbers
  apply ne_of_gt h3


example {x : ℤ} : 2 * x ≠ 3 := by
  have h1 := le_or_succ_le x 1
  obtain h2|h2 := h1
  have h3 :=
  calc
    2 * x ≤ 2*1 := by rel[h2]
    _ = 2 := by numbers
    _ < 3 := by numbers
  apply ne_of_lt h3
  have h3 :=
  calc
    2 * x ≥ 2*2 := by rel[h2]
    _ = 4 := by numbers
    _ > 3 := by numbers
  apply ne_of_gt h3


example {t : ℤ} : 5 * t ≠ 18 := by
  have h1 := le_or_succ_le t 3
  obtain h2|h2 := h1
  have h3 :=
  calc
    5*t ≤ 5*3 := by rel[h2]
    _ = 15 := by numbers
    _ < 18 := by numbers
  apply ne_of_lt h3
  have h3 :=
  calc
    5*t ≥ 5*4 := by rel[h2]
    _ = 20 := by numbers
    _ > 18 := by numbers
  apply ne_of_gt h3

example {m : ℕ} : m ^ 2 + 4 * m ≠ 46 := by
  have h1 := le_or_succ_le m 5
  obtain h2|h2 := h1
  have h3 :=
  calc
    m^2+4*m ≤ 5^2+4*5 := by rel[h2]
    _ = 45 := by numbers
    _ < 46 := by numbers
  apply ne_of_lt h3
  have h3 :=
  calc
    m^2+4*m ≥ 6^2+4*6 := by rel[h2]
    _ = 60 := by numbers
    _ > 46 := by numbers
  apply ne_of_gt h3

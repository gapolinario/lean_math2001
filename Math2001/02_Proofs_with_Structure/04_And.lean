/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init


example {x y : ℤ} (h : 2 * x - y = 4 ∧ y - x + 1 = 2) : x = 5 := by
  obtain ⟨h1, h2⟩ := h
  calc
    x = 2 * x - y + (y - x + 1) - 1 := by ring
    _ = 4 + 2 - 1 := by rw [h1, h2]
    _ = 5 := by ring


example {p : ℚ} (hp : p ^ 2 ≤ 8) : p ≥ -5 := by
  have hp' : -3 ≤ p ∧ p ≤ 3
  · apply abs_le_of_sq_le_sq'
    calc
      p ^ 2 ≤ 9 := by addarith [hp]
      _ = 3 ^ 2 := by numbers
    numbers
  obtain ⟨h1,h2⟩ := hp'
  addarith[h1]

example {a b : ℝ} (h1 : a - 5 * b = 4) (h2 : b + 2 = 3) : a = 9 ∧ b = 1 := by
  constructor
  · calc
      a = 4 + 5 * b := by addarith [h1]
      _ = -6 + 5 * (b + 2) := by ring
      _ = -6 + 5 * 3 := by rw [h2]
      _ = 9 := by ring
  · addarith [h2]


example {a b : ℝ} (h1 : a - 5 * b = 4) (h2 : b + 2 = 3) : a = 9 ∧ b = 1 := by
  have hb : b = 1 := by addarith [h2]
  constructor
  · calc
      a = 4 + 5 * b := by addarith [h1]
      _ = 4 + 5 * 1 := by rw [hb]
      _ = 9 := by ring
  · apply hb


example {a b : ℝ} (h1 : a ^ 2 + b ^ 2 = 0) : a = 0 ∧ b = 0 := by
  have h2 : a ^ 2 = 0
  · apply le_antisymm
    calc
      a ^ 2 ≤ a ^ 2 + b ^ 2 := by extra
      _ = 0 := by rw [h1]
    extra
  have h3 : b^2 = 0
  calc
    b^2
    _ = (a^2+b^2) - a^2 := by ring
    _ = 0 - 0 := by rw[h1,h2]
    _ = 0 := by ring
  constructor
  . have h4: a*a = 0 :=
      calc
        a*a = a^2 := by ring
        _ = 0 := by rw[h2]
    have h5: a=0 ∨ a=0 :=
      eq_zero_or_eq_zero_of_mul_eq_zero h4
    obtain h6|h6 := h5
    exact h6
  . have h4: b*b = 0 :=
      calc
        b*b = b^2 := by ring
        _ = 0 := by rw[h3]
    have h5: b=0 ∨ b=0 :=
      eq_zero_or_eq_zero_of_mul_eq_zero h4
    obtain h6|h6 := h5
    exact h6



/-! # Exercises -/


example {a b : ℚ} (H : a ≤ 1 ∧ a + b ≤ 3) : 2 * a + b ≤ 4 := by
  obtain ⟨h1,h2⟩ := H
  calc
    2 * a + b
    _ = a + (a+b) := by ring
    _ ≤ 1+3 := by rel[h2,h1]
    _ = 4 := by numbers

example {r s : ℝ} (H : r + s ≤ 1 ∧ r - s ≤ 5) : 2 * r ≤ 6 := by
  obtain ⟨h1,h2⟩ := H
  calc
    2 * r = (r+s) + (r-s) := by ring
    _ ≤ 1+5 := by rel[h1,h2]
    _ = 6 := by numbers

example {m n : ℤ} (H : n ≤ 8 ∧ m + 5 ≤ n) : m ≤ 3 := by
  obtain ⟨h1,h2⟩ := H
  calc
    m = (m+5)-5 := by ring
    _ ≤ n-5 := by rel[h2]
    _ ≤ 8-5 := by rel[h1]

example {p : ℤ} (hp : p + 2 ≥ 9) : p ^ 2 ≥ 49 ∧ 7 ≤ p := by
  have h1 : 7 ≤ p := by addarith[hp]
  constructor
  calc
    p^2 = p*p := by ring
    _ ≥ 7*7 := by rel[h1]
  exact h1

example {a : ℚ} (h : a - 1 ≥ 5) : a ≥ 6 ∧ 3 * a ≥ 10 := by
  have h2: a ≥ 6 := by addarith[h]
  constructor
  exact h2
  calc
    3*a ≥ 3*6 := by rel[h2]
    _ = 18 := by ring

example {x y : ℚ} (h : x + y = 5 ∧ x + 2 * y = 7) : x = 3 ∧ y = 2 := by
  obtain ⟨h1,h2⟩ := h
  have h3: x=3 :=
  calc
    x = 2*(x+y)-(x+2*y) := by ring
    _ = 2*5-7 := by rw[h1,h2]
    _ = 3 := by ring
  constructor
  . exact h3
  . calc
      y
      _ = (x+y) - x := by ring
      _ = 5-3 := by rw[h1,h3]
      _ = 2 := by ring

example {a: ℝ} : a>0 ∨ a=0 ∨ a<0 := by
  exact trichotomous a 0

example {a: ℝ} : a>0 ∨ a≤0 := by
  exact lt_or_ge 0 a


example {a b : ℝ} (h1 : a * b = a) (h2 : a * b = b) :
    a = 0 ∧ b = 0 ∨ a = 1 ∧ b = 1 := by
    have hab: a=b :=
      calc
        a
        _ = a*b := by rw[h1]
        _ = b := by rw[h2]
    have h3: a=0 ∨ a≠0 := by exact eq_or_ne a 0
    obtain h3|h3 := h3
    left
    constructor
    exact h3
    calc
      b
      _ = a := by rw[hab]
      _ = 0 := by rw[h3]
    right
    have ha: a=1 :=
    calc
      a
      _ = (a*a)/a := by field_simp
      _ = (a*b)/a := by rw[hab]
      _ = a/a := by rw[h1]
      _ = 1 := by field_simp
    constructor
    exact ha
    calc
      b
      _ = a := by rw[hab]
      _ = 1 := by exact ha


example {a: ℝ} (h1: a≠0) (h2: a*a=a): a=1 := by
  calc
    a
    _ = (a*a)/a := by field_simp
    _ = a/a := by rw[h2]
    _ = 1 := by field_simp

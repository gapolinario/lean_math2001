/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init


example {a : ℚ} (h : ∃ b : ℚ, a = b ^ 2 + 1) : a > 0 := by
  obtain ⟨b, hb⟩ := h
  calc
    a = b ^ 2 + 1 := hb
    _ > 0 := by extra


example {t : ℝ} (h : ∃ a : ℝ, a * t < 0) : t ≠ 0 := by
  obtain ⟨x, hxt⟩ := h
  have H := le_or_gt x 0
  obtain hx | hx := H
  · have hxt' : 0 < (-x) * t := by addarith [hxt]
    have hx' : 0 ≤ -x := by addarith [hx]
    cancel -x at hxt'
    apply ne_of_gt
    apply hxt'
  · have hxt': 0 < x * (-t) :=
    calc
      0 < -x * t := by addarith[hxt]
      _ = x * (-t) := by ring
    cancel x at hxt'
    apply ne_of_lt
    calc
      t < 0 := by addarith[hxt']



example : ∃ n : ℤ, 12 * n = 84 := by
  use 7
  numbers


example (x : ℝ) : ∃ y : ℝ, y > x := by
  use x + 1
  extra


example : ∃ m n : ℤ, m ^ 2 - n ^ 2 = 11 := by
  use 6,5
  numbers

example (a : ℤ) : ∃ m n : ℤ, m ^ 2 - n ^ 2 = 2 * a + 1 := by
  use a+1,a
  ring

example {p q : ℝ} (h : p < q) : ∃ x, p < x ∧ x < q := by
  use p + (q-p)/2
  have h2: 0 < q-p := by addarith[h]
  constructor
  calc
    p
    _ < p + (q-p)/2 := by extra
  calc
    p+(q-p)/2
    _ < p+(q-p)/2+(q-p)/2 := by extra
    _ = q := by ring


-- the way it's done in the book
example {p q : ℝ} (h : p < q) : ∃ x, p < x ∧ x < q := by
  use (p+q)/2
  constructor
  calc
    p
    _ = (p+p)/2 := by ring
    _ < (p+q)/2 := by rel[h]
  calc
    (p+q)/2
    _ < (q+q)/2 := by rel[h]
    _ = q := by ring




example : ∃ a b c d : ℕ,
    a ^ 3 + b ^ 3 = 1729 ∧ c ^ 3 + d ^ 3 = 1729 ∧ a ≠ c ∧ a ≠ d := by
  use 1, 12, 9, 10
  constructor
  numbers
  constructor
  numbers
  constructor
  numbers
  numbers

/-! # Exercises -/


example : ∃ t : ℚ, t ^ 2 = 1.69 := by
  use 1.3
  numbers

example : ∃ m n : ℤ, m ^ 2 + n ^ 2 = 85 := by
  use 6,7
  numbers

example : ∃ x : ℝ, x < 0 ∧ x ^ 2 < 1 := by
  use -0.99
  constructor
  numbers
  numbers

example : ∃ a b : ℕ, 2 ^ a = 5 * b + 1 := by
  use 4,3
  numbers

example (x : ℚ) : ∃ y : ℚ, y ^ 2 > x := by
  use x+1
  have h: x≥0 ∨ x<0 := by exact le_or_gt 0 x
  obtain h|h := h
  calc
    (x+1)^2
    _ = 1+x+x+x^2 := by ring
    _ ≥ 1+x+x := by extra
    _ ≥ 1+x := by addarith[h]
    _ > x := by extra
  calc
    (x+1)^2
    _ ≥ 0 := by extra
    _ > x := by rel[h]



example {t : ℝ} (h : ∃ a : ℝ, a * t + 1 < a + t) : t ≠ 1 := by
  obtain ⟨a,ha⟩ := h
  apply ne_iff_lt_or_gt.mpr
  have h2 := le_or_gt a 1
  obtain h2|h2 := h2
  --if a≤1, t>1
  right
  sorry
  --if a>1, t<1
  left
  sorry

example {m : ℤ} (h : ∃ a, 2 * a = m) : m ≠ 5 := by
  obtain ⟨a,ha⟩ := h
  apply ne_iff_lt_or_gt.mpr
  have h2 := le_or_gt a 2
  obtain h2|h2 := h2
  left
  calc
    m
    _ = 2*a := by rw[ha]
    _ ≤ 2*2 := by rel[h2]
    _ = 4 := by ring
    _ < 5 := by numbers
  have h3 : a ≥ 3 := by addarith[h2]
  right
  calc
    m
    _ = 2*a := by rw[ha]
    _ ≥ 2*3 := by rel[h3]
    _ = 6 := by ring
    _ > 5 := by numbers

lemma help1 {n : ℤ} (h : 0 < n) : 2*n-1 ≥ 0 := by
  have h2 : n ≥ 1 := by addarith[h]
  calc
    2*n-1
    _ ≥ 2*1-1 := by rel[h2]
    _ = 1 := by numbers
    _ ≥ 0 := by numbers

lemma help2 {n : ℤ} : 2*n^2-n ≥ 0 := by
  have h0 := lt_trichotomy n 0
  obtain h0|h0|h0 := h0
  have h0 : -n > 0 := by addarith[h0]
  calc
    2*n^2-n
    _ = 2*(-n)^2+(-n) := by ring
    _ ≥ 2*(-n)^2 := by extra
    _ ≥ 0 := by extra
  calc
    2*n^2-n
    _ = 2*0^2-0 := by rw[h0]
    _ ≥ 0 := by numbers
  have h1: 2*n-1 ≥ 0 := help1 h0
  calc
    2*n^2-n
    _ = n*(2*n-1) := by ring
    _ ≥ 0*0 := by rel[h0,h1]

example {n : ℤ} : ∃ a, 2 * a ^ 3 ≥ n * a + 7 := by
  use n^2+2
  have h0 := eq_or_ne n 0
  obtain h0|h0 := h0
  have h : 12*n^2-n ≥ 0 :=
  calc
    12*n^2-n
    _ = 12*0^2-0 := by rw[h0]
    --_ = 0 := by ring
    _ ≥ 0 := by numbers
  calc
    2 * (n ^ 2 + 2) ^ 3
    _ = 2*(0^2+2)^3 := by rw[h0]
    --_ = 16 := by ring
    --_ = 16 + 0*(0^2+2)+7 - (0*(0^2+2)+7) := by ring
    _ = 9 + 0*(0^2+2)+7 := by ring
    _ = 9 + n*(n^2+2)+7 := by rw[h0]
    _ ≥ n*(n^2+2)+7 := by extra
  have h : 12*n^2-n ≥ 0 :=
  calc
    12*n^2-n
    _ = 10*n^2 + (2*n^2-n) := by ring
    _ ≥ (2*n^2-n) := by extra
    _ ≥ 0 := by exact help2
  -- main calculation
  calc
    2*(n^2+2)^3
    --_ = 2*n^6+12*n^4+24*n^2+16 - (n*(n^2+2)+7) + (n*(n^2+2)+7) := by ring
    --_ = (2*n^6+12*n^4-n^3+24*n^2-2*n+9) + (n*(n^2+2)+7) := by ring
    _ = (2*n^6+9) + (12*n^4-n^3+24*n^2-2*n) + (n*(n^2+2)+7) := by ring
    _ ≥ (12*n^4-n^3+24*n^2-2*n) + (n*(n^2+2)+7) := by extra
    _ = n^2*(12*n^2-n) + 2*(12*n^2-n) + (n*(n^2+2)+7) := by ring
    _ ≥ n^2*0 + 2*0 + (n*(n^2+2)+7) := by rel[h]
    _ = (n*(n^2+2)+7) := by ring



example {a b c : ℝ} (ha : a ≤ b + c) (hb : b ≤ a + c) (hc : c ≤ a + b) :
    ∃ x y z, x ≥ 0 ∧ y ≥ 0 ∧ z ≥ 0 ∧ a = y + z ∧ b = x + z ∧ c = x + y := by
  use (-a+b+c)/2, (a-b+c)/2, (a+b-c)/2
  constructor
  addarith[ha]
  constructor
  addarith[hb]
  constructor
  addarith[hc]
  constructor
  ring
  constructor
  ring
  ring

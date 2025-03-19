/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Library.Basic
import AutograderLib

math2001_init

open Nat

/-! # Homework 3

Don't forget to compare with the text version,
https://github.com/hrmacbeth/math2001/wiki/Homework-3,
for clearer statements and any special instructions. -/

@[autograded 2]
theorem problem1 {a b : ℚ} (h : a = 3 - b) : a + b = 3 ∨ a + b = 4 := by
  left
  addarith[h]


@[autograded 5]
theorem problem2 {t : ℚ} (h : t ^ 2 + t - 6 = 0) : t = 2 ∨ t = -3 := by
  have h2 :=
  calc
    (t+3)*(t-2) = t^2+t-6 := by ring
    _ = 0 := h
  have h3 := eq_zero_or_eq_zero_of_mul_eq_zero h2
  obtain h3|h3 := h3
  right
  addarith[h3]
  left
  addarith[h3]

@[autograded 3]
theorem problem3 : ∃ a b : ℕ, a ≠ 0 ∧ 2 ^ a = 5 * b + 1 := by
  use 4,3
  constructor
  numbers
  numbers

@[autograded 5]
theorem problem4 (x : ℚ) : ∃ y : ℚ, y ^ 2 > x := by
  use x+1
  calc
    (x+1)^2
    _ = x^2+2*x+1 := by ring
    _ > x := by sorry

@[autograded 5]
theorem problem5 {x : ℕ} (hx : Odd x) : Odd (x ^ 3) := by
  obtain ⟨k,hk⟩ := hx
  use k*(3+6*k+4*k^2)
  rw[hk]
  ring

@[autograded 5]
theorem problem6 (n : ℕ) : ∃ m ≥ n, Odd m := by
  use 2*n+1
  constructor
  have h : 2*n+1 > n :=
  calc
    2*n+1 = n+(n+1) := by ring
    _ > n := by extra
  sorry
  use n
  ring

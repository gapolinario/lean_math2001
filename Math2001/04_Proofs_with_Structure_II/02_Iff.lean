/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.ModEq

math2001_init

namespace Int


example {a : ℚ} : 3 * a + 1 ≤ 7 ↔ a ≤ 2 := by
  constructor
  · intro h
    calc a = ((3 * a + 1) - 1) / 3 := by ring
      _ ≤ (7 - 1) / 3 := by rel [h]
      _ = 2 := by numbers
  · intro h
    calc 3 * a + 1 ≤ 3 * 2 + 1 := by rel [h]
      _ = 7 := by numbers


example {n : ℤ} : 8 ∣ 5 * n ↔ 8 ∣ n := by
  constructor
  · intro hn
    obtain ⟨a, ha⟩ := hn
    use -3 * a + 2 * n
    calc
      n = -3 * (5 * n) + 16 * n := by ring
      _ = -3 * (8 * a) + 16 * n := by rw [ha]
      _ = 8 * (-3 * a + 2 * n) := by ring
  · intro hn
    obtain ⟨a, ha⟩ := hn
    use 5 * a
    calc 5 * n = 5 * (8 * a) := by rw [ha]
      _ = 8 * (5 * a) := by ring


theorem odd_iff_modEq (n : ℤ) : Odd n ↔ n ≡ 1 [ZMOD 2] := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := h
    dsimp [Int.ModEq]
    dsimp [(· ∣ ·)]
    use k
    addarith [hk]
  · intro h
    obtain ⟨k,hk⟩ := h
    use k
    addarith[hk]

-- Anki
example (n : ℤ) : n ≡ 0 [ZMOD 2] → Even n := by
  intro h
  obtain ⟨k,hk⟩ := h
  use k
  addarith[hk]

theorem even_iff_modEq (n : ℤ) : Even n ↔ n ≡ 0 [ZMOD 2] := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := h
    dsimp [Int.ModEq]
    dsimp [(· ∣ ·)]
    use k
    addarith [hk]
  · intro h
    obtain ⟨k,hk⟩ := h
    use k
    addarith[hk]

example {x : ℝ} : x ^ 2 + x - 6 = 0 ↔ x = -3 ∨ x = 2 := by
  constructor
  . intro h
    have h2 :=
      calc
        (x+3)*(x-2) = x^2+x-6 := by ring
        _ = 0 := by rw[h]
    have h3 := eq_zero_or_eq_zero_of_mul_eq_zero h2
    obtain h3|h3 := h3
    left
    addarith[h3]
    right
    addarith[h3]
  . intro h
    obtain h|h := h
    calc
      x^2+x-6 = (-3)^2 + (-3) - 6 := by rw[h]
      _ = 0 := by ring
    calc
      x^2+x-6 = 2^2+2-6 := by rw[h]
      _ = 0 := by ring

example {a : ℤ} : a ^ 2 - 5 * a + 5 ≤ -1 ↔ a = 2 ∨ a = 3 := by
  constructor
  . intro h
    have h2 :=
    calc
      (2*a-5)^2 = 4 *(a^2-5*a+5)+5 := by ring
      _ ≤ 4*(-1)+5 := by rel[h]
      _ = 1^2 := by ring
    have h3 := abs_le_of_sq_le_sq' h2 (by numbers)
    obtain ⟨hl,hr⟩ := h3
    have hl2 : 2 * a ≥ 2 * 2 := by addarith[hl]
    have hl3 : 2 * a ≤ 2 * 3 := by addarith[hr]
    cancel 2 at hl2
    cancel 2 at hl3
    interval_cases a
    left
    rfl
    right
    rfl
  . intro h
    obtain h|h := h
    calc
      a^2-5*a+5 = 2^2-5*2+5 := by rw[h]
      _ ≤ -1 := by numbers
    calc
      a^2-5*a+5 = 3^2-5*3+5 := by rw[h]
      _ ≤ -1 := by numbers


example {n : ℤ} (hn : n ^ 2 - 10 * n + 24 = 0) : Even n := by
  have hn1 :=
    calc (n - 4) * (n - 6) = n ^ 2 - 10 * n + 24 := by ring
      _ = 0 := hn
  have hn2 := eq_zero_or_eq_zero_of_mul_eq_zero hn1
  obtain h|h := hn2
  use 2
  addarith[h]
  use 3
  addarith[h]

example {n : ℤ} (hn : n ^ 2 - 10 * n + 24 = 0) : Even n := by
  have hn1 :=
    calc (n - 4) * (n - 6) = n ^ 2 - 10 * n + 24 := by ring
      _ = 0 := hn
  rw [mul_eq_zero] at hn1 -- `hn1 : n - 4 = 0 ∨ n - 6 = 0`
  obtain h|h := hn1
  use 2
  addarith[h]
  use 3
  addarith[h]

example {x y : ℤ} (hx : Odd x) (hy : Odd y) : Odd (x + y + 1) := by
  rw [Int.odd_iff_modEq] at *
  calc x + y + 1 ≡ 1 + 1 + 1 [ZMOD 2] := by rel [hx, hy]
    _ = 2 * 1 + 1 := by ring
    _ ≡ 1 [ZMOD 2] := by extra


example (n : ℤ) : Even n ∨ Odd n := by
  mod_cases hn : n % 2
  · left
    rw [Int.even_iff_modEq]
    apply hn
  · right
    rw [Int.odd_iff_modEq]
    apply hn

/-! # Exercises -/


example {x : ℝ} : 2 * x - 1 = 11 ↔ x = 6 := by
  constructor
  intro h
  calc
    x = ((2*x-1)+1)/2 := by ring
    _ = (11+1)/2 := by rw[h]
    _ = 6 := by ring
  intro h
  calc
    2*x-1 = 2*6-1 := by rw[h]
    _ = 11 := by ring

example {n : ℤ} : 63 ∣ n ↔ 7 ∣ n ∧ 9 ∣ n := by
  constructor
  . intro h
    obtain ⟨a,ha⟩ := h
    constructor
    . use 9*a
      rw[ha]
      ring
    . use 7*a
      rw[ha]
      ring
  . intro h
    obtain ⟨h1,h2⟩ := h
    obtain ⟨a,ha⟩ := h1
    obtain ⟨b,hb⟩ := h2
    use 4*b-3*a
    calc
      n = 28*n-27*n := by ring
      _ = 28*(9*b)-27*n := by rw[hb]
      _ = 28*(9*b)-27*(7*a) := by rw[ha]
      _ = 63*(4*b-3*a) := by ring


theorem dvd_iff_modEq {a n : ℤ} : n ∣ a ↔ a ≡ 0 [ZMOD n] := by
  constructor
  . intro h
    obtain ⟨x,hx⟩ := h
    use x
    rw[hx]
    ring
  . intro h
    obtain ⟨x,hx⟩ := h
    have hx : a = n*x := by addarith[hx]
    use x
    apply hx

example {a b : ℤ} (hab : a ∣ b) : a ∣ 2 * b ^ 3 - b ^ 2 + 3 * b := by
  obtain ⟨n,hn⟩ := hab
  use 2*a^2*n^3-a*n^2+3*n
  calc
    2*b^3-b^2+3*b = 2*(a*n)^3-(a*n)^2+3*(a*n) := by rw[hn]
    _ = a*(2*a^2*n^3-a*n^2+3*n) := by ring

-- temp lemma
lemma lt_of_sq_lt_sq {k b: ℕ} (h: k^2 < b^2) : k < b := by
  have h2: b ≤ k ∨ b > k := le_or_gt b k
  obtain h2|h2 := h2
  have h3: k^2 ≥ b^2 := by rel[h2]
  have h3: ¬(k^2 < b^2) := not_lt_of_ge h3
  contradiction
  exact h2

example {k : ℕ} : k ^ 2 ≤ 6 ↔ k = 0 ∨ k = 1 ∨ k = 2 := by
  constructor
  . intro h
    have h2 :=
    calc
      k^2 ≤ 6 := by rel[h]
      _ < 3^2 := by numbers
    have h3 : k < 3 := lt_of_sq_lt_sq h2
    interval_cases k
    left
    rfl
    right
    left
    rfl
    right
    right
    rfl
  . intro h
    obtain h|h|h := h
    rw[h]
    numbers
    rw[h]
    numbers
    rw[h]
    numbers

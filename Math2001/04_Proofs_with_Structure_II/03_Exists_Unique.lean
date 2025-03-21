/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Theory.ModEq.Defs

math2001_init

namespace Int


example : ∃! a : ℝ, 3 * a + 1 = 7 := by
  use 2
  dsimp
  constructor
  · numbers
  intro y hy
  calc
    y = (3 * y + 1 - 1) / 3 := by ring
    _ = (7 - 1) / 3 := by rw [hy]
    _ = 2 := by numbers


example : ∃! x : ℚ, ∀ a, a ≥ 1 → a ≤ 3 → (a - x) ^ 2 ≤ 1 := by
  use 2
  constructor
  . intro a h1 h2
    rw[← one_pow 2]
    apply sq_le_sq'
    addarith[h1]
    addarith[h2]
  . intro y h1
    have h2 := h1 1 (by numbers) (by numbers)
    have h3 := h1 3 (by numbers) (by numbers)
    rw[← one_pow 2] at h2
    rw[← one_pow 2] at h3
    have h4:= abs_le_of_sq_le_sq' h2 (by numbers)
    have h5:= abs_le_of_sq_le_sq' h3 (by numbers)
    --rw[one_pow 2] at h4
    obtain ⟨h4,_⟩ := h4
    obtain ⟨_,h5⟩ := h5
    have h6: y ≤ 2 := by addarith[h4]
    --have h6': y ≥ 0 := by addarith[h4']
    --have h7: y ≤ 4 := by addarith[h5]
    have h7: y ≥ 2 := by addarith[h5]
    apply le_antisymm
    apply h6
    apply h7



example {x : ℚ} (hx : ∃! a : ℚ, a ^ 2 = x) : x = 0 := by
  obtain ⟨a, ha1, ha2⟩ := hx
  have h1 : -a = a
  · apply ha2
    calc
      (-a) ^ 2 = a ^ 2 := by ring
      _ = x := ha1
  have h2 :=
    calc
      a = (a - -a) / 2 := by ring
      _ = (a - a) / 2 := by rw [h1]
      _ = 0 := by ring
  calc
    x = a ^ 2 := by rw [ha1]
    _ = 0 ^ 2 := by rw [h2]
    _ = 0 := by ring


example : ∃! r : ℤ, 0 ≤ r ∧ r < 5 ∧ 14 ≡ r [ZMOD 5] := by
  use 4
  dsimp
  constructor
  · constructor
    · numbers
    constructor
    · numbers
    use 2
    numbers
  intro r hr
  obtain ⟨hr1, hr2, q, hr3⟩ := hr
  have :=
    calc
      5 * 1 < 14 - r := by addarith [hr2]
      _ = 5 * q := by rw [hr3]
  cancel 5 at this
  have :=
    calc
      5 * q = 14 - r := by rw [hr3]
      _ < 5 * 3 := by addarith [hr1]
  cancel 5 at this
  interval_cases q
  addarith [hr3]

/-! # Exercises -/


example : ∃! x : ℚ, 4 * x - 3 = 9 := by
  use 3
  constructor
  . rfl
  . intro y hy
    calc
      y = ((4*y-3)+3)/4 := by ring
      _ = (9+3)/4 := by rw[hy]
      _ = 3 := by numbers


example : ∃! n : ℕ, ∀ a, n ≤ a := by
  use 0
  constructor
  . intro a
    have h := zero_le a
    apply h
  . intro y hy
    obtain h|h|h := lt_trichotomy y 0
    have h2 := Nat.not_lt_zero y
    contradiction
    apply h
    --have h2 := Nat.not_lt_zero y
    have h3 := hy 0
    rw[← not_le] at h
    contradiction

example : ∃! r : ℤ, 0 ≤ r ∧ r < 3 ∧ 11 ≡ r [ZMOD 3] := by
  use 2
  dsimp
  constructor
  . constructor
    numbers
    constructor
    numbers
    use 3
    numbers
  . intro y hy
    obtain ⟨h1,h2,q,h3⟩ := hy
    sorry

/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Theory.ParityModular
import Library.Basic
import Library.Tactic.ModEq

math2001_init

open Int


example : ¬ (∀ x : ℝ, x ^ 2 ≥ x) := by
  intro h
  have : 0.5 ^ 2 ≥ 0.5 := h 0.5
  numbers at this


example : ¬ 3 ∣ 13 := by
  intro H
  obtain ⟨k, hk⟩ := H
  obtain h4 | h5 := le_or_succ_le k 4
  · have h :=
    calc 13 = 3 * k := hk
      _ ≤ 3 * 4 := by rel [h4]
    numbers at h
  · have h :=
    calc
      13 = 3 * k := hk
      _ ≥ 3 * 5 := by rel[h5]
    numbers at h


example {x y : ℝ} (h : x + y = 0) : ¬(x > 0 ∧ y > 0) := by
  intro h
  obtain ⟨hx, hy⟩ := h
  have H :=
  calc 0 = x + y := by rw [h]
    _ > 0 := by extra
  numbers at H

-- no indentation, doesn't work
example : ¬ (∃ n : ℕ, n ^ 2 = 2) := by
  intro h
  obtain ⟨n,hn⟩ := h
  obtain h|h := le_or_succ_le n 1
  have h2 :=
    calc
      2 = n^2 := by rw[hn]
      _  ≤ 1^2 := by rel[h]
  numbers at h2
  have h2 :=
    calc
      2 = n^2 := by rw[hn]
      _ ≥ 2^2 := by rel[h]
      _ ≥ 4 := by numbers
  numbers at h2

-- with indentation, does work
example : ¬ (∃ n : ℕ, n ^ 2 = 2) := by
  intro h
  obtain ⟨n,hn⟩ := h
  obtain h|h := le_or_succ_le n 1
  . have h2 :=
      calc
        2 = n^2 := by rw[hn]
        _  ≤ 1^2 := by rel[h]
    numbers at h2
  . have h2 :=
      calc
        2 = n^2 := by rw[hn]
        _ ≥ 2^2 := by rel[h]
    numbers at h2


example (n : ℤ) : Int.Even n ↔ ¬ Int.Odd n := by
  constructor
  · intro h1 h2
    rw [Int.even_iff_modEq] at h1
    rw [Int.odd_iff_modEq] at h2
    have h :=
    calc 0 ≡ n [ZMOD 2] := by rel [h1]
      _ ≡ 1 [ZMOD 2] := by rel [h2]
    numbers at h -- contradiction!
  · intro h
    obtain h1 | h2 := Int.even_or_odd n
    · apply h1
    · contradiction


example (n : ℤ) : Int.Odd n ↔ ¬ Int.Even n := by
  constructor
  . intro h1 h2
    rw[Int.odd_iff_modEq] at h1
    rw[Int.even_iff_modEq] at h2
    have h :=
      calc
        0 ≡ n [ZMOD 2] := by rel[h2]
        _ ≡ 1 [ZMOD 2] := by rel[h1]
    numbers at h
  . intro h
    obtain h2|h2 := even_or_odd n
    contradiction
    apply h2

-- this works
example (n : ℤ) : ¬(n ^ 2 ≡ 2 [ZMOD 3]) := by
  intro h
  mod_cases hn : n % 3
  · have h :=
    calc (0:ℤ) = 0 ^ 2 := by numbers
      _ ≡ n ^ 2 [ZMOD 3] := by rel [hn]
      _ ≡ 2 [ZMOD 3] := by rel [h]
    numbers at h -- contradiction!
  · have h :=
      calc 1 = 1^2 := by numbers
        _ ≡ n^2 [ZMOD 3] := by rel[hn]
        _ ≡ 2 [ZMOD 3] := by rel[h]
    numbers at h
  · have h :=
      calc 1
        _ ≡ 1 + 3*1 [ZMOD 3] := by extra
        _ = 2^2 := by numbers
        _ ≡ n^2 [ZMOD 3] := by rel[hn]
        _ ≡ 2 [ZMOD 3] := by rel[h]
    numbers at h

-- this doesn't work, why?
example (n : ℤ) : ¬(n ^ 2 ≡ 2 [ZMOD 3]) := by
  intro h
  mod_cases hn : n % 3
  · have h :=
    calc (0:ℤ) = 0 ^ 2 := by numbers
      _ ≡ n ^ 2 [ZMOD 3] := by rel [hn]
      _ ≡ 2 [ZMOD 3] := by rel [h]
    numbers at h -- contradiction!
  · have h :=
      calc 1 = 1^2 := by numbers
        _ ≡ n^2 [ZMOD 3] := by rel[hn]
        _ ≡ 2 [ZMOD 3] := by rel[h]
    numbers at h
  · have h :=
      calc (4:ℤ)
        _ = 2^2 := by numbers
        _ ≡ n^2 [ZMOD 3] := by rel[hn]
        _ ≡ 2 [ZMOD 3] := by rel[h]
    numbers at h
    sorry

example {p : ℕ} (k l : ℕ) (hk1 : k ≠ 1) (hkp : k ≠ p) (hkl : p = k * l) :
    ¬(Prime p) := by
  have hk : k ∣ p
  · use l
    apply hkl
  intro h
  obtain ⟨h2, hfact⟩ := h
  have : k = 1 ∨ k = p := hfact k hk
  obtain hk1' | hkp' := this
  · contradiction
  · contradiction


example (a b : ℤ) (h : ∃ q, b * q < a ∧ a < b * (q + 1)) : ¬b ∣ a := by
  intro H
  obtain ⟨k, hk⟩ := H
  obtain ⟨q, hq₁, hq₂⟩ := h
  have hb :=
  calc 0 = a - a := by ring
    _ < b * (q + 1) - b * q := by rel [hq₁, hq₂]
    _ = b := by ring
  have h1 :=
  calc b * k = a := by rw [hk]
    _ < b * (q + 1) := hq₂
  cancel b at h1
  sorry

example {p : ℕ} (hp : 2 ≤ p)  (T : ℕ) (hTp : p < T ^ 2)
    (H : ∀ (m : ℕ), 1 < m → m < T → ¬ (m ∣ p)) :
    Prime p := by
  apply prime_test hp
  intro m hm1 hmp
  obtain hmT | hmT := lt_or_le m T
  · apply H m hm1 hmT
  intro h_div
  obtain ⟨l, hl⟩ := h_div
  have : l ∣ p
  · sorry
  have hl1 :=
    calc m * 1 = m := by ring
      _ < p := hmp
      _ = m * l := hl
  cancel m at hl1
  have hl2 : l < T
  · sorry
  have : ¬ l ∣ p := H l hl1 hl2
  contradiction


example : Prime 79 := by
  apply better_prime_test (T := 9)
  · numbers
  · numbers
  intro m hm1 hm2
  apply Nat.not_dvd_of_exists_lt_and_lt
  interval_cases m
  · use 39
    constructor <;> numbers
  · use 26
    constructor <;> numbers
  · use 19
    constructor <;> numbers
  · sorry
  · sorry
  · sorry
  · sorry

/-! # Exercises -/


example : ¬ (∃ t : ℝ, t ≤ 4 ∧ t ≥ 5) := by
  intro h
  obtain ⟨t,ht1,ht2⟩ := h
  have ht3 : ¬(t ≥ 5) := by addarith[ht1]
  contradiction

example : ¬ (∃ a : ℝ, a ^ 2 ≤ 8 ∧ a ^ 3 ≥ 30) := by
  intro h
  obtain ⟨t,h1,h2⟩ := h
  have h3 : t^2 < 3^2 := by addarith[h1]
  obtain ⟨hl,hr⟩ := abs_lt_of_sq_lt_sq' h3 (by numbers)
  obtain h4|h4 := le_or_lt t 0
  . have h5 :=
      calc
        t^3 = t^2 * t := by ring
        _ ≤ t^2 * 0 := by rel[h4]
        _ = 0 := by ring
        _ < 30 := by numbers
    have h6 := not_le_of_lt h5
    contradiction
  . have h5 :=
      calc
        t^3 ≤ 3^3 := by rel[hr]
        _ < 30 := by numbers
    have h6 := not_le_of_lt h5
    contradiction

example : ¬ Int.Even 7 := by
  sorry

example {n : ℤ} (hn : n + 3 = 7) : ¬ (Int.Even n ∧ n ^ 2 = 10) := by
  sorry

example {x : ℝ} (hx : x ^ 2 < 9) : ¬ (x ≤ -3 ∨ x ≥ 3) := by
  sorry

example : ¬ (∃ N : ℕ, ∀ k > N, Nat.Even k) := by
  sorry

example (n : ℤ) : ¬(n ^ 2 ≡ 2 [ZMOD 4]) := by
  sorry

example : ¬ Prime 1 := by
  sorry

example : Prime 97 := by
  sorry

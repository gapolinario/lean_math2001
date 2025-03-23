/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.ModEq

math2001_init


example {y : ℝ} (x : ℝ) (h : 0 < x * y) (hx : 0 ≤ x) : 0 < y := by
  obtain hneg | hpos : y ≤ 0 ∨ 0 < y := le_or_lt y 0
  · -- the case `y ≤ 0`
    have : ¬0 < x * y
    · apply not_lt_of_ge
      calc
        0 = x * 0 := by ring
        _ ≥ x * y := by rel [hneg]
    contradiction
  · -- the case `0 < y`
    apply hpos


example {t : ℤ} (h2 : t < 3) (h : t - 1 = 6) : t = 13 := by
  have H :=
  calc
    7 = t := by addarith [h]
    _ < 3 := h2
  have : ¬(7 : ℤ) < 3 := by numbers
  contradiction


example {t : ℤ} (h2 : t < 3) (h : t - 1 = 6) : t = 13 := by
  have H :=
  calc
    7 = t := by addarith [h]
    _ < 3 := h2
  numbers at H -- this is a contradiction!


example (n : ℤ) (hn : n ^ 2 + n + 1 ≡ 1 [ZMOD 3]) :
    n ≡ 0 [ZMOD 3] ∨ n ≡ 2 [ZMOD 3] := by
  mod_cases h : n % 3
  · -- case 1: `n ≡ 0 [ZMOD 3]`
    left
    apply h
  · -- case 2: `n ≡ 1 [ZMOD 3]`
    have H :=
      calc 0 ≡ 0 + 3 * 1 [ZMOD 3] := by extra
      _ = 1 ^ 2 + 1 + 1 := by numbers
      _ ≡ n ^ 2 + n + 1 [ZMOD 3] := by rel [h]
      _ ≡ 1 [ZMOD 3] := hn
    numbers at H -- contradiction!
  · -- case 3: `n ≡ 2 [ZMOD 3]`
    right
    apply h


example {p : ℕ} (hp : 2 ≤ p) (H : ∀ m : ℕ, 1 < m → m < p → ¬m ∣ p) : Prime p := by
  constructor
  · apply hp -- show that `2 ≤ p`
  intro m hmp
  have hp' : 0 < p := by extra
  have h1m : 1 ≤ m := Nat.pos_of_dvd_of_pos hmp hp'
  obtain hm | hm : 1 = m ∨ 1 < m := eq_or_lt_of_le h1m
  · -- the case `m = 1`
    left
    addarith [hm]
  . -- the case `1 < m`
    have h1 := Nat.le_of_dvd hp' hmp
    -- below, the same thing
    /-have h1 : m ≤ p := by
      apply Nat.le_of_dvd
      apply hp'
      apply hmp-/
    have h2 := lt_trichotomy m p
    obtain h2|h2|h2 := h2
    left
    have H' := H m hm h2
    contradiction
    right
    apply h2
    rw [← not_lt] at h1
    contradiction



example : Prime 5 := by
  apply prime_test
  · numbers
  intro m hm_left hm_right
  apply Nat.not_dvd_of_exists_lt_and_lt
  interval_cases m
  · use 2
    constructor <;> numbers
  · use 1
    constructor <;> numbers
  · use 1
    constructor <;> numbers

-- I first proved this in 02_Iff
-- Now I could golf one line
lemma lt_of_sq_lt_sq {k b: ℕ} (h: k^2 < b^2) : k < b := by
  obtain h2|h2 := le_or_gt b k
  have h3: k^2 ≥ b^2 := by rel[h2]
  have h3: ¬(k^2 < b^2) := not_lt_of_ge h3
  contradiction
  exact h2

example {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h_pyth : a ^ 2 + b ^ 2 = c ^ 2) : 3 ≤ a := by
  have h1 := le_or_lt 3 a
  obtain h1|h1 := h1
  apply h1
  interval_cases a
  obtain h2|h2 := le_or_lt b 2
  have h3 :=
  calc
    c^2 = 1^2+b^2 := by rw[h_pyth]
    _ ≤ 1^2+2^2 := by rel[h2]
    _ < 3^2 := by numbers
  have h4 := lt_of_sq_lt_sq h3
  interval_cases b
  interval_cases c
  --numbers at h_pyth
  have h': 2=1 := by addarith[h_pyth]
  exfalso; exact Nat.succ_ne_self 1 h'
  have h': 2=4 := by addarith[h_pyth]
  have h'': ¬(2=4) := by numbers
  contradiction
  interval_cases c
  have h': 5=4 := by addarith[h_pyth]
  have h'': ¬(5=4) := by numbers
  contradiction
  have h': 5=4 := by addarith[h_pyth]
  have h'': ¬(5=4) := by numbers
  contradiction
  have h3 :=
  calc
    b^2 < 1^2+b^2 := by extra
    _ = c^2 := by rw[h_pyth]
  have h4 := lt_of_sq_lt_sq h3
  have h5 : b+1 ≤ c := by addarith[h4]
  have h6 :=
  calc
    c^2 = 1^2 + b^2 := by rw[h_pyth]
    _ ≤ 1^2 + 3 + b^2 := by extra
    _ = b^2 + 2*2 := by ring
    _ < b^2+2*b := by rel[h2]
    _ < b^2+2*b+1 := by extra
    _ = (b+1)^2 := by ring
  have h7 := lt_of_sq_lt_sq h6
  have h8 := not_le_of_lt h7
  contradiction
  sorry


/-! # Exercises -/


example {x y : ℝ} (n : ℕ) (hx : 0 ≤ x) (hn : 0 < n) (h : y ^ n ≤ x ^ n) :
    y ≤ x := by
  have h2 := le_or_lt y x
  obtain h2|h2 := h2
  . apply h2
  . rw[← not_le] at h2
    sorry

example (n : ℤ) (hn : n ^ 2 ≡ 4 [ZMOD 5]) : n ≡ 2 [ZMOD 5] ∨ n ≡ 3 [ZMOD 5] := by
  obtain ⟨x,hx⟩ := hn
  sorry




example : Prime 7 := by
  apply prime_test
  · numbers
  intro m hm_left hm_right
  apply Nat.not_dvd_of_exists_lt_and_lt
  interval_cases m
  · use 3
    constructor <;> numbers
  · use 2
    constructor <;> numbers
  · use 1
    constructor <;> numbers
  . use 1
    constructor <;> numbers
  . use 1
    constructor <;> numbers

example {x : ℚ} (h1 : x ^ 2 = 4) (h2 : 1 < x) : x = 2 := by
  have h3 :=
    calc
      (x + 2) * (x - 2) = x ^ 2 + 2 * x - 2 * x - 4 := by ring
      _ = 0 := by addarith [h1]
  rw [mul_eq_zero] at h3
  obtain h3|h3 := h3
  have h4 : x=-2 := by addarith[h3]
  have h5 :=
  calc
    x = -2 := by rw[h4]
    _ ≤ 1 := by numbers
  rw[← not_lt] at h5
  contradiction
  addarith[h3]


namespace Nat

example (p : ℕ) (h : Prime p) : p = 2 ∨ Odd p := by
  dsimp[Prime] at h
  have h2 := even_or_odd p
  obtain h2|h2 := h2
  . obtain h3|h3 := eq_or_ne p 2
    . left
      apply h3
    . obtain ⟨hl,hr⟩ := h
      --have h4 := Even.two_dvd h2 -- doesn't work for some reason
      obtain ⟨k,hk⟩ := h2
      have h4 : 2 ∣ p := by
        use k
        apply hk
      have h5 := hr 2 h4
      obtain h5|h5 := h5
      . numbers at h5
      . left
        addarith[h5]
  . right
    apply h2

/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Tactic.GCongr
import Library.Basic

math2001_init

open Nat


def F : ℕ → ℤ
  | 0 => 1
  | 1 => 1
  | n + 2 => F (n + 1) + F n

theorem F_bound (n : ℕ) : F n ≤ 2 ^ n := by
  match n with
  | 0 =>
      calc F 0 = 1 := by rw [F]
        _ ≤ 2 ^ 0 := by numbers
  | 1 =>
      calc F 1 = 1 := by rw [F]
        _ ≤ 2 ^ 1 := by numbers
  | k + 2  =>
      have IH1 := F_bound k -- first inductive hypothesis
      have IH2 := F_bound (k + 1) -- second inductive hypothesis
      calc F (k + 2) = F (k + 1) + F k := by rw [F]
        _ ≤ 2 ^ (k + 1) + 2 ^ k := by rel [IH1, IH2]
        _ ≤ 2 ^ (k + 1) + 2 ^ k + 2 ^ k := by extra
        _ = 2 ^ (k + 2) := by ring


namespace Nat

theorem exists_prime_factor {n : ℕ} (hn2 : 2 ≤ n) : ∃ p : ℕ, Prime p ∧ p ∣ n := by
  by_cases hn : Prime n
  . -- case 1: `n` is prime
    use n
    constructor
    · apply hn
    · use 1
      ring
  . -- case 2: `n` is not prime
    obtain ⟨m, hmn, _, ⟨x, hx⟩⟩ := exists_factor_of_not_prime hn hn2
    have IH : ∃ p, Prime p ∧ p ∣ m := exists_prime_factor hmn -- inductive hypothesis
    obtain ⟨p, hp, y, hy⟩ := IH
    use p
    constructor
    · apply hp
    · use x * y
      calc n = m * x := hx
        _ = (p * y) * x := by rw [hy]
        _ = p * (x * y) := by ring

/-! # Exercises -/


theorem extract_pow_two (n : ℕ) (hn : 0 < n) : ∃ a x, Odd x ∧ n = 2 ^ a * x := by
  obtain h|h := even_or_odd n
  . match n with
    | 1 =>
      have h' : Odd 1 := by use 0; numbers
      have h'' := (odd_iff_not_even 1).mp h'
      contradiction
    | 2 =>
      use 1,1
      constructor
      . use 0
        numbers
      . numbers
    | k+2 =>
      obtain h2|h2|h2 := lt_trichotomy k 0
      . have h3 := not_lt_zero k
        contradiction
      . use 1,1
        constructor
        . use 0
          numbers
        . rw[h2]
          numbers
      have IH := extract_pow_two k h2
      obtain ⟨a,x,⟨hl,hr⟩⟩ := IH
      sorry

  . use 0, n
    constructor
    . apply h
    . ring

theorem extract_pow_two' (n : ℕ) (hn : 0 < n) : ∃ a x, Odd x ∧ n = 2 ^ a * x := by
  obtain h|h := even_or_odd n
  . obtain ⟨k,hk⟩ := h
    obtain h|h|h := lt_trichotomy k 1
    . have h : k = 0 := by addarith[h]
      have h2 :=
        calc
          n = 2*k := by rw[hk]
          _ = 2*0 := by rw[h]
          _ = 0 := by ring
      have h3 :=
        calc
          0 < n := by rel[hn]
          _ = 0 := by rw[h2]
      numbers at h3
    . use 1,1
      constructor
      . use 0
        numbers
      . rw[hk,h]
        numbers
    . have h' :=
        calc
          2 = 2*1 := by numbers
          _ < 2*k := by rel[h]
          _ = n := by rw[hk]
      have h'' :=
        calc
          0 = 2-2 := by numbers
          _ < n-2 := by rel[h']
      induction_from_starting_point k,h with p hp IH
      . use 2,1
        constructor
        . use 0
          numbers
        . rw[hk]
          numbers
      . sorry
  . use 0, n
    constructor
    . apply h
    . ring

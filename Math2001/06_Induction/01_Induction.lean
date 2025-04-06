/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.ModEq

math2001_init

namespace Nat


example (n : ℕ) : 2 ^ n ≥ n + 1 := by
  simple_induction n with k IH
  · -- base case
    numbers
  · -- inductive step
    calc 2 ^ (k + 1) = 2 * 2 ^ k := by ring
      _ ≥ 2 * (k + 1) := by rel [IH]
      _ = (k + 1 + 1) + k := by ring
      _ ≥ k + 1 + 1 := by extra


example (n : ℕ) : Even n ∨ Odd n := by
  simple_induction n with k IH
  · -- base case
    left
    use 0
    numbers
  · -- inductive step
    obtain ⟨x, hx⟩ | ⟨x, hx⟩ := IH
    · right
      use x
      rw[hx]
    · left
      use x+1
      rw[hx]
      ring

example {a b d : ℤ} (h : a ≡ b [ZMOD d]) (n : ℕ) : a ^ n ≡ b ^ n [ZMOD d] := by
  simple_induction n with k IH
  . use 0
    ring
  . calc
      a^(k+1) = a * a^k := by ring
      _ ≡ b * a^k [ZMOD d] := by rel[h]
      _ ≡ b * b^k [ZMOD d] := by rel[IH]
      _ = b^(k+1) := by ring

example (n : ℕ) : 4 ^ n ≡ 1 [ZMOD 15] ∨ 4 ^ n ≡ 4 [ZMOD 15] := by
  simple_induction n with k IH
  · -- base case
    left
    numbers
  · -- inductive step
    obtain hk | hk := IH
    · right
      calc (4:ℤ) ^ (k + 1) = 4 * 4 ^ k := by ring
        _ ≡ 4 * 1 [ZMOD 15] := by rel [hk]
        _ = 4 := by numbers
    · left
      calc (4:ℤ) ^ (k + 1) = 4 * 4 ^ k := by ring
        _ ≡ 4 * 4 [ZMOD 15] := by rel [hk]
        _ = 15 * 1 + 1 := by numbers
        _ ≡ 1 [ZMOD 15] := by extra


example {n : ℕ} (hn : 2 ≤ n) : (3:ℤ) ^ n ≥ 2 ^ n + 5 := by
  induction_from_starting_point n, hn with k hk IH
  · -- base case
    numbers
  · -- inductive step
    calc (3:ℤ) ^ (k + 1) = 2 * 3 ^ k + 3 ^ k := by ring
      _ ≥ 2 * (2 ^ k + 5) + 3 ^ k := by rel [IH]
      _ = 2 ^ (k + 1) + 5 + (5 + 3 ^ k) := by ring
      _ ≥ 2 ^ (k + 1) + 5 := by extra


example : forall_sufficiently_large n : ℕ, 2 ^ n ≥ n ^ 2 := by
  dsimp
  use 4
  intro n hn
  induction_from_starting_point n, hn with k hk IH
  · -- base case
    numbers
  · -- inductive step
    calc
      2^(k+1) = 2 * 2^k := by ring
      _ ≥ 2 * k^2 := by rel[IH]
      _ = k^2 + k*k := by ring
      _ ≥ k^2 + 4*k := by rel[hk]
      _ = k^2 + 2*k + 2*k := by ring
      _ ≥ k^2 + 2*k + 2*4 := by rel[hk]
      _ = k^2 + 2*k + 1 + 7 := by ring
      _ ≥ k^2 + 2*k + 1 := by extra
      _ = (k+1)^2 := by ring


/-! # Exercises -/


example (n : ℕ) : 3 ^ n ≥ n ^ 2 + n + 1 := by
  simple_induction n with k IH
  . numbers
  . calc
      3^(k+1) = 3 * 3^k := by ring
      _ ≥ 3 * (k^2+k+1) := by rel[IH]
      _ = k^2 + 3*k + 3 + 2*k^2 := by ring
      _ ≥ k^2 + 3*k + 3 := by extra
      _ = (k^2+2*k+1) + (k+1) + 1 := by ring
      _ = (k+1)^2 + (k+1) + 1 := by ring

example {a : ℝ} (ha : -1 ≤ a) (n : ℕ) : (1 + a) ^ n ≥ 1 + n * a := by
  simple_induction n with k IH
  . calc
      (1+a)^0 ≥ (1+(-1))^0 := by rel[ha]
      _ = 1 := by ring
      _ = 1 + 0*a := by ring
  . have h :=
      calc
        1+a ≥ 1+(-1) := by rel[ha]
        _ = 0 := by numbers
    calc
      (1+a)^(k+1) = (1+a) * (1+a)^k := by ring
      _ ≥ (1+a) * (1+k*a) := by rel[IH]
      _ = 1 + k*a + a + k*a^2:= by ring
      _ ≥ 1 + k*a + a := by extra
      _ = 1 + (k+1)*a := by ring


example (n : ℕ) : 5 ^ n ≡ 1 [ZMOD 8] ∨ 5 ^ n ≡ 5 [ZMOD 8] := by
  simple_induction n with k IH
  . left
    numbers
  . obtain h|h := IH
    . right
      calc
        5^(k+1) = 5 * 5^k := by ring
        _ ≡ 5 * 1 [ZMOD 8] := by rel[h]
        _ = 8*0 + 5 := by numbers
        _ ≡ 5 [ZMOD 8] := by extra
    . left
      calc
        5^(k+1) = 5 * 5^k := by ring
        _ ≡ 5 * 5 [ZMOD 8] := by rel[h]
        _ = 8*3 + 1 := by numbers
        _ ≡ 1 [ZMOD 8] := by extra


example (n : ℕ) : 6 ^ n ≡ 1 [ZMOD 7] ∨ 6 ^ n ≡ 6 [ZMOD 7] := by
  simple_induction n with k IH
  . left
    numbers
  . obtain h|h := IH
    . right
      calc
        6^(k+1) = 6 * 6^k := by ring
          _ ≡ 6 * 1 [ZMOD 7] := by rel[h]
          _ = 7*0 + 6 := by numbers
          _ ≡ 6 [ZMOD 7] := by extra
    . left
      calc
        6^(k+1) = 6 * 6^k := by ring
        _ ≡ 6 * 6 [ZMOD 7] := by rel[h]
        _ = 7*5 + 1 := by numbers
        _ ≡ 1 [ZMOD 7] := by extra

example (n : ℕ) :
    4 ^ n ≡ 1 [ZMOD 7] ∨ 4 ^ n ≡ 2 [ZMOD 7] ∨ 4 ^ n ≡ 4 [ZMOD 7] := by
  simple_induction n with k IH
  . left
    numbers
  . obtain h|h|h := IH
    . right; right
      calc
        4^(k+1) = 4 * 4^k := by ring
        _ ≡ 4 * 1 [ZMOD 7] := by rel[h]
        _ = 7*0 + 4 := by ring
        _ ≡ 4 [ZMOD 7] := by extra
    . left
      calc
        4^(k+1) = 4 * 4^k := by ring
        _ ≡ 4 * 2 [ZMOD 7] := by rel[h]
        _ = 7*1 + 1 := by ring
        _ ≡ 1 [ZMOD 7] := by extra
    . right;left
      calc
        4^(k+1) = 4 * 4^k := by ring
        _ ≡ 4 * 4 [ZMOD 7] := by rel[h]
        _ = 7*2 + 2 := by ring
        _ ≡ 2 [ZMOD 7] := by extra

-- this wasn't working, then I replaced
-- 3→3:ℤ and now it does, why?
-- one hint for that is that rel[IH] wasn't working
-- that's because the types weren't the same
-- another, more obvious hint, is in the problem description
example : forall_sufficiently_large n : ℕ, (3:ℤ) ^ n ≥ 2 ^ n + 100 := by
  dsimp
  use 5
  intro x hx
  induction_from_starting_point x, hx with k hk IH
  . numbers
  . calc
      (3:ℤ)^(k+1) = 3 * 3^k := by ring
      _ ≥ 3 * ( 2^k + 100 ) := by rel[IH]
      _ = 3*2^k + 300 := by ring
      _ = 2*2^k + 100 + (200+1*2^k) := by ring
      _ ≥ 2*2^k + 100 := by extra
      _ = 2^(k+1) + 100 := by ring


example : forall_sufficiently_large n : ℕ, 2 ^ n ≥ n ^ 2 + 4 := by
  dsimp
  use 5
  intro x hx
  induction_from_starting_point x, hx with k hk IH
  . numbers
  . calc
      2^(k+1) = 2 * 2^k := by ring
      _ ≥ 2 * (k^2+4) := by rel[IH]
      _ = k^2 + k*k + 8 := by ring
      _ ≥ k^2 + 5*k + 8 := by rel[hk]
      _ = k^2 + 2*k +1 +4 + (3*k+3) := by ring
      _ ≥ k^2 + 2*k +1 +4 := by extra
      _ = (k+1)^2 + 4 := by ring

example : forall_sufficiently_large n : ℕ, 2 ^ n ≥ n ^ 3 := by
  dsimp
  use 10
  intro x hx
  induction_from_starting_point x, hx with k hk IH
  . numbers
  . calc
      2^(k+1) = 2 * 2^k := by ring
      _ ≥ 2 * k^3 := by rel[IH]
      _ = k^3 + k*k^2 := by ring
      _ ≥ k^3 + 10 * k^2 := by rel[hk]
      _ = k^3 + 3*k^2 + 7*k*k := by ring
      _ ≥ k^3 + 3*k^2 + 7*10*k := by rel[hk]
      _ = k^3 + 3*k^2 + 3*k + 67*k := by ring
      _ ≥ k^3 + 3*k^2 + 3*k + 67*10 := by rel[hk]
      _ = k^3 + 3*k^2 + 3*k + 1 + 669 := by ring
      _ ≥ k^3 + 3*k^2 + 3*k + 1 := by extra
      _ = (k+1)^3 := by ring

theorem Odd.pow {a : ℕ} (ha : Odd a) (n : ℕ) : Odd (a ^ n) := by
  obtain ⟨x,hx⟩ := ha
  simple_induction n with k IH
  . rw[hx]
    rw[pow_zero]
    use 0
    numbers
  . obtain ⟨y,hy⟩ := IH
    use 2*x*y+x+y
    calc
      a^(k+1) = a * a^k := by ring
      _ = (2*x+1) * a^k := by rw[hx]
      _ = (2*x+1) * (2*y+1) := by rw[hy]
      _ = 2 * (2 * x * y + x + y) + 1 := by ring



lemma help1 {n : ℕ} : ¬ Even n ↔ Odd n := by
  constructor
  . intro h1
    obtain h2|h2 := even_or_odd n
    . contradiction
    . apply h2
  . intro h1 h2
    obtain ⟨p,hp⟩ := h1
    obtain ⟨q,hq⟩ := h2
    have h3 : n ≡ 1 [ZMOD 2] := by
      use p
      rw[hp]
      field_simp
    have h4 : n ≡ 0 [ZMOD 2] := by
      use q
      rw[hq]
      field_simp
    have h5 :=
      calc
        1 ≡ n [ZMOD 2] := by rel[h3]
        _ ≡ 0 [ZMOD 2] := by rel[h4]
    numbers at h5



theorem Nat.even_of_pow_even' {a n : ℕ} (ha : Even (a ^ n)) : Even a := by
  obtain h|h := even_or_odd a
  . apply h
  . have h2 := Odd.pow h n
    have h3 := help1.mpr h2
    contradiction

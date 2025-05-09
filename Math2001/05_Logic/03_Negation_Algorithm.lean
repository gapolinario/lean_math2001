/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.Rel

math2001_init
set_option pp.funBinderTypes true


example (P Q : Prop) : ¬ (P ∧ Q) ↔ (¬ P ∨ ¬ Q) := by
  constructor
  · intro h
    by_cases hP : P
    · right
      intro hQ
      have hPQ : P ∧ Q
      · constructor
        · apply hP
        · apply hQ
      contradiction
    · left
      apply hP
  · intro h h2
    obtain ⟨hl,hr⟩ := h2
    obtain h|h := h
    . contradiction
    . contradiction


example :
    ¬(∀ m : ℤ, m ≠ 2 → ∃ n : ℤ, n ^ 2 = m) ↔ ∃ m : ℤ, m ≠ 2 ∧ ∀ n : ℤ, n ^ 2 ≠ m :=
  calc ¬(∀ m : ℤ, m ≠ 2 → ∃ n : ℤ, n ^ 2 = m)
      ↔ ∃ m : ℤ, ¬(m ≠ 2 → ∃ n : ℤ, n ^ 2 = m) := by rel [not_forall]
    _ ↔ ∃ m : ℤ, m ≠ 2 ∧ ¬(∃ n : ℤ, n ^ 2 = m) := by rel [not_imp]
    _ ↔ ∃ m : ℤ, m ≠ 2 ∧ ∀ n : ℤ, n ^ 2 ≠ m := by rel [not_exists]


example : ¬(∀ n : ℤ, ∃ m : ℤ, n ^ 2 < m ∧ m < (n + 1) ^ 2)
    ↔ ∃ n : ℤ, ∀ m : ℤ, n ^ 2 ≥ m ∨ m ≥ (n + 1) ^ 2 :=
  calc ¬(∀ n : ℤ, ∃ m : ℤ, n ^ 2 < m ∧ m < (n + 1) ^ 2)
    _ ↔ ∃ n:ℤ, ¬(∃ m:ℤ, n^2 < m ∧ m < (n+1)^2 ) := by rel[not_forall]
    _ ↔ ∃ n:ℤ, ∀ m:ℤ, ¬(n^2 < m ∧ m < (n+1)^2 ) := by rel[not_exists]
    _ ↔ ∃ n:ℤ, ∀ m:ℤ, ¬(n^2 < m) ∨ ¬(m < (n+1)^2 ) := by rel[not_and_or]
    _ ↔ ∃ n:ℤ, ∀ m:ℤ, n^2 ≥ m ∨ m ≥ (n + 1)^2 := by sorry

/-#push_neg ¬(∀ m : ℤ, m ≠ 2 → ∃ n : ℤ, n ^ 2 = m)
  -- ∃ m : ℤ, m ≠ 2 ∧ ∀ (n : ℤ), n ^ 2 ≠ m

#push_neg ¬(∀ n : ℤ, ∃ m : ℤ, n ^ 2 < m ∧ m < (n + 1) ^ 2)
  -- ∃ n : ℤ, ∀ m : ℤ, m ≤ n ^ 2 ∨ (n + 1) ^ 2 ≤ m


#push_neg ¬(∃ m n : ℤ, ∀ t : ℝ, m < t ∧ t < n)
#push_neg ¬(∀ a : ℕ, ∃ x y : ℕ, x * y ∣ a → x ∣ a ∧ y ∣ a)
#push_neg ¬(∀ m : ℤ, m ≠ 2 → ∃ n : ℤ, n ^ 2 = m)
-/

example : ¬ (∃ n : ℕ, n ^ 2 = 2) := by
  push_neg
  intro n
  have hn := le_or_succ_le n 1
  obtain hn | hn := hn
  · apply ne_of_lt
    calc
      n ^ 2 ≤ 1 ^ 2 := by rel [hn]
      _ < 2 := by numbers
  · apply ne_of_gt
    calc
      2 ≤ n := by rel[hn]
      _ < n+n := by addarith[hn]
      _ = 2*n := by ring
      _ ≤ n*n := by rel[hn]
      _ = n^2 := by ring


/-! # Exercises -/

-- the easy way
example (P : Prop) : ¬ (¬ P) ↔ P := by
  push_neg
  rfl

example (P : Prop) : ¬ (¬ P) ↔ P := by
  by_cases h : P
  . constructor
    . intro h2
      apply h
    . intro h
      intro h2
      contradiction
  . constructor
    . intro h2
      have h3 := h2 h
      contradiction
    . intro h2
      intro h3
      contradiction

-- no push_neg here
example (P Q : Prop) : ¬ (P → Q) ↔ (P ∧ ¬ Q) := by
  constructor
  . intro h
    constructor
    . dsimp[Not] at h
      by_cases hq : Q
      . sorry
      . sorry
    . dsimp[Not] at h
      intro hq
      sorry
  . intro h hn
    obtain ⟨h1,h2⟩ := h
    have := hn h1
    contradiction


example (P : α → Prop) : ¬ (∀ x, P x) ↔ ∃ x, ¬ P x := by
  constructor
  . intro h
    push_neg at h
    apply h
  . intro h
    push_neg
    apply h

example : (¬ ∀ a b : ℤ, a * b = 1 → a = 1 ∨ b = 1)
    ↔ ∃ a b : ℤ, a * b = 1 ∧ a ≠ 1 ∧ b ≠ 1 := by
  constructor
  . intro h
    push_neg at h
    apply h
  . intro h
    push_neg
    apply h


example : (¬ ∃ x : ℝ, ∀ y : ℝ, y ≤ x) ↔ (∀ x : ℝ, ∃ y : ℝ, y > x) := by
  constructor
  . intro h
    intro x
    --push_neg at h --works, but it's not needed
    use x+1
    extra
  . intro h
    push_neg
    intro x
    use x+1
    extra

example : ¬ (∃ m : ℤ, ∀ n : ℤ, m = n + 5) ↔ ∀ m : ℤ, ∃ n : ℤ, m ≠ n + 5 := by
  constructor
  . intro h
    push_neg at h
    apply h
  . intro h
    push_neg
    apply h

/-
#push_neg ¬(∀ n : ℕ, n > 0 → ∃ k l : ℕ, k < n ∧ l < n ∧ k ≠ l)
#push_neg ¬(∀ m : ℤ, m ≠ 2 → ∃ n : ℤ, n ^ 2 = m)
#push_neg ¬(∃ x : ℝ, ∀ y : ℝ, ∃ m : ℤ, x < y * m ∧ y * m < m)
#push_neg ¬(∃ x : ℝ, ∀ q : ℝ, q > x → ∃ m : ℕ, q ^ m > x)
-/

example : ¬ (∀ x : ℝ, x ^ 2 ≥ x) := by
  push_neg
  use 0.5
  numbers

example : ¬ (∃ t : ℝ, t ≤ 4 ∧ t ≥ 5) := by
  push_neg
  intro t
  have h := le_or_lt t 4
  obtain h|h := h
  . have h : t < 5 := by addarith[h]
    right
    apply h
  . left
    apply h

example : ¬ Int.Even 7 := by
  dsimp [Int.Even]
  push_neg
  intro k
  have h := le_or_lt k 3
  obtain h|h := h
  . apply ne_of_gt
    calc
      2*k ≤ 2*3 := by rel[h]
      _ < 7 := by numbers
  . apply ne_of_lt
    have h : 4 ≤ k := by addarith[h]
    calc
      7 < 2*4 := by numbers
      _ ≤ 2*k := by rel[h]

example {p : ℕ} (k : ℕ) (hk1 : k ≠ 1) (hkp : k ≠ p) (hk : k ∣ p) : ¬ Prime p := by
  dsimp [Prime]
  push_neg
  obtain h|h := le_or_lt 2 p
  . right
    use k
    constructor
    . apply hk
    . constructor
      . apply hk1
      . apply hkp
  . left
    apply h

example : ¬ ∃ a : ℤ, ∀ n : ℤ, 2 * a ^ 3 ≥ n * a + 7 := by
  push_neg
  intro a
  sorry

example {p : ℕ} (hp : ¬ Prime p) (hp2 : 2 ≤ p) : ∃ m, 2 ≤ m ∧ m < p ∧ m ∣ p := by
  have H : ¬ (∀ (m : ℕ), 2 ≤ m → m < p → ¬m ∣ p)
  · intro H
    sorry
  sorry

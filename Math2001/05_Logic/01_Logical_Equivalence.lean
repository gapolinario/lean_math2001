/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Library.Basic

math2001_init
set_option pp.funBinderTypes true

-- Anki
example {Q : Prop} (h1: ¬Q) (h2: Q) : P := by
  contradiction

example {P Q : Prop} (h1 : P ∨ Q) (h2 : ¬ Q) : P := by
  obtain hP | hQ := h1
  · apply hP
  · contradiction


example (P Q : Prop) : P → (P ∨ ¬ Q) := by
  intro hP
  left
  --apply hP
  exact hP --either of them works


#truth_table ¬(P ∧ ¬ Q)


example (P : Prop) : (P ∨ P) ↔ P := by
  constructor
  · intro h
    obtain h1 | h2 := h
    · apply h1
    · apply h2
  · intro h
    left
    apply h


example (P Q R : Prop) : (P ∧ (Q ∨ R)) ↔ ((P ∧ Q) ∨ (P ∧ R)) := by
  constructor
  · intro h
    obtain ⟨h1, h2 | h2⟩ := h
    · left
      constructor
      · apply h1
      · apply h2
    · right
      constructor
      · apply h1
      · apply h2
  · intro h
    obtain h|h := h
    obtain ⟨h1,h2⟩ := h
    constructor
    . apply h1
    . left
      apply h2
    obtain ⟨h1,h2⟩ := h
    constructor
    . apply h1
    . right
      apply h2

-- this also works, see below
example (P Q R : Prop) : (P ∧ (Q ∨ R)) ↔ ((P ∧ Q) ∨ (P ∧ R)) := by
  constructor
  · intro h
    obtain ⟨h1, h2 | h2⟩ := h
    · left
      constructor
      · apply h1
      · apply h2
    · right
      constructor
      · apply h1
      · apply h2
  · intro h
    -- all at once, here
    obtain ⟨h1,h2⟩|⟨h1,h2⟩ := h
    constructor
    . apply h1
    . left
      apply h2
    constructor
    . apply h1
    . right
      apply h2


#truth_table P ∧ (Q ∨ R)
#truth_table (P ∧ Q) ∨ (P ∧ R)


example {P Q : α → Prop} (h1 : ∀ x : α, P x) (h2 : ∀ x : α, Q x) :
    ∀ x : α, P x ∧ Q x := by
  intro x
  constructor
  · apply h1
  · apply h2


example {P : α → β → Prop} (h : ∃ x : α, ∀ y : β, P x y) :
    ∀ y : β, ∃ x : α, P x y := by
  obtain ⟨x, hx⟩ := h
  intro y
  use x
  apply hx


example (P : α → Prop) : ¬ (∃ x, P x) ↔ ∀ x, ¬ P x := by
  constructor
  · intro h a ha
    have : ∃ x, P x
    · use a
      apply ha
    contradiction
  · intro h h'
    obtain ⟨x, hx⟩ := h'
    have : ¬ P x := h x
    contradiction

/-! # Exercises -/


example {P Q : Prop} (h : P ∧ Q) : P ∨ Q := by
  obtain ⟨h1,h2⟩ := h
  left
  apply h1

example {P Q R : Prop} (h1 : P → Q) (h2 : P → R) (h3 : P) : Q ∧ R := by
  constructor
  apply h1
  apply h3
  apply h2
  apply h3


example (P : Prop) : ¬(P ∧ ¬ P) := by
  --apply not_and_or.mpr
  sorry

example {P Q : Prop} (h1 : P ↔ ¬ Q) (h2 : Q) : ¬ P := by
  sorry

example {P Q : Prop} (h1 : P ∨ Q) (h2 : Q → P) : P := by
  obtain h1|h1 := h1
  apply h1
  apply h2
  apply h1

example {P Q R : Prop} (h : P ↔ Q) : (P ∧ R) ↔ (Q ∧ R) := by
  constructor
  . intro h2
    obtain ⟨hP,hR⟩ := h2
    constructor
    . apply h.mp
      apply hP
    . apply hR
  . intro h2
    obtain ⟨hQ,hR⟩ := h2
    constructor
    . apply h.mpr
      apply hQ
    . apply hR


example (P : Prop) : (P ∧ P) ↔ P := by
  constructor
  . intro h
    obtain ⟨h,h⟩ := h
    apply h
  . intro h
    constructor
    . apply h
    . apply h



example (P Q : Prop) : (P ∨ Q) ↔ (Q ∨ P) := by
  constructor
  . intro h
    obtain h|h := h
    right
    apply h
    left
    apply h
  . intro h
    obtain h|h := h
    right
    apply h
    left
    apply h


example (P Q : Prop) : ¬(P ∨ Q) ↔ (¬P ∧ ¬Q) := by
  constructor
  intro h
  have h' : P ∨ Q → False := by apply h
  constructor
  intro R
  sorry
  sorry
  intro h h'
  obtain ⟨h1,h2⟩ := h
  obtain h'|h' := h'
  contradiction
  contradiction


example {P Q : α → Prop} (h1 : ∀ x, P x → Q x) (h2 : ∀ x, P x) : ∀ x, Q x := by
  sorry

example {P Q : α → Prop} (h : ∀ x, P x ↔ Q x) : (∃ x, P x) ↔ (∃ x, Q x) := by
  sorry

example (P : α → β → Prop) : (∃ x y, P x y) ↔ ∃ y x, P x y := by
  sorry

example (P : α → β → Prop) : (∀ x y, P x y) ↔ ∀ y x, P x y := by
  sorry

example (P : α → Prop) (Q : Prop) : ((∃ x, P x) ∧ Q) ↔ ∃ x, (P x ∧ Q) := by
  sorry

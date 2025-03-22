/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Theory.ParityModular
import Library.Basic
import Library.Tactic.ModEq

math2001_init

open Int


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

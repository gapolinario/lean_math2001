import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.GCongr

open Int

-- no indentation
example : ¬ (∃ n : ℕ, n ^ 2 = 2) := by
  intro h
  obtain ⟨n,hn⟩ := h
  obtain h|h : n ≤ 1 ∨ 2 ≤ n := by omega
  have h2 :=
    calc
      2 = n^2 := by rw[hn]
      _  ≤ 1^2 := by gcongr
  norm_num at h2
  have h2 :=
    calc
      2 = n^2 := by rw[hn]
      _ ≥ 2^2 := by gcongr
      _ ≥ 4 := by norm_num
  norm_num at h2

-- with indentation
example : ¬ (∃ n : ℕ, n ^ 2 = 2) := by
  intro h
  obtain ⟨n,hn⟩ := h
  obtain h|h : n ≤ 1 ∨ 2 ≤ n := by omega
  . have h2 :=
      calc
        2 = n^2 := by rw[hn]
        _  ≤ 1^2 := by gcongr
    norm_num at h2
  . have h2 :=
      calc
        2 = n^2 := by rw[hn]
        _ ≥ 2^2 := by gcongr
    norm_num at h2

/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Library.Basic

math2001_init

open Int

-- This was generated by ChatGPT
-- It took 6 tries to get problem and solutions right
-- sending the error messages to ChatGPT
-- After some time, the chat decided to do the algebra
-- first, and then write the lean code, and this generated
-- better results

example {x y : ℤ} (hx : Odd x) (hy : Even y) : Odd (x ^ 2 + 4 * y) := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  use 2 * a ^ 2 + 2 * a + 4 * b  -- Corrected witness
  rw [ha, hb]
  ring

example (n : ℤ) : Even (5 * n ^ 2 + 7 * n + 6) := by
  obtain hn | hn := Int.even_or_odd n
  · obtain ⟨x, hx⟩ := hn
    use 10 * x ^ 2 + 7 * x + 3  -- Fixed witness
    rw [hx]
    ring
  · obtain ⟨x, hx⟩ := hn
    use 10 * x ^ 2 + 17 * x + 9  -- This part was already correct
    rw [hx]
    ring

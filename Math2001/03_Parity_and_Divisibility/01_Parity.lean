/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Library.Basic

math2001_init

open Int


example : Odd (7 : ℤ) := by
  dsimp [Odd]
  use 3
  numbers


example : Odd (-3 : ℤ) := by
  use -2
  numbers

example {n : ℤ} (hn : Odd n) : Odd (3 * n + 2) := by
  dsimp [Odd] at *
  obtain ⟨k, hk⟩ := hn
  use 3 * k + 2
  rw [hk]
  ring


example {n : ℤ} (hn : Odd n) : Odd (7 * n - 4) := by
  dsimp [Odd] at *
  obtain ⟨k,hk⟩ := hn
  use 7*k+1
  rw[hk]
  ring

example {x y : ℤ} (hx : Odd x) (hy : Odd y) : Odd (x + y + 1) := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  use a + b + 1
  rw [ha, hb]
  ring


example {x y : ℤ} (hx : Odd x) (hy : Odd y) : Odd (x * y + 2 * y) := by
  dsimp [Odd] at *
  obtain ⟨a,ha⟩ := hx
  obtain ⟨b,hb⟩ := hy
  use 2*a*b+a+3*b+1
  rw[ha]
  rw[hb]
  ring

example {m : ℤ} (hm : Odd m) : Even (3 * m - 5) := by
  --dsimp [Odd,Even] at *
  obtain ⟨a,ha⟩ := hm
  use 3*a-1
  rw[ha]
  ring

example {n : ℤ} (hn : Even n) : Odd (n ^ 2 + 2 * n - 5) := by
  obtain ⟨a,ha⟩ := hn
  use 2*a^2+2*a-3
  rw[ha]
  ring


example (n : ℤ) : Even (n ^ 2 + n + 4) := by
  obtain hn | hn := Int.even_or_odd n
  · obtain ⟨x, hx⟩ := hn
    use 2 * x ^ 2 + x + 2
    calc
      n ^ 2 + n + 4 = (2 * x) ^ 2 + 2 * x + 4 := by rw [hx]
      _ = 2 * (2 * x ^ 2 + x + 2) := by ring
  · obtain ⟨x, hx⟩ := hn
    use 2 * x ^ 2 + 3 * x + 3
    calc
      n ^ 2 + n + 4 = (2 * x + 1) ^ 2 + (2 * x + 1) + 4 := by rw [hx]
      _ = 2 * (2 * x ^ 2 + 3 * x + 3) := by ring

/-! # Exercises -/


example : Odd (-9 : ℤ) := by
  use -5
  ring

example : Even (26 : ℤ) := by
  use 13
  ring

example {m n : ℤ} (hm : Odd m) (hn : Even n) : Odd (n + m) := by
  obtain ⟨a,ha⟩ := hm
  obtain ⟨b,hb⟩ := hn
  use a+b
  rw[ha,hb]
  ring

example {p q : ℤ} (hp : Odd p) (hq : Even q) : Odd (p - q - 4) := by
  obtain ⟨a,ha⟩ := hp
  obtain ⟨b,hb⟩ := hq
  use a-b-2
  rw[ha,hb]
  ring

example {a b : ℤ} (ha : Even a) (hb : Odd b) : Even (3 * a + b - 3) := by
  obtain ⟨x,hx⟩ := ha
  obtain ⟨y,hy⟩ := hb
  use 3*x+y-1
  rw[hx,hy]
  ring

example {r s : ℤ} (hr : Odd r) (hs : Odd s) : Even (3 * r - 5 * s) := by
  obtain ⟨x,hx⟩ := hr
  obtain ⟨y,hy⟩ := hs
  use 3*x-5*y-1
  rw[hx,hy]
  ring

example {x : ℤ} (hx : Odd x) : Odd (x ^ 3) := by
  have ⟨a,ha⟩ := hx
  use 3*a + 6*a^2 + 4*a^3
  rw[ha]
  ring

example {n : ℤ} (hn : Odd n) : Even (n ^ 2 - 3 * n + 2) := by
  have ⟨a,ha⟩ := hn
  use 2*a^2-a
  rw[ha]
  ring

example {a : ℤ} (ha : Odd a) : Odd (a ^ 2 + 2 * a - 4) := by
  obtain ⟨x,hx⟩ := ha
  use 2*x^2+4*x-1
  rw[hx]
  ring

example {p : ℤ} (hp : Odd p) : Odd (p ^ 2 + 3 * p - 5) := by
  obtain ⟨x,hx⟩ := hp
  use 2*x^2+5*x-1
  rw[hx]
  ring

example {x y : ℤ} (hx : Odd x) (hy : Odd y) : Odd (x * y) := by
  obtain ⟨a,ha⟩ := hx
  obtain ⟨b,hb⟩ := hy
  use 2*a*b+a+b
  rw[ha,hb]
  ring

example (n : ℤ) : Odd (3 * n ^ 2 + 3 * n - 1) := by
  sorry

example (n : ℤ) : ∃ m ≥ n, Odd m := by
  sorry
example (a b c : ℤ) : Even (a - b) ∨ Even (a + c) ∨ Even (b - c) := by
  sorry

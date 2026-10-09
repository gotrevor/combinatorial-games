/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
module

public import CombinatorialGames.Game.Temperature
public import CombinatorialGames.Surreal.Birthday.Dyadic

/-!
# Cooling

The game `x` cooled by `t ≥ -1` (Siegel, *Combinatorial Game Theory*, §II.5) taxes every move of
`x` by `t`, until `x` freezes at its mean. Siegel defines it by recursion: if `x` equals an integer
it's unchanged, and otherwise it's `!{(cool · t - t) '' xᴸ | (cool · t + t) '' xᴿ}`, unless this
game is infinitely close to a number for some `t' < t`, in which case it's that number for the least
such `t'`.

Since we already have walls, temperature and mean, we instead define `x` cooled by `t` as its mean
once `t` exceeds its temperature, and recurse otherwise. We then show that this agrees with Siegel's
definition, and that the walls of `x` are the stops of `x` cooled by `t`. Since cooling respects
equality, so do walls, temperature and mean.

At its temperature `x` hasn't frozen yet: `⋆` cooled by `0` is `⋆`, and `±1` cooled by `1` is `⋆`.

Cooling by `-1` does not respect equality: `!{{⋆, 1} | {0}} ≈ !{{1} | {0}}`, but cooled by `-1`
these differ by a nonzero infinitesimal, since the dominated option `⋆` heats up to `±1`. The walls
still agree at `-1`, where the right wall is the greatest integer below `x`.
-/

public noncomputable section

open Player Trajectory

universe u

namespace IGame

variable {x y : IGame} [Short x] [Short y] {t : 𝔻≥-1}

/-! ### Stops -/

theorem rightStop_neg (x : IGame) [Short x] : rightStop (-x) = -leftStop x :=
  sorry

theorem leftStop_neg (x : IGame) [Short x] : leftStop (-x) = -rightStop x :=
  sorry

/-- A short game is infinitely close to a number iff its stops agree. -/
theorem leftStop_eq_rightStop_iff : leftStop x = rightStop x ↔
    ∃ a : Dyadic, ∀ ε : Dyadic, 0 < ε → ((a - ε : Dyadic) : IGame) < x ∧ x < (a + ε : Dyadic) :=
  sorry

/-! ### Cooling -/

/-- The game `x` cooled by `t`. This is the mean of `x` if `t` exceeds its temperature, or if `x`
equals an integer, and `!{(cool · t - t) '' xᴸ | (cool · t + t) '' xᴿ}` otherwise. -/
def cool (x : IGame) [Short x] (t : 𝔻≥-1) : IGame :=
  if ⊥ < temperature x ∧ t ≤ temperature x then
    !{.range fun y : xᴸ ↦ have := Short.of_mem_moves y.2; cool y t - (t : Dyadic) |
      .range fun y : xᴿ ↦ have := Short.of_mem_moves y.2; cool y t + (t : Dyadic)}
  else mean x
termination_by x
decreasing_by igame_wf

/-- The game `!{(cool · t - t) '' xᴸ | (cool · t + t) '' xᴿ}`, which is `x` cooled by `t` unless
`x` has frozen. -/
def tax (x : IGame) [Short x] (t : 𝔻≥-1) : IGame :=
  !{.range fun y : xᴸ ↦ have := Short.of_mem_moves y.2; cool y t - (t : Dyadic) |
    .range fun y : xᴿ ↦ have := Short.of_mem_moves y.2; cool y t + (t : Dyadic)}

instance Short.cool (x : IGame) [Short x] (t : 𝔻≥-1) : Short (cool x t) :=
  sorry

instance Short.tax (x : IGame) [Short x] (t : 𝔻≥-1) : Short (tax x t) :=
  sorry

theorem cool_of_le_temperature (h : ∀ n : ℤ, ¬ x ≈ n) (ht : t ≤ temperature x) :
    cool x t = tax x t :=
  sorry

theorem cool_of_temperature_lt (ht : temperature x < t) : cool x t = mean x :=
  sorry

theorem cool_of_equiv {n : ℤ} (h : x ≈ n) (t : 𝔻≥-1) : cool x t = n :=
  sorry

@[simp] theorem cool_intCast (n : ℤ) (t : 𝔻≥-1) : cool n t = n := cool_of_equiv .rfl t
@[simp] theorem cool_natCast (n : ℕ) (t : 𝔻≥-1) : cool n t = n := by simpa using cool_intCast n t
@[simp] theorem cool_zero (t : 𝔻≥-1) : cool 0 t = 0 := by simpa using cool_natCast 0 t
@[simp] theorem cool_one (t : 𝔻≥-1) : cool 1 t = 1 := by simpa using cool_natCast 1 t

theorem cool_neg (x : IGame) [Short x] (t : 𝔻≥-1) : cool (-x) t = -cool x t :=
  sorry

/-! ### Walls are stops -/

theorem rightStop_cool (x : IGame) [Short x] (t : 𝔻≥-1) : rightStop (cool x t) = wall right x t :=
  sorry

theorem leftStop_cool (x : IGame) [Short x] (t : 𝔻≥-1) : leftStop (cool x t) = -wall left x t :=
  sorry

/-! ### Siegel's definition -/

/-- The game `tax x t` is infinitely close to a number exactly from the temperature of `x` onwards.
Together with `rightStop_tax_temperature`, this says that `cool` agrees with Siegel's definition. -/
theorem leftStop_tax_eq_rightStop_tax_iff (h : ∀ n : ℤ, ¬ x ≈ n) :
    leftStop (tax x t) = rightStop (tax x t) ↔ temperature x ≤ t :=
  sorry

theorem rightStop_tax_temperature (h : ∀ n : ℤ, ¬ x ≈ n) :
    rightStop (tax x (temperature x)) = mean x :=
  sorry

/-! ### Cooling respects equality -/

theorem cool_add (ht : ⊥ < t) (x y : IGame) [Short x] [Short y] :
    cool (x + y) t ≈ cool x t + cool y t :=
  sorry

theorem cool_congr (ht : ⊥ < t) (h : x ≈ y) : cool x t ≈ cool y t :=
  sorry

theorem cool_le_cool (ht : ⊥ < t) (h : x ≤ y) : cool x t ≤ cool y t :=
  sorry

theorem wall_congr (h : x ≈ y) (p : Player) : wall p x = wall p y :=
  sorry

theorem temperature_congr (h : x ≈ y) : temperature x = temperature y :=
  eq_of_forall_ge_iff fun t ↦ by
    rw [temperature_le_iff, temperature_le_iff, wall_congr h, wall_congr h]

theorem mean_congr (h : x ≈ y) : mean x = mean y := by
  have H (z : IGame) [Short z] : wall right z (temperature z) = mean z :=
    wall_apply_of_temperature_le le_rfl
  rw [← H, ← H, wall_congr h, temperature_congr h]

theorem mean_add (x y : IGame) [Short x] [Short y] : mean (x + y) = mean x + mean y :=
  sorry

/-! ### Examples -/

example : cool ⋆ ⟨0, by decide⟩ = ⋆ :=
  sorry

example (ht : (0 : Dyadic) < t) : cool ⋆ t ≈ 0 :=
  sorry

example (ht : (0 : Dyadic) < t) : cool ↑ t ≈ 0 :=
  sorry

example : cool (±1) ⟨.half, by decide⟩ ≈ ±½ :=
  sorry

example : cool (±1) ⟨1, by decide⟩ ≈ ⋆ :=
  sorry

private instance : Short !{{2} | {0}} := by
  rw [short_def]; simpa using Short.ofNat 2

example : cool !{{2} | {0}} ⟨1, by decide⟩ ≈ 1 + ⋆ :=
  sorry

example (ht : (1 : Dyadic) < t) : cool !{{2} | {0}} t ≈ 1 :=
  sorry

private instance : Short !{{⋆, 1} | {0}} := by
  rw [short_def]; simp

private instance : Short !{{1} | {0}} := by
  rw [short_def]; simp

-- Cooling by `-1` does not respect equality.
example : !{{⋆, 1} | {0}} ≈ !{{1} | {0}} ∧ ¬ cool !{{⋆, 1} | {0}} ⊥ ≈ cool !{{1} | {0}} ⊥ :=
  sorry

end IGame

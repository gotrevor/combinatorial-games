/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
module

public import CombinatorialGames.Game.Special
public import CombinatorialGames.Game.Trajectory

/-!
# Temperature

The left and right walls of a short game `x` (Siegel, *Combinatorial Game Theory*, pp. 106-107) are
the left and right stops of `x` cooled by `t`, as functions of `t ≥ -1`. We instead define them
directly, by mutual recursion with the scaffolds:

* the right scaffold of `x` is the minimum of `t ↦ L(xᴿ, t) + t` over the right options `xᴿ`, and
  the left scaffold is the maximum of `t ↦ R(xᴸ, t) - t` over the left options `xᴸ`;
* the temperature of `x` is the least `t` at which the left scaffold meets the right scaffold, and
  the mean of `x` is their common value there;
* the walls of `x` agree with its scaffolds up to its temperature, and are constant afterwards.

Following Siegel, a game equal to an integer `n` is not cooled: both its walls are the constant `n`,
and its temperature is `-1`.

## Implementation notes

The right wall has slopes `0` and `1`, while the left wall has slopes `0` and `-1`. To use a single
type, `Trajectory`, we represent the left wall of `x` by the right wall of `-x`, its negation. Thus
`wall right x` is the right wall of `x`, and `wall left x` is the right wall of `-x`. The scaffolds
are then minima of reflections `t ↦ t - wall (-p) y t` of walls of options `y`, so that the
recursion only involves options of `x`.

Every short game without left or right options equals an integer, but so do forms such as
`!{{-2} | {2}}`, whose scaffolds meet at `-1` with values `1` and `-1`, rather than `0`. We
therefore case on whether `x` equals an integer, which makes these definitions noncomputable.
-/

public noncomputable section

open Player Trajectory

namespace IGame

/-- A short game which isn't equal to any integer has both left and right options. -/
theorem nonempty_moves_of_forall_not_equiv {x : IGame} [Short x] (h : ∀ n : ℤ, ¬ x ≈ n)
    (p : Player) : (x.moves p).Nonempty :=
  sorry

open Classical in
mutual

/-- The scaffold of `x` for player `p`, as the minimum over the options `y ∈ x.moves p` of the
reflected walls `t ↦ t - wall (-p) y t`.

`scaffold right x` is the right scaffold of `x`, and `scaffold left x` is the negation of the left
scaffold of `x`. This is a junk value if `x` has no options for `p`. -/
def scaffold (p : Player) (x : IGame) [Short x] : Trajectory :=
  have := Fintype.ofFinite (x.moves p)
  if h : (x.moves p).Nonempty then
    Finset.univ.inf' (Finset.univ_nonempty_iff.2 h.to_subtype) fun y ↦
      have := Short.of_mem_moves y.2
      reflect (wall (-p) y)
  else const 0
termination_by (x, 0)
decreasing_by igame_wf

/-- The walls of `x`. `wall right x` is the right wall of `x`, and `wall left x` is the right wall
of `-x`, i.e. the negation of the left wall of `x`.

If `x` equals an integer `n`, these are the constants `n` and `-n`. Otherwise, they follow the
scaffolds of `x` until these meet, and are constant afterwards. -/
def wall (p : Player) (x : IGame) [Short x] : Trajectory :=
  if h : ∃ n : ℤ, x ≈ n then const (p.cases (-h.choose) h.choose) else
    (scaffold p x).freeze (crossing (scaffold left x) (scaffold right x))
termination_by (x, 1)
decreasing_by all_goals exact .right _ one_pos

end

variable {x y : IGame} [Short x] [Short y] {p : Player} {t : 𝔻≥-1}

theorem le_scaffold_iff {f : Trajectory} (h : (x.moves p).Nonempty) : f ≤ scaffold p x ↔
    ∀ y ∈ x.moves p, ∀ [Short y], f ≤ reflect (wall (-p) y) :=
  sorry

theorem wall_of_equiv {n : ℤ} (h : x ≈ n) : wall p x = const (p.cases (-n) n) :=
  sorry

theorem wall_of_forall_not_equiv (h : ∀ n : ℤ, ¬ x ≈ n) :
    wall p x = (scaffold p x).freeze (crossing (scaffold left x) (scaffold right x)) :=
  sorry

theorem scaffold_neg (p : Player) (x : IGame) [Short x] : scaffold p (-x) = scaffold (-p) x :=
  sorry

theorem wall_neg (p : Player) (x : IGame) [Short x] : wall p (-x) = wall (-p) x :=
  sorry

/-! ### Temperature and mean -/

/-- The walls of a short game eventually meet. -/
theorem crossing_wall_ne_top (x : IGame) [Short x] : crossing (wall left x) (wall right x) ≠ ⊤ :=
  sorry

/-- The temperature of `x` is the least `t ≥ -1` at which its walls meet. -/
def temperature (x : IGame) [Short x] : 𝔻≥-1 :=
  (crossing (wall left x) (wall right x)).untop (crossing_wall_ne_top x)

/-- The mean value of `x`, i.e. the common value of its walls at and above its temperature. -/
def mean (x : IGame) [Short x] : Dyadic :=
  wall right x (temperature x)

theorem temperature_le_iff : temperature x ≤ t ↔ 0 ≤ wall left x t + wall right x t := by
  rw [temperature, ← WithTop.coe_le_coe, WithTop.coe_untop, crossing_le_iff]

theorem wall_apply_of_temperature_le (ht : temperature x ≤ t) :
    wall p x t = p.cases (-mean x) (mean x) :=
  sorry

theorem wall_apply_of_le_temperature (h : ∀ n : ℤ, ¬ x ≈ n) (ht : t ≤ temperature x) :
    wall p x t = scaffold p x t :=
  sorry

/-- For a game not equal to an integer, the temperature is where the scaffolds meet. -/
theorem temperature_of_forall_not_equiv (h : ∀ n : ℤ, ¬ x ≈ n) :
    temperature x = crossing (scaffold left x) (scaffold right x) :=
  sorry

theorem temperature_eq_bot_iff : temperature x = ⊥ ↔ ∃ n : ℤ, x ≈ n :=
  sorry

theorem temperature_neg (x : IGame) [Short x] : temperature (-x) = temperature x :=
  sorry

theorem mean_neg (x : IGame) [Short x] : mean (-x) = -mean x :=
  sorry

/-- Walls only depend on the value of a game. -/
theorem wall_congr (h : x ≈ y) : wall p x = wall p y :=
  sorry

theorem temperature_congr (h : x ≈ y) : temperature x = temperature y := by
  simp_rw [temperature, wall_congr h]

theorem mean_congr (h : x ≈ y) : mean x = mean y := by
  rw [mean, mean, wall_congr h, temperature_congr h]

/-! ### Examples -/

theorem temperature_intCast (n : ℤ) : temperature n = ⊥ :=
  temperature_eq_bot_iff.2 ⟨n, .rfl⟩

theorem mean_intCast (n : ℤ) : mean n = n :=
  sorry

theorem temperature_star : (temperature ⋆ : Dyadic) = 0 :=
  sorry

theorem mean_star : mean ⋆ = 0 :=
  sorry

theorem temperature_up : (temperature ↑ : Dyadic) = 0 :=
  sorry

theorem mean_up : mean ↑ = 0 :=
  sorry

theorem temperature_half : (temperature ½ : Dyadic) = -.half :=
  sorry

theorem mean_half : mean ½ = .half :=
  sorry

theorem temperature_switch_one : (temperature (±1) : Dyadic) = 1 :=
  sorry

theorem mean_switch_one : mean (±1) = 0 :=
  sorry

example [Short !{{2} | {0}}] : (temperature !{{2} | {0}} : Dyadic) = 1 :=
  sorry

example [Short !{{2} | {0}}] : mean !{{2} | {0}} = 1 :=
  sorry

end IGame

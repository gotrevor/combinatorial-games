/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
module

public import CombinatorialGames.Game.Classes
public import CombinatorialGames.Game.Trajectory

import CombinatorialGames.Surreal.Basic
import CombinatorialGames.Tactic.GameCmp
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.Finite
import Mathlib.Tactic.IntervalCases

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

## Todo

Define cooling, show that the walls of `x` are the stops of `x` cooled by `t`, and deduce that
walls, temperature and mean only depend on the value of `x`:

* `wall_congr (h : x ≈ y) : wall p x = wall p y`
* `temperature_congr (h : x ≈ y) : temperature x = temperature y`
* `mean_congr (h : x ≈ y) : mean x = mean y`
-/

public noncomputable section

open Filter Player Trajectory

universe u

namespace IGame

private theorem intCast_le_of_forall_lf {x : IGame} (h : ∀ m : ℤ, ¬ x ≈ m) {n : ℤ}
    (hn : ∀ y ∈ xᴿ, n ⧏ y) : n ≤ x := by
  refine le_iff_forall_lf.2 ⟨fun z hz hxz ↦ ?_, hn⟩
  by_cases! hf : ∀ y ∈ xᴸ, y ⧏ n
  · obtain ⟨m, hm⟩ := Fits.exists_intCast_equiv ⟨hf, hn⟩
    exact h m hm
  · obtain ⟨y, hy, hny⟩ := hf
    exact left_lf hy (hxz.trans ((Numeric.left_lt hz).le.trans hny))

/-- A short game which isn't equal to any integer has both left and right options. -/
theorem nonempty_moves_of_forall_not_equiv {x : IGame} [Short x] (h : ∀ n : ℤ, ¬ x ≈ n)
    (p : Player) : (x.moves p).Nonempty := by
  suffices ∀ x [Short x], (∀ n : ℤ, ¬ x ≈ n) → xᴿ.Nonempty by
    cases p
    · simpa using this (-x) fun n hn ↦ h (-n) (by simpa using neg_equiv.1 hn)
    · exact this x h
  intro x _ h
  by_contra! hx
  obtain ⟨n, hn⟩ := Short.exists_lt_natCast x
  exact hn.not_ge (by simpa using intCast_le_of_forall_lf h (n := n) (by simp [hx]))

/-! ### Walls and scaffolds -/

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

theorem scaffold_apply_le (hy : y ∈ x.moves p) (t : 𝔻≥-1) :
    scaffold p x t ≤ t - wall (-p) y t := by
  let := Fintype.ofFinite (x.moves p)
  rw [scaffold, dite_eq_left ⟨y, hy⟩, inf'_apply]
  exact Finset.inf'_le _ (Finset.mem_univ (⟨y, hy⟩ : x.moves p))

theorem exists_scaffold_apply_eq (h : (x.moves p).Nonempty) (t : 𝔻≥-1) :
    ∃ y ∈ x.moves p, ∃ _ : Short y, scaffold p x t = t - wall (-p) y t := by
  let := Fintype.ofFinite (x.moves p)
  rw [scaffold, dite_eq_left h, inf'_apply]
  obtain ⟨⟨y, hy⟩, -, e⟩ := Finset.exists_mem_eq_inf' (Finset.univ_nonempty_iff.2 h.to_subtype)
    fun y : x.moves p ↦ have := Short.of_mem_moves y.2; (t : Dyadic) - wall (-p) y t
  exact ⟨y, hy, .of_mem_moves hy, e⟩

theorem scaffold_of_moves_eq_singleton (h : x.moves p = {y}) :
    scaffold p x = reflect (wall (-p) y) := by
  refine Trajectory.ext fun t ↦ ?_
  obtain ⟨z, hz, _, e⟩ := exists_scaffold_apply_eq (h ▸ Set.singleton_nonempty y) t
  obtain rfl : z = y := by simpa [h] using hz
  exact e

theorem wall_of_equiv {n : ℤ} (h : x ≈ n) : wall p x = const (p.cases (-n) n) := by
  have h' : ∃ n : ℤ, x ≈ n := ⟨n, h⟩
  rw [wall, dite_eq_left h', intCast_equiv.1 (h'.choose_spec.symm.trans h)]

theorem wall_intCast (p : Player) (n : ℤ) : wall p n = const (p.cases (-n) n) :=
  wall_of_equiv .rfl

theorem wall_of_forall_not_equiv (h : ∀ n : ℤ, ¬ x ≈ n) :
    wall p x = (scaffold p x).freeze (crossing (scaffold left x) (scaffold right x)) := by
  rw [wall, dite_eq_right (not_exists.2 h)]

private theorem scaffold_neg_aux (H : ∀ y ∈ x.moves (-p), ∀ [Short y], wall (-p) (-y) = wall p y) :
    scaffold p (-x) = scaffold (-p) x := by
  by_cases h : (x.moves (-p)).Nonempty
  · refine Trajectory.ext fun t ↦ le_antisymm ?_ ?_
    · obtain ⟨y, hy, _, e⟩ := exists_scaffold_apply_eq h t
      rw [e, neg_neg, ← H y hy]
      exact scaffold_apply_le (by simpa) t
    · obtain ⟨y, hy, _, e⟩ := exists_scaffold_apply_eq (p := p) (x := -x) (by simpa) t
      simpa [e, ← H (-y) (by simpa using hy)] using
        scaffold_apply_le (p := -p) (y := -y) (by simpa using hy) t
  · rw [scaffold, scaffold, dite_eq_right (by simpa), dite_eq_right h]

theorem wall_neg (p : Player) (x : IGame) [Short x] : wall p (-x) = wall (-p) x := by
  induction x using moveRecOn generalizing ‹x.Short› p with | ind x ih
  by_cases! h : ∃ n : ℤ, x ≈ n
  · obtain ⟨n, hn⟩ := h
    rw [wall_of_equiv hn, wall_of_equiv (n := -n) (by simpa using neg_congr hn)]
    cases p <;> simp
  · have h' (n : ℤ) : ¬ -x ≈ n := fun hn ↦ h (-n) (by simpa using neg_equiv.1 hn)
    have hs (q) : scaffold q (-x) = scaffold (-q) x :=
      scaffold_neg_aux fun y hy _ ↦ by simpa using ih _ y hy (-q)
    rw [wall_of_forall_not_equiv h, wall_of_forall_not_equiv h', hs, hs, hs, crossing_comm]
    rfl

theorem scaffold_neg (p : Player) (x : IGame) [Short x] : scaffold p (-x) = scaffold (-p) x :=
  scaffold_neg_aux fun _ _ _ ↦ by simpa using wall_neg (-p) _

/-! ### Temperature and mean -/

/-- At `t = -1`, the right wall of `x` is the greatest integer `n ≤ x`. -/
private theorem wall_right_bot (x : IGame) [Short x] :
    ∃ k : ℤ, wall right x ⊥ = k ∧ ∀ n : ℤ, n ≤ k ↔ n ≤ x := by
  by_cases! h : ∃ n : ℤ, x ≈ n
  · obtain ⟨m, hm⟩ := h
    exact ⟨m, by simp [wall_of_equiv hm], fun n ↦ by simp [hm.le_congr_right]⟩
  have H (y) (hy : y ∈ xᴿ) [Short y] :
      ∃ k : ℤ, -1 - wall left y ⊥ = k ∧ ∀ n : ℤ, n ≤ k ↔ n ⧏ y := by
    obtain ⟨k, hk, hk'⟩ := wall_right_bot (-y)
    refine ⟨-1 - k, by rw [← neg_right, ← wall_neg, hk]; push_cast; rfl, fun n ↦ ?_⟩
    rw [← IGame.neg_le_neg_iff, ← intCast_neg, ← hk']
    omega
  obtain ⟨y, hy, _, e⟩ := exists_scaffold_apply_eq (nonempty_moves_of_forall_not_equiv h right) ⊥
  obtain ⟨k, hk, hk'⟩ := H y hy
  refine ⟨k, by rw [wall_of_forall_not_equiv h, freeze_apply_bot, e, ← hk]; rfl,
    fun n ↦ ⟨fun hn ↦ intCast_le_of_forall_lf h fun z hz ↦ ?_, fun hn ↦ ?_⟩⟩
  · have := Short.of_mem_moves hz
    obtain ⟨l, hl, hl'⟩ := H z hz
    have := (e.symm.trans_le (scaffold_apply_le hz ⊥)).trans_eq hl
    exact (hl' n).1 (hn.trans (Int.cast_le.1 (hk ▸ this)))
  · exact (hk' n).2 fun h ↦ lf_right hy (h.trans hn)
termination_by x.birthday
decreasing_by exact (birthday_neg y).trans_lt (birthday_lt_of_mem_moves hy)

/-- At `t = -1`, the walls of a game which isn't equal to an integer haven't met yet. -/
private theorem wall_bot_add_neg (h : ∀ n : ℤ, ¬ x ≈ n) : wall left x ⊥ + wall right x ⊥ < 0 := by
  obtain ⟨k, hk, hk'⟩ := wall_right_bot x
  obtain ⟨l, hl, hl'⟩ := wall_right_bot (-x)
  rw [wall_neg, neg_right] at hl
  rw [hl, hk]
  by_contra! hs
  have : 0 ≤ l + k := by exact_mod_cast hs
  exact h k ⟨by simpa using (hl' (-k)).1 (by omega), (hk' k).1 le_rfl⟩

private theorem crossing_scaffold_ne_top_aux (h : ∀ n : ℤ, ¬ x ≈ n)
    (H : ∀ p, ∀ y ∈ x.moves p, ∀ [Short y], ∀ᶠ C in atTop, ∀ t, wall (-p) y t ≤ C) :
    crossing (scaffold left x) (scaffold right x) ≠ ⊤ := by
  have := fun p (y : x.moves p) ↦ Short.of_mem_moves y.2
  obtain ⟨M, hM, hC⟩ := ((eventually_ge_atTop (-1 : Dyadic)).and <|
    eventually_all.2 fun p ↦ eventually_all.2 fun y : x.moves p ↦ H p y y.2).exists
  have hS (p) : 0 ≤ scaffold p x ⟨M, hM⟩ := by
    obtain ⟨y, hy, _, e⟩ := exists_scaffold_apply_eq (nonempty_moves_of_forall_not_equiv h p) _
    exact e ▸ sub_nonneg.2 (hC p ⟨y, hy⟩ _)
  exact ne_top_of_le_ne_top WithTop.coe_ne_top (crossing_le_iff.2 (add_nonneg (hS _) (hS _)))

private theorem eventually_wall_le (p : Player) (x : IGame) [Short x] :
    ∀ᶠ C in atTop, ∀ t, wall p x t ≤ C := by
  induction x using moveRecOn generalizing ‹x.Short› p with | ind x ih
  by_cases! h : ∃ n : ℤ, x ≈ n
  · obtain ⟨n, hn⟩ := h
    filter_upwards [eventually_ge_atTop (wall p x ⊥)] with C hC t
    simpa [wall_of_equiv hn] using hC
  obtain ⟨τ, hτ⟩ := WithTop.ne_top_iff_exists.1 <|
    crossing_scaffold_ne_top_aux h fun p y hy _ ↦ ih p y hy (-p)
  filter_upwards [eventually_ge_atTop (scaffold p x τ)] with C hC t
  rw [wall_of_forall_not_equiv h, ← hτ, freeze_apply]
  exact ((scaffold p x).monotone (min_le_right _ _)).trans hC

/-- The walls of a short game eventually meet. -/
theorem crossing_wall_ne_top (x : IGame) [Short x] : crossing (wall left x) (wall right x) ≠ ⊤ := by
  by_cases! h : ∃ n : ℤ, x ≈ n
  · obtain ⟨n, hn⟩ := h
    exact ne_top_of_le_ne_top (WithTop.coe_ne_top (a := ⊥))
      (crossing_le_iff.2 (by simp [wall_of_equiv hn]))
  · simpa [wall_of_forall_not_equiv h] using
      crossing_scaffold_ne_top_aux h fun p y _ _ ↦ eventually_wall_le (-p) y

/-- The temperature of `x` is the least `t ≥ -1` at which its walls meet. -/
def temperature (x : IGame) [Short x] : 𝔻≥-1 :=
  (crossing (wall left x) (wall right x)).untop (crossing_wall_ne_top x)

/-- The mean value of `x`, i.e. the common value of its walls at and above its temperature. -/
def mean (x : IGame) [Short x] : Dyadic :=
  wall right x (temperature x)

theorem temperature_le_iff : temperature x ≤ t ↔ 0 ≤ wall left x t + wall right x t := by
  rw [temperature, ← WithTop.coe_le_coe, WithTop.coe_untop, crossing_le_iff]

/-- For a game not equal to an integer, the temperature is where the scaffolds meet. -/
theorem temperature_of_forall_not_equiv (h : ∀ n : ℤ, ¬ x ≈ n) :
    temperature x = crossing (scaffold left x) (scaffold right x) := by
  simp [temperature, wall_of_forall_not_equiv h]

theorem wall_apply_of_le_temperature (h : ∀ n : ℤ, ¬ x ≈ n) (ht : t ≤ temperature x) :
    wall p x t = scaffold p x t := by
  rw [wall_of_forall_not_equiv h, ← temperature_of_forall_not_equiv h, freeze_apply,
    min_eq_left ht]

theorem wall_apply_of_temperature_le (ht : temperature x ≤ t) :
    wall p x t = p.cases (-mean x) (mean x) := by
  by_cases! h : ∃ n : ℤ, x ≈ n
  · obtain ⟨n, hn⟩ := h
    cases p <;> simp [mean, wall_of_equiv hn]
  have hs := add_eq_zero_of_crossing_eq (temperature_of_forall_not_equiv h).symm
    (by simpa [wall_of_forall_not_equiv h] using (wall_bot_add_neg h).le)
  rw [mean, wall_apply_of_le_temperature h le_rfl, wall_of_forall_not_equiv h,
    ← temperature_of_forall_not_equiv h, freeze_apply, min_eq_right ht]
  cases p
  · exact eq_neg_of_add_eq_zero_left hs
  · rfl

theorem temperature_eq_bot_iff : temperature x = ⊥ ↔ ∃ n : ℤ, x ≈ n := by
  refine ⟨fun ht ↦ ?_, fun ⟨n, hn⟩ ↦ le_bot_iff.1 (temperature_le_iff.2 ?_)⟩
  · by_contra! h
    exact (wall_bot_add_neg h).not_ge (temperature_le_iff.1 ht.le)
  · simp [wall_of_equiv hn]

theorem temperature_neg (x : IGame) [Short x] : temperature (-x) = temperature x :=
  eq_of_forall_ge_iff fun t ↦ by
    rw [temperature_le_iff, temperature_le_iff, wall_neg, wall_neg, add_comm]
    rfl

theorem mean_neg (x : IGame) [Short x] : mean (-x) = -mean x := by
  rw [mean, wall_neg, temperature_neg]
  exact wall_apply_of_temperature_le le_rfl

theorem temperature_intCast (n : ℤ) : temperature n = ⊥ :=
  temperature_eq_bot_iff.2 ⟨n, .rfl⟩

theorem mean_intCast (n : ℤ) : mean n = n := by
  simp [mean, wall_intCast]

/-! ### Examples -/

omit [Short x] in
private theorem forall_not_equiv_of_lt {a b : ℤ} (ha : a < x) (hb : x < b)
    (h : ∀ n : ℤ, a < n → n < b → ¬ x ≈ n) (n : ℤ) : ¬ x ≈ n := fun hn ↦
  h n (intCast_lt.1 (ha.trans_le hn.le)) (intCast_lt.1 (hn.ge.trans_lt hb)) hn

private theorem temperature_mean_of {f g : Trajectory} {τ : 𝔻≥-1} {m : Dyadic}
    (h : ∀ n : ℤ, ¬ x ≈ n) (hl : scaffold left x = f) (hr : scaffold right x = g)
    (hτ : crossing f g = τ) (hm : g τ = m) : temperature x = τ ∧ mean x = m := by
  have hT : temperature x = τ :=
    WithTop.coe_injective (by rw [temperature_of_forall_not_equiv h, hl, hr, hτ])
  rw [mean, wall_apply_of_le_temperature h le_rfl, hr, hT, hm]
  exact ⟨rfl, rfl⟩

private theorem scaffold_of_moves_eq_intCast {n : ℤ} (h : x.moves p = {(n : IGame)}) :
    scaffold p x = reflect (const (p.cases n (-n))) := by
  cases p <;> simp [scaffold_of_moves_eq_singleton h, wall_intCast]

private theorem star_ne : ∀ n : ℤ, ¬ ⋆ ≈ n :=
  forall_not_equiv_of_lt (a := -1) (b := 1) (by game_cmp) (by game_cmp) fun n _ _ ↦ by
    interval_cases n; game_cmp

example : temperature (⋆ : IGame.{u}) = ⟨0, by decide⟩ ∧ mean (⋆ : IGame.{u}) = 0 :=
  temperature_mean_of star_ne (scaffold_of_moves_eq_intCast (n := 0) (by simp))
    (scaffold_of_moves_eq_intCast (n := 0) (by simp)) rfl rfl

example : temperature (↑ : IGame.{u}) = ⟨0, by decide⟩ ∧ mean (↑ : IGame.{u}) = 0 := by
  refine temperature_mean_of (forall_not_equiv_of_lt (a := 0) (b := 1) (by game_cmp) (by game_cmp)
    fun n _ _ ↦ by omega) (scaffold_of_moves_eq_intCast (n := 0) (by simp)) (by
      rw [scaffold_of_moves_eq_singleton (y := ⋆) (by simp), neg_right,
        wall_of_forall_not_equiv star_ne, scaffold_of_moves_eq_intCast (n := 0) (by simp),
        scaffold_of_moves_eq_intCast (n := 0) (by simp)]) (by rfl) (by rfl)

example : temperature (½ : IGame.{u}) = ⟨-.half, by decide⟩ ∧ mean (½ : IGame.{u}) = .half :=
  temperature_mean_of (forall_not_equiv_of_lt (a := 0) (b := 1) (by game_cmp) (by game_cmp)
    fun n _ _ ↦ by omega) (scaffold_of_moves_eq_intCast (n := 0) (by simp))
    (scaffold_of_moves_eq_intCast (n := 1) (by simp)) rfl rfl

example : temperature (±1 : IGame.{u}) = ⟨1, by decide⟩ ∧ mean (±1 : IGame.{u}) = 0 :=
  temperature_mean_of (forall_not_equiv_of_lt (a := -2) (b := 2) (by game_cmp) (by game_cmp)
    fun n _ _ ↦ by interval_cases n <;> game_cmp) (scaffold_of_moves_eq_intCast (n := 1) (by simp))
    (scaffold_of_moves_eq_intCast (n := -1) (by simp)) rfl rfl

private instance : Short !{{2} | {0}} := by
  rw [short_def]; simpa using Short.ofNat 2

example : temperature (!{{2} | {0}} : IGame.{u}) = ⟨1, by decide⟩ ∧
    mean (!{{2} | {0}} : IGame.{u}) = 1 :=
  temperature_mean_of (forall_not_equiv_of_lt (a := -1) (b := 3) (by game_cmp) (by game_cmp)
    fun n _ _ ↦ by interval_cases n <;> game_cmp) (scaffold_of_moves_eq_intCast (n := 2) (by simp))
    (scaffold_of_moves_eq_intCast (n := 0) (by simp)) rfl rfl

end IGame

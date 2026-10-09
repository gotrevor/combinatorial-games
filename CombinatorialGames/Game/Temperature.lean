/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
module

public import CombinatorialGames.Game.Trajectory
public import CombinatorialGames.Surreal.Basic

import CombinatorialGames.Tactic.GameCmp
import Mathlib.Data.Fintype.Order
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Tactic.Linarith -- shake: keep

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

open Player Trajectory

universe u

namespace IGame

theorem exists_eq_intCast_of_wsubposition {n : ℤ} {x : IGame} (h : WSubposition x n) :
    ∃ m : ℤ, x = m := by
  generalize hy : (n : IGame) = y at h
  induction y using moveRecOn generalizing n with | ind y ih
  obtain rfl | h := wsubposition_iff_eq_or_subposition.1 h
  · exact ⟨n, hy.symm⟩
  obtain ⟨p, z, hz, hxz⟩ := subposition_iff_exists.1 h
  subst hy
  cases p
  · exact ih _ z hz (eq_sub_one_of_mem_leftMoves_intCast hz).symm hxz
  · exact ih _ z hz (eq_add_one_of_mem_rightMoves_intCast hz).symm hxz

/-- If an integer fits within `x`, then `x` equals an integer. -/
theorem Fits.exists_intCast_equiv {n : ℤ} {x : IGame} (h : Fits n x) : ∃ m : ℤ, x ≈ m := by
  obtain ⟨y, hy, hyx⟩ := h.exists_wsubposition_equiv
  obtain ⟨m, rfl⟩ := exists_eq_intCast_of_wsubposition hy
  exact ⟨m, hyx.symm⟩

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
  obtain ⟨m, hm⟩ := Fits.exists_intCast_equiv (n := n)
    ⟨fun y hy hny ↦ left_lf hy (hn.le.trans hny), by simp [hx]⟩
  exact h m hm

private theorem intCast_le_of_forall_lf {x : IGame} (h : ∀ m : ℤ, ¬ x ≈ m) {n : ℤ}
    (hn : ∀ y ∈ xᴿ, n ⧏ y) : n ≤ x := by
  refine le_iff_forall_lf.2 ⟨fun z hz hxz ↦ ?_, hn⟩
  by_cases! hf : ∀ y ∈ xᴸ, y ⧏ n
  · obtain ⟨m, hm⟩ := Fits.exists_intCast_equiv ⟨hf, hn⟩
    exact h m hm
  · obtain ⟨y, hy, hny⟩ := hf
    exact left_lf hy (hxz.trans ((Numeric.left_lt hz).le.trans hny))

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
  rw [h, Set.mem_singleton_iff] at hz
  subst hz
  exact e

theorem wall_of_equiv {n : ℤ} (h : x ≈ n) : wall p x = const (p.cases (-n) n) := by
  have h' : ∃ n : ℤ, x ≈ n := ⟨n, h⟩
  rw [wall, dite_eq_left h', IGame.intCast_equiv.1 (h'.choose_spec.symm.trans h)]

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
      have := H (-y) (by simpa using hy)
      simp only [neg_neg] at this
      have h' := scaffold_apply_le (p := -p) (y := -y) (by simpa using hy) t
      rwa [neg_neg, ← this, ← e] at h'
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
private theorem wall_right_bot_aux (x : IGame) [Short x]
    (IH : ∀ y ∈ xᴿ, ∀ [Short y], ∃ k : ℤ, wall right (-y) ⊥ = k ∧ ∀ n : ℤ, n ≤ k ↔ n ≤ -y) :
    ∃ k : ℤ, wall right x ⊥ = k ∧ ∀ n : ℤ, n ≤ k ↔ n ≤ x := by
  by_cases! h : ∃ n : ℤ, x ≈ n
  · obtain ⟨m, hm⟩ := h
    exact ⟨m, by simp [wall_of_equiv hm], fun n ↦ by simp [hm.le_congr_right]⟩
  obtain ⟨y, hy, _, e⟩ := exists_scaffold_apply_eq (nonempty_moves_of_forall_not_equiv h right) ⊥
  obtain ⟨k, hk, hk'⟩ := IH y hy
  have hx : scaffold right x ⊥ = -1 - k := by
    rw [e, ← wall_neg, hk]
    rfl
  refine ⟨-1 - k, by simp [wall_of_forall_not_equiv h, hx], fun n ↦ ⟨fun hn ↦ ?_, fun hn ↦ ?_⟩⟩
  · refine intCast_le_of_forall_lf h fun z hz hzn ↦ ?_
    have := Short.of_mem_moves hz
    obtain ⟨l, hl, hl'⟩ := IH z hz
    have h₁ := scaffold_apply_le hz ⊥
    rw [hx, ← wall_neg, hl] at h₁
    have h₂ := (hl' (-n)).2 (by simpa)
    have : (l : Dyadic) ≤ k := by change _ ≤ (-1 : Dyadic) - l at h₁; linarith
    have := Int.cast_le.1 this
    omega
  · by_contra! hlt
    exact lf_right hy (hn.trans' (by simpa using (hk' (-n)).1 (by omega)))

private theorem wall_right_bot (x : IGame) [Short x] :
    ∃ k : ℤ, wall right x ⊥ = k ∧ ∀ n : ℤ, n ≤ k ↔ n ≤ x := by
  suffices ∀ x [Short x], (∃ k : ℤ, wall right x ⊥ = k ∧ ∀ n : ℤ, n ≤ k ↔ n ≤ x) ∧
      ∃ k : ℤ, wall right (-x) ⊥ = k ∧ ∀ n : ℤ, n ≤ k ↔ n ≤ -x from (this x).1
  intro x _
  induction x using moveRecOn generalizing ‹x.Short› with | ind x ih
  refine ⟨wall_right_bot_aux x fun y hy _ ↦ (ih _ y hy).2, wall_right_bot_aux (-x) fun y hy _ ↦ ?_⟩
  rw [moves_neg, Set.mem_neg] at hy
  have := Short.of_mem_moves hy
  simpa using (ih _ _ hy).1

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
    (H : ∀ p, ∀ y ∈ x.moves p, ∀ [Short y], ∃ C, ∀ q t, wall q y t ≤ C) :
    crossing (scaffold left x) (scaffold right x) ≠ ⊤ := by
  have (y : ⋃ p, x.moves p) : ∃ C, ∀ p (hy : y.1 ∈ x.moves p) t,
      (have := Short.of_mem_moves hy; wall (-p) y t) ≤ C := by
    obtain ⟨p, hp⟩ := Set.mem_iUnion.1 y.2
    have := Short.of_mem_moves hp
    exact (H p y hp).imp fun _ h _ _ ↦ h _
  choose C hC using this
  obtain ⟨M, hM⟩ := Finite.exists_le C
  have hS (p : Player) : Set.projIci (-1) M - M ≤ scaffold p x (Set.projIci (-1) M) := by
    obtain ⟨y, hy, _, e⟩ := exists_scaffold_apply_eq (nonempty_moves_of_forall_not_equiv h p) _
    linarith [hC ⟨y, Set.mem_iUnion_of_mem p hy⟩ p hy (Set.projIci (-1) M),
      hM ⟨y, Set.mem_iUnion_of_mem p hy⟩]
  have : M ≤ Set.projIci (-1) M := (le_max_right ..).trans_eq (Set.coe_projIci ..).symm
  exact ne_top_of_le_ne_top WithTop.coe_ne_top (crossing_le_iff.2 (by linarith [hS left, hS right]))

private theorem exists_wall_le (x : IGame) [Short x] : ∃ C, ∀ p t, wall p x t ≤ C := by
  induction x using moveRecOn generalizing ‹x.Short› with | ind x ih
  by_cases! h : ∃ n : ℤ, x ≈ n
  · obtain ⟨n, hn⟩ := h
    exact ⟨max (-n) n, fun p t ↦ by cases p <;> simp [wall_of_equiv hn]⟩
  obtain ⟨τ, hτ⟩ :=
    WithTop.ne_top_iff_exists.1 (crossing_scaffold_ne_top_aux h fun p y hy _ ↦ ih p y hy)
  refine ⟨max (scaffold left x τ) (scaffold right x τ), fun p t ↦ ?_⟩
  rw [wall_of_forall_not_equiv h, ← hτ, freeze_apply]
  cases p
  · exact ((scaffold _ x).monotone (min_le_right _ _)).trans (le_max_left ..)
  · exact ((scaffold _ x).monotone (min_le_right _ _)).trans (le_max_right ..)

/-- The scaffolds of a game which isn't equal to an integer meet, with equal values. -/
private theorem exists_crossing_scaffold (h : ∀ n : ℤ, ¬ x ≈ n) : ∃ τ : 𝔻≥-1,
    crossing (scaffold left x) (scaffold right x) = τ ∧
      scaffold left x τ + scaffold right x τ = 0 := by
  obtain ⟨τ, hτ⟩ := WithTop.ne_top_iff_exists.1 <|
    crossing_scaffold_ne_top_aux h fun _ y _ _ ↦ exists_wall_le y
  refine ⟨τ, hτ.symm, add_eq_zero_of_crossing_eq hτ.symm ?_⟩
  simpa [wall_of_forall_not_equiv h] using (wall_bot_add_neg h).le

private theorem crossing_wall_of_forall_not_equiv (h : ∀ n : ℤ, ¬ x ≈ n) :
    crossing (wall left x) (wall right x) = crossing (scaffold left x) (scaffold right x) := by
  obtain ⟨τ, hτ, hs⟩ := exists_crossing_scaffold h
  rw [wall_of_forall_not_equiv h, wall_of_forall_not_equiv h, hτ]
  refine eq_of_forall_ge_iff fun c ↦ ?_
  induction c using WithTop.recTopCoe with
  | top => simp
  | coe c =>
    rw [crossing_le_iff, freeze_apply, freeze_apply, WithTop.coe_le_coe]
    obtain hc | hc := le_total c τ
    · rw [min_eq_left hc, ← crossing_le_iff, hτ, WithTop.coe_le_coe]
    · simp [hs, hc]

/-- The walls of a short game eventually meet. -/
theorem crossing_wall_ne_top (x : IGame) [Short x] : crossing (wall left x) (wall right x) ≠ ⊤ := by
  by_cases! h : ∃ n : ℤ, x ≈ n
  · obtain ⟨n, hn⟩ := h
    exact ne_top_of_le_ne_top (WithTop.coe_ne_top (a := ⊥))
      (crossing_le_iff.2 (by simp [wall_of_equiv hn]))
  · obtain ⟨τ, hτ, -⟩ := exists_crossing_scaffold h
    simp [crossing_wall_of_forall_not_equiv h, hτ]

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
  rw [temperature, WithTop.coe_untop, crossing_wall_of_forall_not_equiv h]

theorem wall_apply_of_le_temperature (h : ∀ n : ℤ, ¬ x ≈ n) (ht : t ≤ temperature x) :
    wall p x t = scaffold p x t := by
  rw [wall_of_forall_not_equiv h, ← temperature_of_forall_not_equiv h, freeze_apply,
    min_eq_left ht]

theorem wall_apply_of_temperature_le (ht : temperature x ≤ t) :
    wall p x t = p.cases (-mean x) (mean x) := by
  by_cases! h : ∃ n : ℤ, x ≈ n
  · obtain ⟨n, hn⟩ := h
    cases p <;> simp [mean, wall_of_equiv hn]
  obtain ⟨τ, hτ, hs⟩ := exists_crossing_scaffold h
  have hT : temperature x = τ :=
    WithTop.coe_injective (by rw [temperature_of_forall_not_equiv h, hτ])
  rw [mean, wall_of_forall_not_equiv h, wall_of_forall_not_equiv h, hτ, freeze_apply,
    freeze_apply, hT, min_self, min_eq_right (hT ▸ ht)]
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

private theorem star_ne : ∀ n : ℤ, ¬ ⋆ ≈ n :=
  forall_not_equiv_of_lt (a := -1) (b := 1) (by game_cmp) (by game_cmp) fun n h₁ h₂ ↦ by
    obtain rfl : n = 0 := by omega
    game_cmp

private theorem scaffold_star (p : Player) : scaffold p ⋆ = reflect (const 0) := by
  cases p <;> simpa [scaffold_of_moves_eq_singleton (y := 0)] using
    congrArg reflect (wall_intCast _ 0)

example : temperature (⋆ : IGame.{u}) = ⟨0, by decide⟩ ∧ mean (⋆ : IGame.{u}) = 0 :=
  temperature_mean_of star_ne (scaffold_star _) (scaffold_star _) (τ := ⟨0, by decide⟩) rfl rfl

example : temperature (↑ : IGame.{u}) = ⟨0, by decide⟩ ∧ mean (↑ : IGame.{u}) = 0 := by
  have hs : wall left ⋆ = (reflect (const 0)).freeze ↑(⟨0, by decide⟩ : 𝔻≥-1) := by
    rw [wall_of_forall_not_equiv star_ne, scaffold_star, scaffold_star]
    rfl
  refine temperature_mean_of (x := ↑) (τ := ⟨0, by decide⟩) ?_
    (by simpa [scaffold_of_moves_eq_singleton (y := 0)] using congrArg reflect (wall_intCast _ 0))
    (by rw [scaffold_of_moves_eq_singleton (y := ⋆) (by simp), neg_right, hs]) (by rfl) (by rfl)
  exact forall_not_equiv_of_lt (a := 0) (b := 1) (by game_cmp) (by game_cmp) fun n _ _ ↦ by omega

example : temperature (½ : IGame.{u}) = ⟨-.half, by decide⟩ ∧ mean (½ : IGame.{u}) = .half := by
  refine temperature_mean_of (x := ½) (τ := ⟨-.half, by decide⟩) ?_
    (by simpa [scaffold_of_moves_eq_singleton (y := 0)] using congrArg reflect (wall_intCast _ 0))
    (by simpa [scaffold_of_moves_eq_singleton (y := 1)] using congrArg reflect (wall_intCast _ 1))
    (by rfl) (by rfl)
  exact forall_not_equiv_of_lt (a := 0) (b := 1) (by game_cmp) (by game_cmp) fun n _ _ ↦ by omega

example : temperature (±1 : IGame.{u}) = ⟨1, by decide⟩ ∧ mean (±1 : IGame.{u}) = 0 := by
  refine temperature_mean_of (x := ±1) (τ := ⟨1, by decide⟩) ?_
    (by simpa [scaffold_of_moves_eq_singleton (y := 1)] using congrArg reflect (wall_intCast _ 1))
    (by simpa [scaffold_of_moves_eq_singleton (y := -1)] using
      congrArg reflect (wall_intCast _ (-1))) (by rfl) (by rfl)
  refine forall_not_equiv_of_lt (a := -2) (b := 2) (by game_cmp) (by game_cmp) fun n _ _ ↦ ?_
  obtain rfl | rfl | rfl : n = -1 ∨ n = 0 ∨ n = 1 := by omega
  all_goals game_cmp

private instance : Short !{{2} | {0}} := by
  rw [short_def]; simpa using Short.ofNat 2

example : temperature (!{{2} | {0}} : IGame.{u}) = ⟨1, by decide⟩ ∧
    mean (!{{2} | {0}} : IGame.{u}) = 1 := by
  refine temperature_mean_of (x := !{{2} | {0}}) (τ := ⟨1, by decide⟩) ?_
    (by simpa [scaffold_of_moves_eq_singleton (y := 2)] using congrArg reflect (wall_intCast _ 2))
    (by simpa [scaffold_of_moves_eq_singleton (y := 0)] using congrArg reflect (wall_intCast _ 0))
    (by rfl) (by rfl)
  refine forall_not_equiv_of_lt (a := -1) (b := 3) (by game_cmp) (by game_cmp) fun n _ _ ↦ ?_
  obtain rfl | rfl | rfl : n = 0 ∨ n = 1 ∨ n = 2 := by omega
  all_goals game_cmp

end IGame

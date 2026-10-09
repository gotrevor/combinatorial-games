/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
module

public import CombinatorialGames.Game.Temperature
public import CombinatorialGames.Surreal.Birthday.Dyadic

import CombinatorialGames.Tactic.GameCmp
import Mathlib.Data.Set.Finite.Range
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith

/-!
# Cooling

The game `x` cooled by `t ≥ -1` (Siegel, *Combinatorial Game Theory*, §II.5) taxes every move of
`x` by `t`, until `x` freezes at its mean. Siegel defines it by recursion: if `x` equals an integer
it's unchanged, and otherwise it's `!{(cool · t - t) '' xᴸ | (cool · t + t) '' xᴿ}`, unless this
game is infinitely close to a number for some `t' < t`, in which case it's that number for the least
such `t'`.

Since we already have walls, temperature and mean, we instead define `x` cooled by `t` as its mean
once `t` exceeds its temperature, and recurse otherwise. We then show that this agrees with Siegel's
definition, and that the walls of `x` are the stops of `x` cooled by `t`. Since cooling by `t > -1`
is monotone, it respects equality, and hence so do walls, temperature and mean.

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

private theorem rightStop_eq_of {a : Dyadic} (h₁ : ∀ b : Dyadic, b < a → (b : IGame) ≤ x)
    (h₂ : ∀ b : Dyadic, a < b → x ⧏ b) : rightStop x = a := by
  refine le_antisymm (not_lt.1 fun h ↦ ?_) (not_lt.1 fun h ↦ ?_)
  · obtain ⟨b, hab, hb⟩ := exists_between h
    exact h₂ b hab (lt_of_lt_rightStop (Dyadic.toIGame_lt_toIGame.2 hb)).le
  · obtain ⟨b, hb, hba⟩ := exists_between h
    exact lf_of_rightStop_lt (Dyadic.toIGame_lt_toIGame.2 hb) (h₁ b hba)

private theorem leftStop_eq_of {a : Dyadic} (h₁ : ∀ b : Dyadic, b < a → (b : IGame) ⧏ x)
    (h₂ : ∀ b : Dyadic, a < b → x ≤ b) : leftStop x = a := by
  refine le_antisymm (not_lt.1 fun h ↦ ?_) (not_lt.1 fun h ↦ ?_)
  · obtain ⟨b, hab, hb⟩ := exists_between h
    exact lf_of_lt_leftStop (Dyadic.toIGame_lt_toIGame.2 hb) (h₂ b hab)
  · obtain ⟨b, hb, hba⟩ := exists_between h
    exact h₁ b hba (lt_of_leftStop_lt (Dyadic.toIGame_lt_toIGame.2 hb)).le

private theorem le_leftStop_of_lf {a : Dyadic} (h : (a : IGame) ⧏ x) : a ≤ leftStop x :=
  not_lt.1 fun ha ↦ h (lt_of_leftStop_lt (Dyadic.toIGame_lt_toIGame.2 ha)).le

private theorem rightStop_eq_of_eq {a b : IGame} [Short a] [Short b] (h : a = b) :
    rightStop a = rightStop b := by
  subst h; rfl

private theorem leftStop_eq_of_eq {a b : IGame} [Short a] [Short b] (h : a = b) :
    leftStop a = leftStop b := by
  subst h; rfl

private theorem rightStop_mono (h : x ≤ y) : rightStop x ≤ rightStop y :=
  not_lt.1 fun hs ↦ by
    obtain ⟨b, hb, hb'⟩ := exists_between hs
    exact lf_of_rightStop_lt (Dyadic.toIGame_lt_toIGame.2 hb)
      ((lt_of_lt_rightStop (Dyadic.toIGame_lt_toIGame.2 hb')).le.trans h)

@[simp]
private theorem rightStop_toIGame (a : Dyadic) : rightStop a = a :=
  rightStop_eq_of (fun _ h ↦ (Dyadic.toIGame_lt_toIGame.2 h).le)
    fun _ h ↦ (Dyadic.toIGame_lt_toIGame.2 h).not_ge

@[simp]
private theorem leftStop_toIGame (a : Dyadic) : leftStop a = a :=
  leftStop_eq_of (fun _ h ↦ (Dyadic.toIGame_lt_toIGame.2 h).not_ge)
    fun _ h ↦ (Dyadic.toIGame_lt_toIGame.2 h).le

theorem rightStop_neg (x : IGame) [Short x] : rightStop (-x) = -leftStop x := by
  refine rightStop_eq_of (fun b hb ↦ ?_) fun b hb ↦ ?_
  · rw [IGame.le_neg, ← Dyadic.toIGame_neg]
    exact (lt_of_leftStop_lt (Dyadic.toIGame_lt_toIGame.2 (lt_neg.1 hb))).le
  · rw [← IGame.neg_le_neg_iff, neg_neg, ← Dyadic.toIGame_neg]
    exact lf_of_lt_leftStop (Dyadic.toIGame_lt_toIGame.2 (neg_lt.1 hb))

theorem leftStop_neg (x : IGame) [Short x] : leftStop (-x) = -rightStop x := by
  exact neg_eq_iff_eq_neg.1 (by simpa using (rightStop_neg (-x)).symm)

private theorem rightStop_add_toIGame (x : IGame) [Short x] (a : Dyadic) :
    rightStop (x + a) = rightStop x + a := by
  refine rightStop_eq_of (fun b hb ↦ ?_) fun b hb ↦ ?_
  · rw [← IGame.sub_le_iff_le_add, ← (Dyadic.toIGame_sub_equiv b a).le_congr_left]
    exact (lt_of_lt_rightStop (Dyadic.toIGame_lt_toIGame.2 (sub_lt_iff_lt_add.2 hb))).le
  · rw [← IGame.sub_le_iff_le_add, ← (Dyadic.toIGame_sub_equiv b a).le_congr_left]
    exact lf_of_rightStop_lt (Dyadic.toIGame_lt_toIGame.2 (lt_sub_iff_add_lt.2 hb))

private theorem leftStop_add_toIGame (x : IGame) [Short x] (a : Dyadic) :
    leftStop (x + a) = leftStop x + a := by
  refine leftStop_eq_of (fun b hb ↦ ?_) fun b hb ↦ ?_
  · rw [← IGame.le_sub_iff_add_le, ← (Dyadic.toIGame_sub_equiv b a).le_congr_right]
    exact lf_of_lt_leftStop (Dyadic.toIGame_lt_toIGame.2 (sub_lt_iff_lt_add.2 hb))
  · rw [← IGame.le_sub_iff_add_le, ← (Dyadic.toIGame_sub_equiv b a).le_congr_right]
    exact (lt_of_leftStop_lt (Dyadic.toIGame_lt_toIGame.2 (lt_sub_iff_add_lt.2 hb))).le

private theorem rightStop_sub_toIGame (x : IGame) [Short x] (a : Dyadic) :
    rightStop (x - a) = rightStop x - a := by
  refine rightStop_eq_of (fun b hb ↦ ?_) fun b hb ↦ ?_
  · rw [IGame.le_sub_iff_add_le, ← (Dyadic.toIGame_add_equiv b a).le_congr_left]
    exact (lt_of_lt_rightStop (Dyadic.toIGame_lt_toIGame.2 (lt_sub_iff_add_lt.1 hb))).le
  · rw [IGame.le_sub_iff_add_le, ← (Dyadic.toIGame_add_equiv b a).le_congr_left]
    exact lf_of_rightStop_lt (Dyadic.toIGame_lt_toIGame.2 (sub_lt_iff_lt_add.1 hb))

/-- A short game is infinitely close to a number iff its stops agree. -/
theorem leftStop_eq_rightStop_iff : leftStop x = rightStop x ↔
    ∃ a : Dyadic, ∀ ε : Dyadic, 0 < ε → ((a - ε : Dyadic) : IGame) < x ∧ x < (a + ε : Dyadic) := by
  refine ⟨fun h ↦ ⟨rightStop x, fun ε hε ↦ ⟨lt_of_lt_rightStop ?_, lt_of_leftStop_lt ?_⟩⟩,
    fun ⟨a, ha⟩ ↦ le_antisymm ?_ (rightStop_le_leftStop x)⟩
  · exact Dyadic.toIGame_lt_toIGame.2 (sub_lt_self _ hε)
  · rw [h]; exact Dyadic.toIGame_lt_toIGame.2 (lt_add_of_pos_right _ hε)
  · refine le_trans (b := a) (not_lt.1 fun h ↦ ?_) (not_lt.1 fun h ↦ ?_)
    · obtain ⟨b, hb, hb'⟩ := exists_between h
      refine lf_of_lt_leftStop (Dyadic.toIGame_lt_toIGame.2 hb') ?_
      simpa using (ha (b - a) (sub_pos.2 hb)).2.le
    · obtain ⟨b, hb, hb'⟩ := exists_between h
      refine lf_of_rightStop_lt (Dyadic.toIGame_lt_toIGame.2 hb) ?_
      simpa using (ha (a - b) (sub_pos.2 hb')).1.le

/-- If the right stops of the left options of `x` don't exceed the least left stop of its right
options, the latter is the right stop of `x`. -/
private theorem rightStop_eq_of_moves {a : Dyadic}
    (h₁ : ∀ z ∈ xᴿ, ∀ [Short z], a ≤ leftStop z) (h₂ : ∃ z ∈ xᴿ, ∃ _ : Short z, leftStop z ≤ a)
    (h₃ : ∃ z ∈ xᴸ, ∃ _ : Short z, a ≤ rightStop z) : rightStop x = a := by
  obtain ⟨z, hz, _, hz'⟩ := h₂
  obtain ⟨y, hy, _, hy'⟩ := h₃
  refine rightStop_eq_of (fun b hb ↦ le_iff_forall_lf.2 ⟨fun c hc ↦ ?_, fun w hw ↦ ?_⟩)
    fun b hb ↦ ?_
  · have := (Numeric.left_lt hc).le.trans (lt_of_lt_rightStop
      (Dyadic.toIGame_lt_toIGame.2 (hb.trans_le hy'))).le
    exact fun h ↦ left_lf hy (h.trans this)
  · have := Short.of_mem_moves hw
    exact lf_of_lt_leftStop (Dyadic.toIGame_lt_toIGame.2 (hb.trans_le (h₁ w hw)))
  · exact fun h ↦ lf_right hz ((lt_of_leftStop_lt
      (Dyadic.toIGame_lt_toIGame.2 (hz'.trans_lt hb))).le.trans h)

/-- A short game which some dyadic fits in has equal stops. -/
private theorem leftStop_eq_rightStop_of_fits {a : Dyadic} (h : Fits a x) :
    leftStop x = rightStop x := by
  obtain ⟨z, hz, hzx⟩ := h.exists_wsubposition_equiv
  have : Short z := by
    obtain rfl | hz := wsubposition_iff_eq_or_subposition.1 hz
    exacts [inferInstance, .subposition hz]
  have := Numeric.wsubposition hz
  have H := equiv_toIGame_toDyadic z
  rw [← leftStop_congr hzx, ← rightStop_congr hzx, leftStop_congr H, rightStop_congr H,
    leftStop_toIGame, rightStop_toIGame]

/-! ### Cooling -/

mutual

/-- The game `!{(cool · t - t) '' xᴸ | (cool · t + t) '' xᴿ}`, i.e. `x` cooled by `t` unless `x`
has frozen. -/
def tax (x : IGame) [Short x] (t : 𝔻≥-1) : IGame :=
  !{.range fun y : xᴸ ↦ have := Short.of_mem_moves y.2; cool y t - (t : Dyadic) |
    .range fun y : xᴿ ↦ have := Short.of_mem_moves y.2; cool y t + (t : Dyadic)}
termination_by (x, 0)
decreasing_by all_goals igame_wf

/-- The game `x` cooled by `t`: this is `tax x t` while `x` is hot, i.e. `t` doesn't exceed its
temperature and `x` doesn't equal an integer, and its mean afterwards. -/
def cool (x : IGame) [Short x] (t : 𝔻≥-1) : IGame :=
  if ⊥ < temperature x ∧ t ≤ temperature x then tax x t else mean x
termination_by (x, 1)
decreasing_by exact .right _ one_pos

end

theorem leftMoves_tax :
    (tax x t)ᴸ = .range fun y : xᴸ ↦ have := Short.of_mem_moves y.2; cool y t - (t : Dyadic) := by
  rw [tax, leftMoves_ofSets]

theorem rightMoves_tax :
    (tax x t)ᴿ = .range fun y : xᴿ ↦ have := Short.of_mem_moves y.2; cool y t + (t : Dyadic) := by
  rw [tax, rightMoves_ofSets]

private theorem short_tax (H : ∀ p, ∀ y ∈ x.moves p, ∀ [Short y], Short (cool y t)) :
    Short (tax x t) := by
  rw [short_def]
  rintro (_ | _) <;> simp only [leftMoves_tax, rightMoves_tax] <;>
    refine ⟨Set.finite_range _, ?_⟩ <;> rintro _ ⟨⟨y, hy⟩, rfl⟩ <;>
    have := Short.of_mem_moves hy <;> have := H _ y hy <;> infer_instance

instance Short.cool (x : IGame) [Short x] (t : 𝔻≥-1) : Short (cool x t) := by
  induction x using moveRecOn generalizing ‹x.Short› with | ind x ih
  rw [IGame.cool]
  split_ifs
  · exact short_tax fun p y hy _ ↦ ih p y hy
  · infer_instance

instance Short.tax (x : IGame) [Short x] (t : 𝔻≥-1) : Short (tax x t) :=
  short_tax fun _ _ _ _ ↦ inferInstance

private theorem forall_not_equiv_of_bot_lt (h : ⊥ < temperature x) : ∀ n : ℤ, ¬ x ≈ n :=
  fun n hn ↦ h.ne' (temperature_eq_bot_iff.2 ⟨n, hn⟩)

private theorem bot_lt_of_forall_not_equiv (h : ∀ n : ℤ, ¬ x ≈ n) : ⊥ < temperature x :=
  bot_lt_iff_ne_bot.2 fun ht ↦ by
    obtain ⟨n, hn⟩ := temperature_eq_bot_iff.1 ht
    exact h n hn

theorem cool_of_le_temperature (h : ∀ n : ℤ, ¬ x ≈ n) (ht : t ≤ temperature x) :
    cool x t = tax x t := by
  rw [cool, ite_eq_left ⟨bot_lt_of_forall_not_equiv h, ht⟩]

theorem cool_of_temperature_lt (ht : temperature x < t) : cool x t = mean x := by
  rw [cool, ite_eq_right fun h ↦ h.2.not_gt ht]

private theorem cool_of_not_hot (h : ¬ (⊥ < temperature x ∧ t ≤ temperature x)) :
    cool x t = mean x := by
  rw [cool, ite_eq_right h]

private theorem mean_of_equiv {n : ℤ} (h : x ≈ n) : mean x = n := by
  have := wall_apply_of_temperature_le (x := x) (p := right) (t := temperature x) le_rfl
  rw [wall_of_equiv h] at this
  exact this.symm

theorem cool_of_equiv {n : ℤ} (h : x ≈ n) (t : 𝔻≥-1) : cool x t = n := by
  rw [cool_of_not_hot fun h' ↦ h'.1.ne' (temperature_eq_bot_iff.2 ⟨n, h⟩), mean_of_equiv h,
    Dyadic.toIGame_intCast]

@[simp] theorem cool_intCast (n : ℤ) (t : 𝔻≥-1) : cool n t = n := cool_of_equiv .rfl t
@[simp] theorem cool_natCast (n : ℕ) (t : 𝔻≥-1) : cool n t = n := by simpa using cool_intCast n t
@[simp] theorem cool_zero (t : 𝔻≥-1) : cool 0 t = 0 := by simpa using cool_natCast 0 t
@[simp] theorem cool_one (t : 𝔻≥-1) : cool 1 t = 1 := by simpa using cool_natCast 1 t

private theorem tax_neg_aux (H : ∀ p, ∀ y ∈ x.moves p, ∀ [Short y], cool (-y) t = -cool y t) :
    tax (-x) t = -tax x t := by
  ext (_ | _) w <;>
    simp only [moves_neg, leftMoves_tax, rightMoves_tax, neg_left, neg_right, Set.mem_neg,
      Set.mem_range, Subtype.exists] <;>
    refine ⟨?_, fun ⟨y, hy, e⟩ ↦ ⟨-y, by simpa using hy, ?_⟩⟩
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨z, hz, rfl⟩ : ∃ z ∈ xᴿ, -z = y := ⟨-y, hy, neg_neg y⟩
    have := Short.of_mem_moves hz
    exact ⟨z, hz, by rw [H _ z hz]; simp [sub_eq_add_neg, add_comm]⟩
  · have := Short.of_mem_moves hy
    rw [H _ y hy, ← neg_neg w, ← e]
    simp [sub_eq_add_neg, add_comm]
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨z, hz, rfl⟩ : ∃ z ∈ xᴸ, -z = y := ⟨-y, hy, neg_neg y⟩
    have := Short.of_mem_moves hz
    exact ⟨z, hz, by rw [H _ z hz]; simp [sub_eq_add_neg, add_comm]⟩
  · have := Short.of_mem_moves hy
    rw [H _ y hy, ← neg_neg w, ← e]
    simp [sub_eq_add_neg, add_comm]

theorem cool_neg (x : IGame) [Short x] (t : 𝔻≥-1) : cool (-x) t = -cool x t := by
  induction x using moveRecOn generalizing ‹x.Short› with | ind x ih
  rw [cool, cool, temperature_neg]
  split_ifs
  · exact tax_neg_aux fun p y hy _ ↦ ih p y hy
  · rw [mean_neg, Dyadic.toIGame_neg]

theorem tax_neg (x : IGame) [Short x] (t : 𝔻≥-1) : tax (-x) t = -tax x t :=
  tax_neg_aux fun _ _ _ _ ↦ cool_neg ..

/-! ### Walls are stops -/

private theorem wall_add_wall_nonpos (ht : t ≤ temperature x) :
    wall left x t + wall right x t ≤ 0 := by
  have := add_le_add ((wall left x).monotone ht) ((wall right x).monotone ht)
  rwa [wall_apply_of_temperature_le le_rfl, wall_apply_of_temperature_le le_rfl,
    neg_add_cancel] at this

private theorem scaffold_add_scaffold_nonpos (h : ∀ n : ℤ, ¬ x ≈ n) (ht : t ≤ temperature x) :
    scaffold left x t + scaffold right x t ≤ 0 := by
  simpa [wall_apply_of_le_temperature h ht] using wall_add_wall_nonpos ht

private theorem rightStop_tax_aux (h : ∀ n : ℤ, ¬ x ≈ n)
    (hs : scaffold left x t + scaffold right x t ≤ 0)
    (H : ∀ y ∈ xᴸ, ∀ [Short y], rightStop (cool y t) = wall right y t)
    (H' : ∀ y ∈ xᴿ, ∀ [Short y], leftStop (cool y t) = -wall left y t) :
    rightStop (tax x t) = scaffold right x t := by
  refine rightStop_eq_of_moves ?_ ?_ ?_
  · rw [rightMoves_tax]
    rintro _ ⟨⟨y, hy⟩, rfl⟩ _
    have := Short.of_mem_moves hy
    rw [leftStop_add_toIGame, H' y hy]
    simpa [neg_add_eq_sub] using scaffold_apply_le hy t
  · obtain ⟨y, hy, _, e⟩ := exists_scaffold_apply_eq (nonempty_moves_of_forall_not_equiv h right) t
    refine ⟨_, by rw [rightMoves_tax]; exact ⟨⟨y, hy⟩, rfl⟩, inferInstance, ?_⟩
    rw [leftStop_add_toIGame, H' y hy, e]
    simp [neg_add_eq_sub]
  · obtain ⟨y, hy, _, e⟩ := exists_scaffold_apply_eq (nonempty_moves_of_forall_not_equiv h left) t
    refine ⟨_, by rw [leftMoves_tax]; exact ⟨⟨y, hy⟩, rfl⟩, inferInstance, ?_⟩
    rw [rightStop_sub_toIGame, H y hy]
    simp only [neg_left] at e
    linarith

private theorem leftStop_tax_aux (h : ∀ n : ℤ, ¬ x ≈ n)
    (hs : scaffold left x t + scaffold right x t ≤ 0)
    (H : ∀ y ∈ xᴸ, ∀ [Short y], rightStop (cool y t) = wall right y t)
    (H' : ∀ y ∈ xᴿ, ∀ [Short y], leftStop (cool y t) = -wall left y t) :
    leftStop (tax x t) = -scaffold left x t := by
  have h' (n : ℤ) : ¬ -x ≈ n := fun hn ↦ h (-n) (by simpa using neg_equiv.1 hn)
  have e := rightStop_tax_aux (t := t) h' (by rwa [scaffold_neg, scaffold_neg, add_comm]) ?_ ?_
  · rw [rightStop_eq_of_eq (tax_neg x t), rightStop_neg, scaffold_neg, neg_right] at e
    rw [← e, neg_neg]
  all_goals
    intro y hy _
    simp only [moves_neg, neg_left, neg_right, Set.mem_neg] at hy
    obtain ⟨z, hz, rfl⟩ : ∃ z, _ ∧ -z = y := ⟨-y, hy, neg_neg y⟩
    have := Short.of_mem_moves hz
  · rw [rightStop_eq_of_eq (cool_neg z t), rightStop_neg, H' z hz, wall_neg, neg_right, neg_neg]
  · rw [leftStop_eq_of_eq (cool_neg z t), leftStop_neg, H z hz, wall_neg, neg_left]

private theorem stops_cool (x : IGame) [Short x] (t : 𝔻≥-1) :
    rightStop (cool x t) = wall right x t ∧ leftStop (cool x t) = -wall left x t := by
  induction x using moveRecOn generalizing ‹x.Short› with | ind x ih
  by_cases hx : ⊥ < temperature x ∧ t ≤ temperature x
  · have h := forall_not_equiv_of_bot_lt hx.1
    have hs := scaffold_add_scaffold_nonpos h hx.2
    have H : ∀ y ∈ xᴸ, ∀ [Short y], rightStop (cool y t) = wall right y t :=
      fun y hy _ ↦ (ih left y hy).1
    have H' : ∀ y ∈ xᴿ, ∀ [Short y], leftStop (cool y t) = -wall left y t :=
      fun y hy _ ↦ (ih right y hy).2
    rw [rightStop_eq_of_eq (cool_of_le_temperature h hx.2),
      leftStop_eq_of_eq (cool_of_le_temperature h hx.2), wall_apply_of_le_temperature h hx.2,
      wall_apply_of_le_temperature h hx.2]
    exact ⟨rightStop_tax_aux h hs H H', leftStop_tax_aux h hs H H'⟩
  · have ht : temperature x ≤ t := by
      by_contra! ht
      exact hx ⟨(bot_le.trans_lt ht), ht.le⟩
    rw [rightStop_eq_of_eq (cool_of_not_hot hx), leftStop_eq_of_eq (cool_of_not_hot hx),
      wall_apply_of_temperature_le ht, wall_apply_of_temperature_le ht]
    simp

theorem rightStop_cool (x : IGame) [Short x] (t : 𝔻≥-1) : rightStop (cool x t) = wall right x t :=
  (stops_cool x t).1

theorem leftStop_cool (x : IGame) [Short x] (t : 𝔻≥-1) : leftStop (cool x t) = -wall left x t :=
  (stops_cool x t).2

/-! ### Siegel's definition -/

theorem rightStop_tax_of_le_temperature (h : ∀ n : ℤ, ¬ x ≈ n) (ht : t ≤ temperature x) :
    rightStop (tax x t) = wall right x t := by
  rw [← rightStop_eq_of_eq (cool_of_le_temperature h ht), rightStop_cool]

theorem rightStop_tax_temperature (h : ∀ n : ℤ, ¬ x ≈ n) :
    rightStop (tax x (temperature x)) = mean x := by
  rw [rightStop_tax_of_le_temperature h le_rfl]
  exact wall_apply_of_temperature_le le_rfl

/-- The game `tax x t` is infinitely close to a number exactly from the temperature of `x` onwards.
Together with `rightStop_tax_temperature`, this says that `cool` agrees with Siegel's definition. -/
theorem leftStop_tax_eq_rightStop_tax_iff (h : ∀ n : ℤ, ¬ x ≈ n) :
    leftStop (tax x t) = rightStop (tax x t) ↔ temperature x ≤ t := by
  have H : ∀ y ∈ xᴸ, ∀ [Short y], rightStop (cool y t) = wall right y t :=
    fun y _ _ ↦ rightStop_cool y t
  have H' : ∀ y ∈ xᴿ, ∀ [Short y], leftStop (cool y t) = -wall left y t :=
    fun y _ _ ↦ leftStop_cool y t
  rw [← WithTop.coe_le_coe, temperature_of_forall_not_equiv h, crossing_le_iff]
  obtain hs | hs := le_or_gt (scaffold left x t + scaffold right x t) 0
  · rw [leftStop_tax_aux h hs H H', rightStop_tax_aux h hs H H', neg_eq_iff_add_eq_zero]
    exact ⟨fun h ↦ h.ge, fun h ↦ le_antisymm hs h⟩
  · refine iff_of_true ?_ hs.le
    obtain ⟨a, ha, ha'⟩ := exists_between (show -scaffold left x t < scaffold right x t by linarith)
    refine leftStop_eq_rightStop_of_fits (a := a) ⟨?_, ?_⟩
    · rw [leftMoves_tax]
      rintro _ ⟨⟨y, hy⟩, rfl⟩
      have := Short.of_mem_moves hy
      refine lf_of_rightStop_lt (Dyadic.toIGame_lt_toIGame.2 (lt_of_le_of_lt ?_ ha))
      rw [rightStop_sub_toIGame, H y hy, le_neg]
      simpa using scaffold_apply_le hy t
    · rw [rightMoves_tax]
      rintro _ ⟨⟨y, hy⟩, rfl⟩
      have := Short.of_mem_moves hy
      refine lf_of_lt_leftStop (Dyadic.toIGame_lt_toIGame.2 (ha'.trans_le ?_))
      rw [leftStop_add_toIGame, H' y hy]
      simpa [neg_add_eq_sub] using scaffold_apply_le hy t

/-! ### Monotonicity -/

private theorem sub_add_cancel_equiv (a b : IGame) : a - b + b ≈ a :=
  Game.mk_eq_mk.1 (by simp)

private theorem add_sub_cancel_equiv (a b : IGame) : a + b - b ≈ a :=
  Game.mk_eq_mk.1 (by simp)

private theorem temperature_lt_of_not_hot (hb : ⊥ < t)
    (h : ¬ (⊥ < temperature x ∧ t ≤ temperature x)) : temperature x < t :=
  not_le.1 fun ht ↦ h ⟨hb.trans_le ht, ht⟩

/-- If the right wall of `w` is constant on `[s, t]`, then `w` cooled by `t` is at least its value.
If `u ↦ u - wall left w u` is constant on `[s, t]`, then its value is less or fuzzy than `w` cooled
by `t`, plus `t`. -/
private theorem le_cool_and_lf_cool_add (w : IGame) [Short w] {s : 𝔻≥-1} (hs : s < t) :
    (wall right w s = wall right w t → (wall right w t : IGame) ≤ cool w t) ∧
    ((s : Dyadic) - wall left w s = t - wall left w t →
      (((t : Dyadic) - wall left w t : Dyadic) : IGame) ⧏ cool w t + (t : Dyadic)) := by
  induction w using moveRecOn generalizing ‹w.Short› with | ind w ih
  constructor
  · intro he
    by_cases hw : ⊥ < temperature w ∧ t ≤ temperature w
    · have h := forall_not_equiv_of_bot_lt hw.1
      rw [cool_of_le_temperature h hw.2]
      refine le_iff_forall_lf.2 ⟨fun c hc ↦ ?_, ?_⟩
      · have := Numeric.of_mem_moves hc
        refine (lt_of_lt_rightStop ((Numeric.left_lt hc).trans_le ?_)).not_ge
        exact Dyadic.toIGame_le_toIGame.2 (rightStop_tax_of_le_temperature h hw.2).ge
      · rw [rightMoves_tax]
        rintro _ ⟨⟨z, hz⟩, rfl⟩
        have := Short.of_mem_moves hz
        have h₁ := scaffold_apply_le hz t
        rw [neg_right, ← wall_apply_of_le_temperature h hw.2] at h₁
        obtain h₁ | h₁ := h₁.lt_or_eq
        · refine lf_of_lt_leftStop (Dyadic.toIGame_lt_toIGame.2 ?_)
          rwa [leftStop_add_toIGame, leftStop_cool, neg_add_eq_sub]
        · have h₂ := scaffold_apply_le hz s
          rw [neg_right, ← wall_apply_of_le_temperature h (hs.le.trans hw.2), he] at h₂
          have h₃ := (wall left z).reflect.monotone hs.le
          simp only [reflect_apply] at h₃
          rw [h₁]
          exact ((ih right z hz).2 (by linarith)).imp id
    · rw [cool_of_not_hot hw, wall_apply_of_temperature_le
        (temperature_lt_of_not_hot ((bot_le.trans_lt hs)) hw).le]
  · intro he
    have hw : ⊥ < temperature w ∧ t ≤ temperature w := by
      by_contra hw
      have hτ := temperature_lt_of_not_hot (bot_le.trans_lt hs) hw
      have hr : max (temperature w) s < t := max_lt hτ hs
      have h₁ := (wall left w).reflect.monotone (le_max_right (temperature w) s)
      have h₂ := (wall left w).reflect.monotone hr.le
      have h₃ : wall left w (max (temperature w) s) = wall left w t := by
        rw [wall_apply_of_temperature_le (le_max_left _ _),
          wall_apply_of_temperature_le hτ.le]
      simp only [reflect_apply] at h₁ h₂
      have : ((max (temperature w) s : 𝔻≥-1) : Dyadic) = t := by linarith
      exact hr.ne (Subtype.ext this)
    have h := forall_not_equiv_of_bot_lt hw.1
    rw [cool_of_le_temperature h hw.2]
    obtain ⟨v, hv, _, e⟩ :=
      exists_scaffold_apply_eq (nonempty_moves_of_forall_not_equiv h left) s
    have h₁ := scaffold_apply_le hv t
    have h₂ := (wall right v).monotone hs.le
    rw [← wall_apply_of_le_temperature h (hs.le.trans hw.2)] at e
    rw [← wall_apply_of_le_temperature h hw.2] at h₁
    simp only [neg_left] at e h₁
    have hv' : (((t : Dyadic) - wall left w t : Dyadic) : IGame) ≤ cool v t := by
      have := (ih left v hv).1 (by linarith)
      rwa [show wall right v t = t - wall left w t by linarith] at this
    refine lf_of_le_left (hv'.trans (sub_add_cancel_equiv _ _).ge) (add_right_mem_moves_add ?_ _)
    rw [leftMoves_tax]
    exact ⟨⟨v, hv⟩, rfl⟩

/-- Once `x` has frozen, its mean fits in `tax x t`: this is the right half. -/
private theorem mean_lf_cool_add (hb : ⊥ < t) (ht : temperature x < t) {z : IGame} [Short z]
    (hz : z ∈ xᴿ) : (mean x : IGame) ⧏ cool z t + (t : Dyadic) := by
  obtain ⟨s, hs, hm⟩ : ∃ s < t, mean x ≤ s - wall left z s := by
    by_cases! h : ∃ n : ℤ, x ≈ n
    · obtain ⟨n, hn⟩ := h
      obtain ⟨k, hk, hk'⟩ := wall_right_bot (-z)
      refine ⟨⊥, hb, ?_⟩
      have hm : mean x = n := by
        simpa [wall_of_equiv hn] using (wall_apply_of_temperature_le (x := x) (p := right)
          (t := temperature x) le_rfl).symm
      rw [wall_neg, neg_right] at hk
      rw [hm, hk]
      have : k ≤ -n - 1 := by
        by_contra! hk''
        exact lf_right hz (le_trans (by simpa using (hk' (-n)).1 (by omega)) hn.ge)
      change (n : Dyadic) ≤ -1 - k
      exact_mod_cast (by omega : n ≤ -1 - k)
    · refine ⟨temperature x, ht, ?_⟩
      have := scaffold_apply_le hz (temperature x)
      rwa [neg_right, ← wall_apply_of_le_temperature h le_rfl,
        wall_apply_of_temperature_le le_rfl] at this
  have h₁ := (wall left z).reflect.monotone hs.le
  simp only [reflect_apply] at h₁
  obtain hm' | hm' := (hm.trans h₁).lt_or_eq
  · refine lf_of_lt_leftStop (Dyadic.toIGame_lt_toIGame.2 ?_)
    rwa [leftStop_add_toIGame, leftStop_cool, neg_add_eq_sub]
  · rw [hm']
    exact (le_cool_and_lf_cool_add z hs).2 (le_antisymm h₁ (hm'.symm.trans_le hm))

/-- Once `x` has frozen, its mean fits in `tax x t`: this is the left half. -/
private theorem cool_sub_lf_mean (hb : ⊥ < t) (ht : temperature x < t) {y : IGame} [Short y]
    (hy : y ∈ xᴸ) : cool y t - (t : Dyadic) ⧏ mean x := by
  have := mean_lf_cool_add (x := -x) hb (by rwa [temperature_neg]) (z := -y) (by simpa)
  rw [mean_neg, Dyadic.toIGame_neg, cool_neg] at this
  exact fun h ↦ this (by simpa [neg_sub, sub_eq_neg_add] using IGame.neg_le_neg_iff.2 h)

/-- The induction hypothesis for `cool_le_cool`. -/
private def CoolMonoIH (x y : IGame) : Prop :=
  ∀ x' y' : IGame, [Short x'] → [Short y'] → birthday x' + birthday y' < birthday x + birthday y →
    ∀ t : 𝔻≥-1, ⊥ < t → x' ≤ y' → cool x' t ≤ cool y' t

private theorem CoolMonoIH.neg (IH : CoolMonoIH x y) : CoolMonoIH (-y) (-x) :=
  fun x' y' _ _ h ↦ IH x' y' (by rwa [birthday_neg, birthday_neg, add_comm (birthday y)] at h)

private theorem cool_le_cool_of_frozen (IH : CoolMonoIH x y) (hb : ⊥ < t)
    (hx : temperature x < t) (hy : ⊥ < temperature y ∧ t ≤ temperature y) (h : x ≤ y) :
    cool x t ≤ cool y t := by
  have hy' := forall_not_equiv_of_bot_lt hy.1
  rw [cool_of_temperature_lt hx, cool_of_le_temperature hy' hy.2]
  have H : ∀ u ∈ (tax y t)ᴿ, (mean x : IGame) ⧏ u := by
    rw [rightMoves_tax]
    rintro _ ⟨⟨w, hw⟩, rfl⟩
    have := Short.of_mem_moves hw
    dsimp only
    obtain ⟨z, hz, hxz⟩ | ⟨z, hz, hzw⟩ := lf_iff_exists_le.1 (lf_right_of_le h hw)
    · have := Short.of_mem_moves hz
      have hle := IH x z (add_lt_add_right ((birthday_lt_of_mem_moves hz).trans
        (birthday_lt_of_mem_moves hw)) _) t hb hxz
      rw [cool_of_temperature_lt hx] at hle
      by_cases hw' : ⊥ < temperature w ∧ t ≤ temperature w
      · rw [cool_of_le_temperature (forall_not_equiv_of_bot_lt hw'.1) hw'.2]
        refine lf_of_le_left (hle.trans (sub_add_cancel_equiv _ _).ge)
          (add_right_mem_moves_add ?_ _)
        rw [leftMoves_tax]
        exact ⟨⟨z, hz⟩, rfl⟩
      · rw [cool_of_not_hot hw']
        refine fun h' ↦ cool_sub_lf_mean hb (temperature_lt_of_not_hot hb hw') hz ?_
        rw [IGame.le_sub_iff_add_le]
        exact h'.trans hle
    · have := Short.of_mem_moves hz
      have hle := IH z w (add_lt_add (birthday_lt_of_mem_moves hz)
        (birthday_lt_of_mem_moves hw)) t hb hzw
      exact fun h' ↦ mean_lf_cool_add hb hx hz ((add_le_add_left hle _).trans h')
  refine le_iff_forall_lf.2 ⟨fun c hc ↦ ?_, H⟩
  have := Numeric.of_mem_moves hc
  obtain ⟨w, hw, _, e⟩ := exists_scaffold_apply_eq (nonempty_moves_of_forall_not_equiv hy' right) t
  have h₁ : mean x ≤ rightStop (tax y t) := by
    rw [rightStop_tax_of_le_temperature hy' hy.2, wall_apply_of_le_temperature hy' hy.2, e,
      neg_right]
    have := le_leftStop_of_lf (H _ (by rw [rightMoves_tax]; exact ⟨⟨w, hw⟩, rfl⟩))
    rwa [leftStop_add_toIGame, leftStop_cool, neg_add_eq_sub] at this
  exact (lt_of_lt_rightStop ((Numeric.left_lt hc).trans_le
    (Dyadic.toIGame_le_toIGame.2 h₁))).not_ge

private theorem lf_cool_of_hot (IH : CoolMonoIH x y) (hb : ⊥ < t)
    (hx : ⊥ < temperature x ∧ t ≤ temperature x) (h : x ≤ y) :
    ∀ v ∈ (tax x t)ᴸ, v ⧏ cool y t := by
  rw [leftMoves_tax]
  rintro _ ⟨⟨x', hx'⟩, rfl⟩
  have := Short.of_mem_moves hx'
  dsimp only
  obtain ⟨z, hz, hxz⟩ | ⟨z, hz, hzy⟩ := lf_iff_exists_le.1 (left_lf_of_le h hx')
  · have := Short.of_mem_moves hz
    have hle := IH x' z (add_lt_add (birthday_lt_of_mem_moves hx')
      (birthday_lt_of_mem_moves hz)) t hb hxz
    have key : cool z t - (t : Dyadic) ⧏ cool y t := by
      by_cases hy : ⊥ < temperature y ∧ t ≤ temperature y
      · rw [cool_of_le_temperature (forall_not_equiv_of_bot_lt hy.1) hy.2]
        refine left_lf ?_
        rw [leftMoves_tax]
        exact ⟨⟨z, hz⟩, rfl⟩
      · rw [cool_of_not_hot hy]
        exact cool_sub_lf_mean hb (temperature_lt_of_not_hot hb hy) hz
    exact fun h' ↦ key (h'.trans (add_le_add_left hle _))
  · have := Short.of_mem_moves hz
    have hle := IH z y (add_lt_add_left ((birthday_lt_of_mem_moves hz).trans
      (birthday_lt_of_mem_moves hx')) _) t hb hzy
    by_cases hx'' : ⊥ < temperature x' ∧ t ≤ temperature x'
    · rw [cool_of_le_temperature (forall_not_equiv_of_bot_lt hx''.1) hx''.2, sub_eq_add_neg]
      refine lf_of_right_le ((add_sub_cancel_equiv _ _).le.trans hle)
        (add_right_mem_moves_add ?_ _)
      rw [rightMoves_tax]
      exact ⟨⟨z, hz⟩, rfl⟩
    · rw [cool_of_not_hot hx'']
      refine fun h' ↦ mean_lf_cool_add hb (temperature_lt_of_not_hot hb hx'') hz ?_
      rw [← IGame.le_sub_iff_add_le]
      exact hle.trans h'

private theorem cool_le_cool_of_hot (IH : CoolMonoIH x y) (hb : ⊥ < t)
    (hhot : (⊥ < temperature x ∧ t ≤ temperature x) ∨ (⊥ < temperature y ∧ t ≤ temperature y))
    (h : x ≤ y) : cool x t ≤ cool y t := by
  have hneg : -y ≤ -x := IGame.neg_le_neg_iff.2 h
  by_cases hx : ⊥ < temperature x ∧ t ≤ temperature x <;>
    by_cases hy : ⊥ < temperature y ∧ t ≤ temperature y
  · have hx' := forall_not_equiv_of_bot_lt hx.1
    have hy' := forall_not_equiv_of_bot_lt hy.1
    have H₁ := lf_cool_of_hot IH hb hx h
    have H₂ := lf_cool_of_hot IH.neg hb (by rwa [temperature_neg]) hneg
    rw [tax_neg, moves_neg, cool_neg, cool_of_le_temperature hx' hx.2] at H₂
    rw [cool_of_le_temperature hy' hy.2] at H₁
    rw [cool_of_le_temperature hx' hx.2, cool_of_le_temperature hy' hy.2]
    refine le_iff_forall_lf.2 ⟨H₁, fun u hu ↦ ?_⟩
    simpa using H₂ (-u) (by simpa using hu)
  · have := cool_le_cool_of_frozen IH.neg hb
      (by rw [temperature_neg]; exact temperature_lt_of_not_hot hb hy)
      (by rwa [temperature_neg]) hneg
    rwa [cool_neg, cool_neg, IGame.neg_le_neg_iff] at this
  · exact cool_le_cool_of_frozen IH hb (temperature_lt_of_not_hot hb hx) hy h
  · exact (hhot.elim hx hy).elim

private theorem cool_le_cool_aux (x y : IGame) [Short x] [Short y] (t : 𝔻≥-1) (hb : ⊥ < t)
    (h : x ≤ y) : cool x t ≤ cool y t := by
  have IH : CoolMonoIH x y := fun x' y' _ _ _ t hb h ↦ cool_le_cool_aux x' y' t hb h
  by_cases hhot : (⊥ < temperature x ∧ t ≤ temperature x) ∨
      (⊥ < temperature y ∧ t ≤ temperature y)
  · exact cool_le_cool_of_hot IH hb hhot h
  rw [not_or] at hhot
  have hx := temperature_lt_of_not_hot hb hhot.1
  have hy := temperature_lt_of_not_hot hb hhot.2
  rw [cool_of_temperature_lt hx, cool_of_temperature_lt hy, Dyadic.toIGame_le_toIGame]
  have key {s : 𝔻≥-1} (hxs : temperature x ≤ s) (hys : temperature y ≤ s) (hs : ⊥ < s)
      (hhot : (⊥ < temperature x ∧ s ≤ temperature x) ∨ (⊥ < temperature y ∧ s ≤ temperature y)) :
      mean x ≤ mean y := by
    have := rightStop_mono (cool_le_cool_of_hot IH hs hhot h)
    rwa [rightStop_cool, rightStop_cool, wall_apply_of_temperature_le hxs,
      wall_apply_of_temperature_le hys] at this
  obtain hxy | hxy := le_total (temperature x) (temperature y)
  · obtain hy' | hy' := (bot_le : ⊥ ≤ temperature y).eq_or_lt
    · obtain ⟨n, hn⟩ := temperature_eq_bot_iff.1 (le_bot_iff.1 (hxy.trans hy'.ge))
      obtain ⟨m, hm⟩ := temperature_eq_bot_iff.1 hy'.symm
      rw [mean_of_equiv hn, mean_of_equiv hm, Int.cast_le, ← intCast_le]
      exact hn.ge.trans (h.trans hm.le)
    · exact key hxy le_rfl hy' (.inr ⟨hy', le_rfl⟩)
  · obtain hx' | hx' := (bot_le : ⊥ ≤ temperature x).eq_or_lt
    · obtain ⟨n, hn⟩ := temperature_eq_bot_iff.1 hx'.symm
      obtain ⟨m, hm⟩ := temperature_eq_bot_iff.1 (le_bot_iff.1 (hxy.trans hx'.ge))
      rw [mean_of_equiv hn, mean_of_equiv hm, Int.cast_le, ← intCast_le]
      exact hn.ge.trans (h.trans hm.le)
    · exact key le_rfl hxy hx' (.inl ⟨hx', le_rfl⟩)
termination_by birthday x + birthday y

theorem cool_le_cool (ht : ⊥ < t) (h : x ≤ y) : cool x t ≤ cool y t :=
  cool_le_cool_aux x y t ht h

theorem cool_congr (ht : ⊥ < t) (h : x ≈ y) : cool x t ≈ cool y t :=
  ⟨cool_le_cool ht h.le, cool_le_cool ht h.ge⟩

/-! ### Walls only depend on the value -/

private theorem wall_right_congr (h : x ≈ y) : wall right x = wall right y := by
  refine Trajectory.ext fun t ↦ ?_
  obtain rfl | ht := eq_bot_or_bot_lt t
  · obtain ⟨k, hk, hk'⟩ := wall_right_bot x
    obtain ⟨l, hl, hl'⟩ := wall_right_bot y
    rw [hk, hl, Int.cast_inj]
    exact le_antisymm ((hl' k).2 (((hk' k).1 le_rfl).trans h.le))
      ((hk' l).2 (((hl' l).1 le_rfl).trans h.ge))
  · rw [← rightStop_cool, ← rightStop_cool, rightStop_congr (cool_congr ht h)]

theorem wall_congr (h : x ≈ y) (p : Player) : wall p x = wall p y := by
  cases p
  · rw [← neg_right, ← wall_neg, ← wall_neg]
    exact wall_right_congr (neg_congr h)
  · exact wall_right_congr h

theorem temperature_congr (h : x ≈ y) : temperature x = temperature y :=
  eq_of_forall_ge_iff fun t ↦ by
    rw [temperature_le_iff, temperature_le_iff, wall_congr h, wall_congr h]

theorem mean_congr (h : x ≈ y) : mean x = mean y := by
  have H (z : IGame) [Short z] : wall right z (temperature z) = mean z :=
    wall_apply_of_temperature_le le_rfl
  rw [← H, ← H, wall_congr h, temperature_congr h]

end IGame

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

theorem cool_of_equiv {n : ℤ} (h : x ≈ n) (t : 𝔻≥-1) : cool x t = n := by
  have hm : mean x = n := by
    have := wall_apply_of_temperature_le (x := x) (p := right) (t := temperature x) le_rfl
    rw [wall_of_equiv h] at this
    exact this.symm
  rw [cool_of_not_hot fun h' ↦ h'.1.ne' (temperature_eq_bot_iff.2 ⟨n, h⟩), hm,
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

end IGame

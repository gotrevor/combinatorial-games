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
import Mathlib.Tactic.Linarith.Frontend

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

## Todo

Prove that cooling by `t > -1` is additive, `cool_add`, and hence that the mean is additive.
-/

public noncomputable section

open Player Trajectory

universe u

namespace IGame

variable {x y : IGame} [Short x] [Short y] {p : Player} {t : 𝔻≥-1}

/-! ### Stops -/

theorem rightStop_eq_of_forall {a : Dyadic} (h₁ : ∀ b : Dyadic, b < a → (b : IGame) ≤ x)
    (h₂ : ∀ b : Dyadic, a < b → x ⧏ b) : rightStop x = a := by
  refine le_antisymm (not_lt.1 fun h ↦ ?_) (not_lt.1 fun h ↦ ?_)
  · obtain ⟨b, hab, hb⟩ := exists_between h
    exact h₂ b hab (lt_of_lt_rightStop (Dyadic.toIGame_lt_toIGame.2 hb)).le
  · obtain ⟨b, hb, hba⟩ := exists_between h
    exact lf_of_rightStop_lt (Dyadic.toIGame_lt_toIGame.2 hb) (h₁ b hba)

theorem leftStop_eq_of_forall {a : Dyadic} (h₁ : ∀ b : Dyadic, b < a → (b : IGame) ⧏ x)
    (h₂ : ∀ b : Dyadic, a < b → x ≤ b) : leftStop x = a := by
  refine le_antisymm (not_lt.1 fun h ↦ ?_) (not_lt.1 fun h ↦ ?_)
  · obtain ⟨b, hab, hb⟩ := exists_between h
    exact lf_of_lt_leftStop (Dyadic.toIGame_lt_toIGame.2 hb) (h₂ b hab)
  · obtain ⟨b, hb, hba⟩ := exists_between h
    exact h₁ b hba (lt_of_leftStop_lt (Dyadic.toIGame_lt_toIGame.2 hb)).le

theorem le_leftStop_of_lf {a : Dyadic} (h : (a : IGame) ⧏ x) : a ≤ leftStop x :=
  not_lt.1 fun ha ↦ h (lt_of_leftStop_lt (Dyadic.toIGame_lt_toIGame.2 ha)).le

theorem rightStop_le_of_lf {a : Dyadic} (h : x ⧏ a) : rightStop x ≤ a :=
  not_lt.1 fun ha ↦ h (lt_of_lt_rightStop (Dyadic.toIGame_lt_toIGame.2 ha)).le

theorem rightStop_le_rightStop (h : x ≤ y) : rightStop x ≤ rightStop y :=
  not_lt.1 fun hs ↦ by
    obtain ⟨b, hb, hb'⟩ := exists_between hs
    exact lf_of_rightStop_lt (Dyadic.toIGame_lt_toIGame.2 hb)
      ((lt_of_lt_rightStop (Dyadic.toIGame_lt_toIGame.2 hb')).le.trans h)

theorem leftStop_le_leftStop (h : x ≤ y) : leftStop x ≤ leftStop y :=
  not_lt.1 fun hs ↦ by
    obtain ⟨b, hb, hb'⟩ := exists_between hs
    exact lf_of_lt_leftStop (Dyadic.toIGame_lt_toIGame.2 hb')
      (h.trans (lt_of_leftStop_lt (Dyadic.toIGame_lt_toIGame.2 hb)).le)

theorem rightStop_le_leftStop_of_mem_leftMoves (h : y ∈ xᴸ) : rightStop y ≤ leftStop x :=
  not_lt.1 fun hs ↦ by
    obtain ⟨b, hb, hb'⟩ := exists_between hs
    exact left_lf h ((lt_of_leftStop_lt (Dyadic.toIGame_lt_toIGame.2 hb)).le.trans
      (lt_of_lt_rightStop (Dyadic.toIGame_lt_toIGame.2 hb')).le)

theorem rightStop_le_leftStop_of_mem_rightMoves (h : y ∈ xᴿ) : rightStop x ≤ leftStop y :=
  not_lt.1 fun hs ↦ by
    obtain ⟨b, hb, hb'⟩ := exists_between hs
    exact lf_right h ((lt_of_leftStop_lt (Dyadic.toIGame_lt_toIGame.2 hb)).le.trans
      (lt_of_lt_rightStop (Dyadic.toIGame_lt_toIGame.2 hb')).le)

@[simp]
theorem rightStop_toIGame (a : Dyadic) : rightStop a = a :=
  rightStop_eq_of_forall (fun _ h ↦ (Dyadic.toIGame_lt_toIGame.2 h).le)
    fun _ h ↦ (Dyadic.toIGame_lt_toIGame.2 h).not_ge

@[simp]
theorem leftStop_toIGame (a : Dyadic) : leftStop a = a :=
  leftStop_eq_of_forall (fun _ h ↦ (Dyadic.toIGame_lt_toIGame.2 h).not_ge)
    fun _ h ↦ (Dyadic.toIGame_lt_toIGame.2 h).le

theorem rightStop_neg (x : IGame) [Short x] : rightStop (-x) = -leftStop x := by
  refine rightStop_eq_of_forall (fun b hb ↦ ?_) fun b hb ↦ ?_
  · rw [IGame.le_neg, ← Dyadic.toIGame_neg]
    exact (lt_of_leftStop_lt (Dyadic.toIGame_lt_toIGame.2 (lt_neg.1 hb))).le
  · rw [← IGame.neg_le_neg_iff, neg_neg, ← Dyadic.toIGame_neg]
    exact lf_of_lt_leftStop (Dyadic.toIGame_lt_toIGame.2 (neg_lt.1 hb))

theorem leftStop_neg (x : IGame) [Short x] : leftStop (-x) = -rightStop x :=
  neg_eq_iff_eq_neg.1 (by simpa using (rightStop_neg (-x)).symm)

theorem rightStop_add_toIGame (x : IGame) [Short x] (a : Dyadic) :
    rightStop (x + a) = rightStop x + a := by
  refine rightStop_eq_of_forall (fun b hb ↦ ?_) fun b hb ↦ ?_
  · rw [← IGame.sub_le_iff_le_add, ← (Dyadic.toIGame_sub_equiv b a).le_congr_left]
    exact (lt_of_lt_rightStop (Dyadic.toIGame_lt_toIGame.2 (sub_lt_iff_lt_add.2 hb))).le
  · rw [← IGame.sub_le_iff_le_add, ← (Dyadic.toIGame_sub_equiv b a).le_congr_left]
    exact lf_of_rightStop_lt (Dyadic.toIGame_lt_toIGame.2 (lt_sub_iff_add_lt.2 hb))

theorem leftStop_add_toIGame (x : IGame) [Short x] (a : Dyadic) :
    leftStop (x + a) = leftStop x + a := by
  refine leftStop_eq_of_forall (fun b hb ↦ ?_) fun b hb ↦ ?_
  · rw [← IGame.le_sub_iff_add_le, ← (Dyadic.toIGame_sub_equiv b a).le_congr_right]
    exact lf_of_lt_leftStop (Dyadic.toIGame_lt_toIGame.2 (sub_lt_iff_lt_add.2 hb))
  · rw [← IGame.le_sub_iff_add_le, ← (Dyadic.toIGame_sub_equiv b a).le_congr_right]
    exact (lt_of_leftStop_lt (Dyadic.toIGame_lt_toIGame.2 (lt_sub_iff_add_lt.2 hb))).le

theorem rightStop_sub_toIGame (x : IGame) [Short x] (a : Dyadic) :
    rightStop (x - a) = rightStop x - a := by
  rw [rightStop_congr (y := x + (-a : Dyadic))
    (.of_eq (by rw [Dyadic.toIGame_neg, sub_eq_add_neg])),
    rightStop_add_toIGame, sub_eq_add_neg]

theorem rightStop_add_rightStop_le (x y : IGame) [Short x] [Short y] :
    rightStop x + rightStop y ≤ rightStop (x + y) := by
  refine not_lt.1 fun h ↦ ?_
  obtain ⟨c, hc, hc'⟩ := exists_between h
  obtain ⟨a, ha, ha'⟩ := exists_between (sub_lt_iff_lt_add.2 hc')
  refine lf_of_rightStop_lt (Dyadic.toIGame_lt_toIGame.2 hc) ?_
  rw [show c = a + (c - a) by linarith, (Dyadic.toIGame_add_equiv _ _).le_congr_left]
  exact (add_lt_add (lt_of_lt_rightStop (Dyadic.toIGame_lt_toIGame.2 ha'))
    (lt_of_lt_rightStop (Dyadic.toIGame_lt_toIGame.2 (sub_lt_comm.1 ha)))).le

theorem leftStop_add_le (x y : IGame) [Short x] [Short y] :
    leftStop (x + y) ≤ leftStop x + leftStop y := by
  have := rightStop_add_rightStop_le (-x) (-y)
  rw [rightStop_congr (neg_add x y).symm.antisymmRel, rightStop_neg, rightStop_neg,
    rightStop_neg] at this
  linarith

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

/-- If some right option of `x` has left stop `a`, none has a smaller one, and some left option has
right stop at least `a`, then `a` is the right stop of `x`. -/
theorem rightStop_eq_of_moves {a : Dyadic}
    (h₁ : ∀ z ∈ xᴿ, ∀ [Short z], a ≤ leftStop z) (h₂ : ∃ z ∈ xᴿ, ∃ _ : Short z, leftStop z ≤ a)
    (h₃ : ∃ z ∈ xᴸ, ∃ _ : Short z, a ≤ rightStop z) : rightStop x = a := by
  obtain ⟨z, hz, _, hz'⟩ := h₂
  obtain ⟨y, hy, _, hy'⟩ := h₃
  refine rightStop_eq_of_forall (fun b hb ↦ le_iff_forall_lf.2 ⟨fun c hc ↦ ?_, fun w hw ↦ ?_⟩)
    fun b hb ↦ ?_
  · have := (Numeric.left_lt hc).le.trans (lt_of_lt_rightStop
      (Dyadic.toIGame_lt_toIGame.2 (hb.trans_le hy'))).le
    exact fun h ↦ left_lf hy (h.trans this)
  · have := Short.of_mem_moves hw
    exact lf_of_lt_leftStop (Dyadic.toIGame_lt_toIGame.2 (hb.trans_le (h₁ w hw)))
  · exact fun h ↦ lf_right hz ((lt_of_leftStop_lt
      (Dyadic.toIGame_lt_toIGame.2 (hz'.trans_lt hb))).le.trans h)

/-- A short game which some dyadic fits in has equal stops. -/
theorem leftStop_eq_rightStop_of_fits {a : Dyadic} (h : Fits a x) :
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

/-- The game `!{(cool · t - t) '' xᴸ | (cool · t + t) '' xᴿ}`, `x` cooled by `t` until frozen. -/
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
  bot_lt_iff_ne_bot.2 fun ht ↦ let ⟨n, hn⟩ := temperature_eq_bot_iff.1 ht; h n hn

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

private theorem scaffold_add_scaffold_nonpos (h : ∀ n : ℤ, ¬ x ≈ n) (ht : t ≤ temperature x) :
    scaffold left x t + scaffold right x t ≤ 0 := by
  have := add_le_add ((wall left x).monotone ht) ((wall right x).monotone ht)
  rwa [wall_apply_of_temperature_le le_rfl, wall_apply_of_temperature_le le_rfl, neg_add_cancel,
    wall_apply_of_le_temperature h ht, wall_apply_of_le_temperature h ht] at this

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
  · rw [rightStop_congr (tax_neg x t).antisymmRel, rightStop_neg, scaffold_neg, neg_right] at e
    rw [← e, neg_neg]
  all_goals
    intro y hy _
    simp only [moves_neg, neg_left, neg_right, Set.mem_neg] at hy
    obtain ⟨z, hz, rfl⟩ : ∃ z, _ ∧ -z = y := ⟨-y, hy, neg_neg y⟩
    have := Short.of_mem_moves hz
  · rw [rightStop_congr (cool_neg z t).antisymmRel, rightStop_neg, H' z hz, wall_neg, neg_right,
      neg_neg]
  · rw [leftStop_congr (cool_neg z t).antisymmRel, leftStop_neg, H z hz, wall_neg, neg_left]

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
    have e : cool x t ≈ tax x t := (cool_of_le_temperature h hx.2).antisymmRel
    rw [rightStop_congr e, leftStop_congr e, wall_apply_of_le_temperature h hx.2,
      wall_apply_of_le_temperature h hx.2]
    exact ⟨rightStop_tax_aux h hs H H', leftStop_tax_aux h hs H H'⟩
  · have ht : temperature x ≤ t := by
      by_contra! ht
      exact hx ⟨(bot_le.trans_lt ht), ht.le⟩
    have e : cool x t ≈ mean x := (cool_of_not_hot hx).antisymmRel
    rw [rightStop_congr e, leftStop_congr e, wall_apply_of_temperature_le ht,
      wall_apply_of_temperature_le ht]
    simp

theorem rightStop_cool (x : IGame) [Short x] (t : 𝔻≥-1) : rightStop (cool x t) = wall right x t :=
  (stops_cool x t).1

theorem leftStop_cool (x : IGame) [Short x] (t : 𝔻≥-1) : leftStop (cool x t) = -wall left x t :=
  (stops_cool x t).2

/-! ### Siegel's definition -/

theorem rightStop_tax_of_le_temperature (h : ∀ n : ℤ, ¬ x ≈ n) (ht : t ≤ temperature x) :
    rightStop (tax x t) = wall right x t := by
  rw [← rightStop_congr (cool_of_le_temperature h ht).antisymmRel, rightStop_cool]

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
      rw [wall_neg, neg_right] at hk
      rw [mean_of_equiv hn, hk]
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

/-! ### Additivity -/

private theorem cool_eq_of_eq {a b : IGame} [Short a] [Short b] (h : a = b) :
    cool a t = cool b t := by
  subst h; rfl

private theorem tax_eq_of_eq {a b : IGame} [Short a] [Short b] (h : a = b) :
    tax a t = tax b t := by
  subst h; rfl

private theorem lf_of_leftStop_lt_leftStop (h : leftStop x < leftStop y) : x ⧏ y :=
  fun h' ↦ (leftStop_le_leftStop h').not_gt h

private theorem cool_sub_lf_cool (hb : ⊥ < t) {y : IGame} [Short y] (hy : y ∈ xᴸ) :
    cool y t - (t : Dyadic) ⧏ cool x t := by
  by_cases hx : ⊥ < temperature x ∧ t ≤ temperature x
  · rw [cool_of_le_temperature (forall_not_equiv_of_bot_lt hx.1) hx.2]
    exact left_lf (by rw [leftMoves_tax]; exact ⟨⟨y, hy⟩, rfl⟩)
  · rw [cool_of_not_hot hx]
    exact cool_sub_lf_mean hb (temperature_lt_of_not_hot hb hx) hy

private theorem exists_leftStop_cool (h : ⊥ < temperature x ∧ t ≤ temperature x) :
    ∃ y ∈ xᴸ, ∃ _ : Short y, rightStop (cool y t) - t = leftStop (cool x t) := by
  have h' := forall_not_equiv_of_bot_lt h.1
  obtain ⟨y, hy, _, e⟩ := exists_scaffold_apply_eq (nonempty_moves_of_forall_not_equiv h' left) t
  refine ⟨y, hy, inferInstance, ?_⟩
  rw [leftStop_cool, wall_apply_of_le_temperature h' h.2, e, rightStop_cool, neg_left, neg_sub]

private theorem exists_rightStop_cool (h : ⊥ < temperature x ∧ t ≤ temperature x) :
    ∃ y ∈ xᴿ, ∃ _ : Short y, leftStop (cool y t) + t = rightStop (cool x t) := by
  have h' := forall_not_equiv_of_bot_lt h.1
  obtain ⟨y, hy, _, e⟩ := exists_scaffold_apply_eq (nonempty_moves_of_forall_not_equiv h' right) t
  refine ⟨y, hy, inferInstance, ?_⟩
  rw [rightStop_cool, wall_apply_of_le_temperature h' h.2, e, leftStop_cool, neg_right,
    neg_add_eq_sub]

/-- The induction hypothesis for `cool_add`. -/
private def CoolAddIH (x y : IGame) : Prop :=
  ∀ x' y' : IGame, [Short x'] → [Short y'] → birthday x' + birthday y' < birthday x + birthday y →
    ∀ t : 𝔻≥-1, ⊥ < t → cool (x' + y') t ≈ cool x' t + cool y' t

omit [Short x] [Short y] in
private theorem CoolAddIH.neg (IH : CoolAddIH x y) : CoolAddIH (-x) (-y) :=
  fun x' y' _ _ h ↦ IH x' y' (by rwa [birthday_neg, birthday_neg] at h)

omit [Short x] [Short y] in
private theorem CoolAddIH.swap (IH : CoolAddIH x y) : CoolAddIH y x :=
  fun x' y' _ _ h ↦ IH x' y' (by rwa [add_comm (birthday y)] at h)

/-- Half of `tax (x + y) t ≈ cool x t + cool y t`, while `y` is hot. -/
private theorem tax_add_left (IH : CoolAddIH x y) (hb : ⊥ < t)
    (hy : ⊥ < temperature y ∧ t ≤ temperature y) :
    (∀ a ∈ (tax (x + y) t)ᴸ, a ⧏ cool x t + cool y t) ∧
    (∀ b ∈ (cool x t + cool y t)ᴸ, b ⧏ tax (x + y) t) := by
  have hY := cool_of_le_temperature (forall_not_equiv_of_bot_lt hy.1) hy.2
  have hl {a : IGame} [Short a] (ha : a ∈ xᴸ) : cool (a + y) t - (t : Dyadic) ≈
      cool a t - (t : Dyadic) + cool y t := Game.mk_eq_mk.1 <| by
    simp only [Game.mk_sub, Game.mk_add, Game.mk_eq_mk.2 (IH a y (add_lt_add_left
      (birthday_lt_of_mem_moves ha) _) t hb), add_sub_right_comm]
  have hr {b : IGame} [Short b] (hb' : b ∈ yᴸ) : cool (x + b) t - (t : Dyadic) ≈
      cool x t + (cool b t - (t : Dyadic)) := Game.mk_eq_mk.1 <| by
    simp only [Game.mk_sub, Game.mk_add, Game.mk_eq_mk.2 (IH x b (add_lt_add_right
      (birthday_lt_of_mem_moves hb') _) t hb), add_sub_assoc]
  have hT {w : IGame} [Short w] (hw : w ∈ (x + y)ᴸ) :
      cool w t - (t : Dyadic) ⧏ tax (x + y) t :=
    left_lf (by rw [leftMoves_tax]; exact ⟨⟨w, hw⟩, rfl⟩)
  constructor
  · rw [leftMoves_tax]
    rintro _ ⟨⟨w, hw⟩, rfl⟩
    rw [moves_add] at hw
    obtain ⟨a, ha, rfl⟩ | ⟨b, hb', rfl⟩ := hw
    · have := Short.of_mem_moves ha
      exact (hl ha).le_congr_right.not.2 fun h ↦ cool_sub_lf_cool hb ha (le_of_add_le_add_right h)
    · have := Short.of_mem_moves hb'
      exact (hr hb').le_congr_right.not.2 fun h ↦ cool_sub_lf_cool hb hb' (le_of_add_le_add_left h)
  · intro v hv
    simp only [moves_add, Set.mem_union, Set.mem_image] at hv
    obtain ⟨a, ha, rfl⟩ | ⟨b, hb', rfl⟩ := hv
    · by_cases hx : ⊥ < temperature x ∧ t ≤ temperature x
      · rw [cool_of_le_temperature (forall_not_equiv_of_bot_lt hx.1) hx.2, leftMoves_tax] at ha
        obtain ⟨⟨a, ha⟩, rfl⟩ := ha
        have := Short.of_mem_moves ha
        exact (hl ha).le_congr_right.not.1 (hT (add_right_mem_moves_add ha y))
      · rw [cool_of_not_hot hx] at ha
        obtain rfl := Dyadic.eq_lower_of_mem_leftMoves_toIGame ha
        obtain ⟨b, hb', _, e⟩ := exists_leftStop_cool hy
        refine lf_of_leftStop_lt_leftStop ((rightStop_le_leftStop_of_mem_leftMoves
          (by rw [leftMoves_tax]; exact ⟨⟨_, add_left_mem_moves_add hb' x⟩, rfl⟩)).trans_lt' ?_)
        have h₁ := rightStop_add_rightStop_le (cool x t) (cool b t)
        rw [← rightStop_congr (IH x b (add_lt_add_right (birthday_lt_of_mem_moves hb') _) t hb),
          rightStop_congr (cool_of_not_hot hx).antisymmRel, rightStop_toIGame] at h₁
        rw [leftStop_congr (add_comm _ _).antisymmRel, leftStop_add_toIGame,
          rightStop_sub_toIGame]
        have := Dyadic.lower_lt (mean x)
        linarith
    · rw [hY, leftMoves_tax] at hb'
      obtain ⟨⟨b, hb'⟩, rfl⟩ := hb'
      have := Short.of_mem_moves hb'
      exact (hr hb').le_congr_right.not.1 (hT (add_left_mem_moves_add hb' x))

private theorem tax_add_equiv (IH : CoolAddIH x y) (hb : ⊥ < t)
    (hy : ⊥ < temperature y ∧ t ≤ temperature y) :
    tax (x + y) t ≈ cool x t + cool y t := by
  obtain ⟨hl₁, hl₂⟩ := tax_add_left IH hb hy
  obtain ⟨hr₁, hr₂⟩ := tax_add_left IH.neg hb (by rwa [temperature_neg])
  rw [tax_eq_of_eq (neg_add x y).symm, tax_neg, cool_neg, cool_neg, ← neg_add] at hr₁ hr₂
  refine equiv_of_forall_lf hl₁ (fun u hu ↦ ?_) hl₂ fun v hv ↦ ?_
  · have := hr₁ (-u) (by simpa using hu)
    rwa [IGame.neg_le_neg_iff] at this
  · have := hr₂ (-v) (by rw [moves_neg, neg_left, Set.neg_mem_neg]; exact hv)
    rwa [IGame.neg_le_neg_iff] at this

private theorem fits_mean_tax (hb : ⊥ < t) (ht : temperature x < t) : Fits (mean x) (tax x t) := by
  refine ⟨fun v hv ↦ ?_, fun u hu ↦ ?_⟩
  · rw [leftMoves_tax] at hv
    obtain ⟨⟨y, hy⟩, rfl⟩ := hv
    have := Short.of_mem_moves hy
    exact cool_sub_lf_mean hb ht hy
  · rw [rightMoves_tax] at hu
    obtain ⟨⟨z, hz⟩, rfl⟩ := hu
    have := Short.of_mem_moves hz
    exact mean_lf_cool_add hb ht hz

/-- While `y` is hot, the only dyadic that fits in `tax (x + y) t` is
`leftStop (cool x t) + rightStop (cool y t)`. -/
private theorem eq_of_fits_tax_add (IH : CoolAddIH x y) (hb : ⊥ < t)
    (hy : ⊥ < temperature y ∧ t ≤ temperature y) {a : Dyadic} (h : Fits a (tax (x + y) t)) :
    a = leftStop (cool x t) + rightStop (cool y t) := by
  have hR {b : IGame} [Short b] (hb' : b ∈ yᴸ) :
      rightStop (cool x t) + rightStop (cool b t) - t ≤ a := by
    have := rightStop_le_of_lf (h.1 _ (by
      rw [leftMoves_tax]; exact ⟨⟨_, add_left_mem_moves_add hb' x⟩, rfl⟩))
    rw [rightStop_sub_toIGame, rightStop_congr (IH x b (add_lt_add_right
      (birthday_lt_of_mem_moves hb') _) t hb)] at this
    linarith [rightStop_add_rightStop_le (cool x t) (cool b t)]
  refine le_antisymm ?_ ?_
  · obtain ⟨z, hz, _, e⟩ := exists_rightStop_cool hy
    have := le_leftStop_of_lf (h.2 _ (by
      rw [rightMoves_tax]; exact ⟨⟨_, add_left_mem_moves_add hz x⟩, rfl⟩))
    rw [leftStop_add_toIGame, leftStop_congr (IH x z (add_lt_add_right
      (birthday_lt_of_mem_moves hz) _) t hb)] at this
    linarith [leftStop_add_le (cool x t) (cool z t)]
  · by_cases hx : ⊥ < temperature x ∧ t ≤ temperature x
    · obtain ⟨w, hw, _, e⟩ := exists_leftStop_cool hx
      have := rightStop_le_of_lf (h.1 _ (by
        rw [leftMoves_tax]; exact ⟨⟨_, add_right_mem_moves_add hw y⟩, rfl⟩))
      rw [rightStop_sub_toIGame, rightStop_congr (IH w y (add_lt_add_left
        (birthday_lt_of_mem_moves hw) _) t hb)] at this
      linarith [rightStop_add_rightStop_le (cool w t) (cool y t)]
    · obtain ⟨b, hb', _, e⟩ := exists_leftStop_cool hy
      have := hR hb'
      have hx' : cool x t ≈ mean x := (cool_of_not_hot hx).antisymmRel
      rw [leftStop_congr hx', leftStop_toIGame]
      rw [rightStop_congr hx', rightStop_toIGame] at this
      linarith [rightStop_le_leftStop (cool y t)]

private theorem cool_add_of_le (IH : CoolAddIH x y) (hb : ⊥ < t)
    (hxy : temperature x ≤ temperature y) : cool (x + y) t ≈ cool x t + cool y t := by
  obtain hy | hy := (bot_le : ⊥ ≤ temperature y).eq_or_lt
  · obtain ⟨n, hn⟩ := temperature_eq_bot_iff.1 (le_bot_iff.1 (hxy.trans hy.ge))
    obtain ⟨m, hm⟩ := temperature_eq_bot_iff.1 hy.symm
    rw [cool_of_equiv hn, cool_of_equiv hm,
      cool_of_equiv ((add_congr hn hm).trans (intCast_add_equiv n m).symm)]
    exact intCast_add_equiv n m
  have key {t : 𝔻≥-1} (hb : ⊥ < t) (ht : t ≤ temperature y) :
      cool (x + y) t ≈ cool x t + cool y t := by
    have H := tax_add_equiv IH hb ⟨hy, ht⟩
    by_cases hs : ⊥ < temperature (x + y) ∧ t ≤ temperature (x + y)
    · rwa [cool_of_le_temperature (forall_not_equiv_of_bot_lt hs.1) hs.2]
    have hf := fits_mean_tax hb (temperature_lt_of_not_hot hb hs)
    obtain ⟨z, hz, hzT⟩ := hf.exists_wsubposition_equiv
    have : Short z := by
      obtain rfl | hz := wsubposition_iff_eq_or_subposition.1 hz
      exacts [inferInstance, .subposition hz]
    have := Numeric.wsubposition hz
    have hd := (equiv_toIGame_toDyadic z).symm.trans hzT
    rw [cool_of_not_hot hs, (eq_of_fits_tax_add IH hb ⟨hy, ht⟩ hf).trans
      (eq_of_fits_tax_add IH hb ⟨hy, ht⟩ (fits_of_equiv hd)).symm]
    exact hd.trans H
  obtain ht | ht := le_or_gt t (temperature y)
  · exact key hb ht
  have E := key hy le_rfl
  have h₁ := rightStop_add_rightStop_le (cool x (temperature y)) (cool y (temperature y))
  have h₂ := leftStop_add_le (cool x (temperature y)) (cool y (temperature y))
  have h₃ := rightStop_le_leftStop (cool (x + y) (temperature y))
  rw [← rightStop_congr E] at h₁
  rw [← leftStop_congr E] at h₂
  simp only [rightStop_cool, leftStop_cool, wall_apply_of_temperature_le hxy,
    wall_apply_of_temperature_le le_rfl, Player.cases, neg_neg] at h₁ h₂ h₃
  have hτ : temperature (x + y) ≤ temperature y := temperature_le_iff.2 (by linarith)
  have hm : mean (x + y) = mean x + mean y := by
    have : wall right (x + y) (temperature y) = mean (x + y) := wall_apply_of_temperature_le hτ
    linarith
  rw [cool_of_temperature_lt (hτ.trans_lt ht), cool_of_temperature_lt (hxy.trans_lt ht),
    cool_of_temperature_lt ht, hm]
  exact Dyadic.toIGame_add_equiv _ _

private theorem cool_add_aux (x y : IGame) [Short x] [Short y] (t : 𝔻≥-1) (hb : ⊥ < t) :
    cool (x + y) t ≈ cool x t + cool y t := by
  have IH : CoolAddIH x y := fun x' y' _ _ _ t hb ↦ cool_add_aux x' y' t hb
  obtain h | h := le_total (temperature x) (temperature y)
  · exact cool_add_of_le IH hb h
  · rw [cool_eq_of_eq (add_comm x y), add_comm (cool x t)]
    exact cool_add_of_le IH.swap hb h
termination_by birthday x + birthday y

/-- Cooling by `t > -1` is additive (Bando, Ken and Morikawa, Theorem 12). -/
theorem cool_add (ht : ⊥ < t) (x y : IGame) [Short x] [Short y] :
    cool (x + y) t ≈ cool x t + cool y t :=
  cool_add_aux x y t ht

theorem mean_add (x y : IGame) [Short x] [Short y] : mean (x + y) = mean x + mean y := by
  let τ := max (temperature (x + y)) (max (temperature x) (temperature y))
  let t : 𝔻≥-1 := ⟨τ + 1, Set.mem_Ici.2 (by linarith [Set.mem_Ici.1 τ.2])⟩
  have ht : τ < t := Subtype.mk_lt_mk.2 (lt_add_one (τ : Dyadic))
  have h := cool_add (bot_le.trans_lt ht) x y
  rw [cool_of_temperature_lt ((le_max_left _ _).trans_lt ht),
    cool_of_temperature_lt (((le_max_left _ _).trans (le_max_right _ _)).trans_lt ht),
    cool_of_temperature_lt (((le_max_right _ _).trans (le_max_right _ _)).trans_lt ht)] at h
  exact Dyadic.toIGame_equiv_toIGame.1 (h.trans (Dyadic.toIGame_add_equiv _ _).symm)

theorem zero_le_cool (ht : ⊥ < t) {x : IGame} [Short x] (h : 0 ≤ x) : 0 ≤ cool x t := by
  by_cases hx : ⊥ < temperature x ∧ t ≤ temperature x
  · rw [cool_of_le_temperature (forall_not_equiv_of_bot_lt hx.1) hx.2, zero_le, rightMoves_tax]
    rintro _ ⟨⟨z, hz⟩, rfl⟩ h'
    have := Short.of_mem_moves hz
    obtain ⟨w, hw, hw'⟩ := zero_lf.1 (lf_right_of_le h hz)
    have := Short.of_mem_moves hw
    refine cool_sub_lf_cool ht hw ((IGame.le_sub_iff_add_le.2 h').trans ?_)
    exact add_le_add_left (zero_le_cool ht hw') _
  · obtain ⟨k, hk, hk'⟩ := wall_right_bot x
    have := (wall right x).monotone (bot_le : ⊥ ≤ temperature x)
    rw [hk, wall_apply_of_temperature_le le_rfl] at this
    rw [cool_of_not_hot hx, Dyadic.zero_le_toIGame]
    exact (Int.cast_nonneg ((hk' 0).2 (by simpa using h))).trans this
termination_by x
decreasing_by igame_wf

/-- Cooling by `t > -1` is monotone (Bando, Ken and Morikawa, Theorem 11). -/
theorem cool_le_cool (ht : ⊥ < t) (h : x ≤ y) : cool x t ≤ cool y t := by
  have := (zero_le_cool ht (IGame.sub_nonneg.2 h)).trans (cool_add ht y (-x)).le
  rwa [cool_neg, ← sub_eq_add_neg, IGame.sub_nonneg] at this

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
  have H : wall right x (temperature x) = mean x := wall_apply_of_temperature_le le_rfl
  rw [← H, wall_apply_of_le_temperature h le_rfl, hr, hT, hm]
  exact ⟨rfl, rfl⟩

private theorem scaffold_of_moves_eq_intCast {n : ℤ} (h : x.moves p = {(n : IGame)}) :
    scaffold p x = reflect (const (p.cases n (-n))) := by
  cases p <;> simp [scaffold_of_moves_eq_singleton h, wall_intCast]

private theorem star_ne : ∀ n : ℤ, ¬ ⋆ ≈ n :=
  forall_not_equiv_of_lt (a := -1) (b := 1) (by game_cmp) (by game_cmp) fun n _ _ ↦ by
    interval_cases n; game_cmp

private theorem temperature_mean_star :
    temperature (⋆ : IGame.{u}) = ⟨0, by decide⟩ ∧ mean (⋆ : IGame.{u}) = 0 :=
  temperature_mean_of star_ne (scaffold_of_moves_eq_intCast (n := 0) (by simp))
    (scaffold_of_moves_eq_intCast (n := 0) (by simp)) rfl rfl

private theorem temperature_mean_up :
    temperature (↑ : IGame.{u}) = ⟨0, by decide⟩ ∧ mean (↑ : IGame.{u}) = 0 := by
  refine temperature_mean_of (forall_not_equiv_of_lt (a := 0) (b := 1) (by game_cmp) (by game_cmp)
    fun n _ _ ↦ by omega) (scaffold_of_moves_eq_intCast (n := 0) (by simp)) (by
      rw [scaffold_of_moves_eq_singleton (y := ⋆) (by simp), neg_right,
        wall_of_forall_not_equiv star_ne, scaffold_of_moves_eq_intCast (n := 0) (by simp),
        scaffold_of_moves_eq_intCast (n := 0) (by simp)]) (by rfl) (by rfl)

example : temperature (½ : IGame.{u}) = ⟨-.half, by decide⟩ ∧ mean (½ : IGame.{u}) = .half :=
  temperature_mean_of (forall_not_equiv_of_lt (a := 0) (b := 1) (by game_cmp) (by game_cmp)
    fun n _ _ ↦ by omega) (scaffold_of_moves_eq_intCast (n := 0) (by simp))
    (scaffold_of_moves_eq_intCast (n := 1) (by simp)) rfl rfl

private theorem temperature_mean_switch :
    temperature (±1 : IGame.{u}) = ⟨1, by decide⟩ ∧ mean (±1 : IGame.{u}) = 0 :=
  temperature_mean_of (forall_not_equiv_of_lt (a := -2) (b := 2) (by game_cmp) (by game_cmp)
    fun n _ _ ↦ by interval_cases n <;> game_cmp) (scaffold_of_moves_eq_intCast (n := 1) (by simp))
    (scaffold_of_moves_eq_intCast (n := -1) (by simp)) rfl rfl

private instance : Short !{{2} | {0}} := by
  rw [short_def]; simpa using Short.ofNat 2

private theorem temperature_mean_two_zero :
    temperature (!{{2} | {0}} : IGame.{u}) = ⟨1, by decide⟩ ∧ mean (!{{2} | {0}} : IGame.{u}) = 1 :=
  temperature_mean_of (forall_not_equiv_of_lt (a := -1) (b := 3) (by game_cmp) (by game_cmp)
    fun n _ _ ↦ by interval_cases n <;> game_cmp) (scaffold_of_moves_eq_intCast (n := 2) (by simp))
    (scaffold_of_moves_eq_intCast (n := 0) (by simp)) rfl rfl

private theorem mem_moves_tax {w : IGame} :
    w ∈ (tax x t).moves p ↔ ∃ y, ∃ h : y ∈ x.moves p,
      @cool y (.of_mem_moves h) t + p.cases (-(t : Dyadic) : IGame) (t : Dyadic) = w := by
  cases p <;> simp [leftMoves_tax, rightMoves_tax, sub_eq_add_neg]

private theorem tax_eq {a b : IGame} [Short a] [Short b] (hl : xᴸ = {a}) (hr : xᴿ = {b}) :
    tax x t = !{{cool a t - (t : Dyadic)} | {cool b t + (t : Dyadic)}} := by
  ext p w
  cases p <;> simp only [mem_moves_tax, hl, hr, moves_ofSets, Player.cases, Set.mem_singleton_iff,
    sub_eq_add_neg] <;> exact ⟨fun ⟨_, rfl, e⟩ ↦ e.symm, fun e ↦ ⟨_, rfl, e.symm⟩⟩

example : cool (⋆ : IGame) ⟨0, by decide⟩ = ⋆ := by
  rw [cool_of_le_temperature star_ne temperature_mean_star.1.ge, tax_eq (moves_star left)
    (moves_star right)]
  ext p; cases p <;> simp

example (ht : (0 : Dyadic) < t) : cool (⋆ : IGame) t = 0 := by
  rw [cool_of_temperature_lt (temperature_mean_star.1.trans_lt ht), temperature_mean_star.2,
    Dyadic.toIGame_zero]

example (ht : (0 : Dyadic) < t) : cool (↑ : IGame) t = 0 := by
  rw [cool_of_temperature_lt (temperature_mean_up.1.trans_lt ht), temperature_mean_up.2,
    Dyadic.toIGame_zero]

private theorem switch_one_ne : ∀ n : ℤ, ¬ (±1 : IGame) ≈ n :=
  forall_not_equiv_of_lt (a := -2) (b := 2) (by game_cmp) (by game_cmp) fun n _ _ ↦ by
    interval_cases n <;> game_cmp

example : cool (±1) ⟨.half, by decide⟩ ≈ ±½ := by
  rw [cool_of_le_temperature switch_one_ne (temperature_mean_switch.1.ge.trans' (by decide)),
    tax_eq (leftMoves_switch 1) (rightMoves_switch 1)]
  simp only [cool_neg, cool_one, Dyadic.toIGame_half]
  game_cmp

example : cool (±1) ⟨1, by decide⟩ ≈ ⋆ := by
  rw [cool_of_le_temperature switch_one_ne temperature_mean_switch.1.ge,
    tax_eq (leftMoves_switch 1) (rightMoves_switch 1)]
  simp only [cool_neg, cool_one, Dyadic.toIGame_one]
  game_cmp

private theorem two_zero_ne : ∀ n : ℤ, ¬ (!{{2} | {0}} : IGame) ≈ n :=
  forall_not_equiv_of_lt (a := -1) (b := 3) (by game_cmp) (by game_cmp) fun n _ _ ↦ by
    interval_cases n <;> game_cmp

example : cool !{{2} | {0}} ⟨1, by decide⟩ ≈ 1 + ⋆ := by
  rw [cool_of_le_temperature two_zero_ne temperature_mean_two_zero.1.ge,
    tax_eq (leftMoves_ofSets ..) (rightMoves_ofSets ..)]
  rw [show cool 2 ⟨1, by decide⟩ = 2 by simpa using cool_natCast 2 ⟨1, by decide⟩]
  simp only [Dyadic.toIGame_one, cool_zero, zero_add]
  game_cmp

example (ht : (1 : Dyadic) < t) : cool !{{2} | {0}} t = 1 := by
  rw [cool_of_temperature_lt (temperature_mean_two_zero.1.trans_lt ht),
    temperature_mean_two_zero.2, Dyadic.toIGame_one]

private instance : Short !{{⋆, 1} | {0}} := by
  rw [short_def]; simp

private instance : Short !{{1} | {0}} := by
  rw [short_def]; simp

/-- Cooling by `-1` does not respect equality. -/
example : !{{⋆, 1} | {0}} ≈ !{{1} | {0}} ∧ ¬ cool !{{⋆, 1} | {0}} ⊥ ≈ cool !{{1} | {0}} ⊥ := by
  refine ⟨by game_cmp, ?_⟩
  have hA : cool !{{⋆, 1} | {0}} ⊥ = !{{!{{(0 : IGame) - -1} | {(0 : IGame) + -1}} - -1,
      (1 : IGame) - -1} | {(0 : IGame) + -1}} := by
    rw [cool_of_le_temperature (forall_not_equiv_of_lt (a := -1) (b := 2) (by game_cmp)
      (by game_cmp) fun n _ _ ↦ by interval_cases n <;> game_cmp) bot_le]
    ext p w
    cases p <;> simp only [mem_moves_tax, moves_ofSets, Player.cases, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    · refine ⟨fun ⟨y, hy, e⟩ ↦ ?_, fun h ↦ ?_⟩
      · obtain rfl | rfl := hy
        · left
          rw [← e, cool_of_le_temperature star_ne bot_le, tax_eq (moves_star left)
            (moves_star right)]
          simp [sub_eq_add_neg]
        · simp [← e]
      · obtain rfl | rfl := h
        · refine ⟨⋆, .inl rfl, ?_⟩
          rw [cool_of_le_temperature star_ne bot_le, tax_eq (moves_star left) (moves_star right)]
          simp [sub_eq_add_neg]
        · exact ⟨1, .inr rfl, by simp [sub_eq_add_neg]⟩
    · exact ⟨fun ⟨y, hy, e⟩ ↦ by subst hy; simp [← e], fun h ↦ ⟨0, rfl, by simp [h]⟩⟩
  have hB : cool !{{1} | {0}} ⊥ = !{{(1 : IGame) - -1} | {(0 : IGame) + -1}} := by
    rw [cool_of_le_temperature (forall_not_equiv_of_lt (a := -1) (b := 2) (by game_cmp)
      (by game_cmp) fun n _ _ ↦ by interval_cases n <;> game_cmp) bot_le,
      tax_eq (leftMoves_ofSets ..) (rightMoves_ofSets ..)]
    simp [sub_eq_add_neg]
  rw [hA, hB]
  game_cmp

end IGame

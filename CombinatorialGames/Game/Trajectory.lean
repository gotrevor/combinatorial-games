/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
module

public import CombinatorialGames.Mathlib.Dyadic
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Finset.Union
public import Mathlib.Order.Interval.Set.ProjIcc
public import Mathlib.Order.LatticeIntervals

import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Tactic.Linarith -- shake: keep
import Mathlib.Tactic.Ring.RingNF

/-!
# Trajectories

A trajectory is a continuous piecewise linear function `𝔻≥-1 → Dyadic` with finitely many
breakpoints, whose slopes are all `0` or `1`. These are the building blocks of the left and right
walls of a short game (Siegel, *Combinatorial Game Theory*, pp. 106-107).

Trajectories form a distributive lattice under pointwise `min` and `max`, and are closed under the
reflection `t ↦ t - f t`, which swaps the slopes `0` and `1`. Since a sum `f + g` of two
trajectories has slopes `0`, `1` or `2`, the least `t` with `0 ≤ f t + g t` is dyadic; we compute it
as `Trajectory.crossing`.

## Implementation notes

A trajectory is stored as its underlying function, together with a finite set of points which
contains its breakpoints. This set is wrapped in `Trunc`, so that trajectories with the same values
are equal, while the breakpoints remain available to computations such as `Trajectory.crossing`.

The notation `𝔻≥-1` for `Set.Ici (-1 : Dyadic)` clashes with the subtype notation of the same name
in #462.
-/

@[expose] public section

open Set

/-- The dyadic rationals `t ≥ -1`, i.e. the possible temperatures of a short game. -/
notation "𝔻≥-1" => Set.Ici (-1 : Dyadic)

namespace Trajectory

/-- Every interval which doesn't meet `s` in its interior is mapped by `f` linearly, with slope
`0` or `1`. -/
def IsBreakSet (s : Finset 𝔻≥-1) (f : 𝔻≥-1 → Dyadic) : Prop :=
  ∀ ⦃t u⦄, t ≤ u → Disjoint (s : Set 𝔻≥-1) (Ioo t u) → f u = f t ∨ f u = f t + (u - t)

variable {s s' : Finset 𝔻≥-1} {f g : 𝔻≥-1 → Dyadic} {q t u : 𝔻≥-1}

theorem IsBreakSet.linear (hf : IsBreakSet s f) (hqu : q ≤ u)
    (hd : Disjoint (s : Set 𝔻≥-1) (Ioo q u)) :
    (∀ t ∈ Icc q u, f t = f q) ∨ ∀ t ∈ Icc q u, f t = f q + (t - q) := by
  obtain h | h := hf hqu hd <;> [left; right] <;> intro t ⟨hqt, htu⟩ <;>
    obtain h₁ | h₁ := hf hqt (hd.mono_right (Ioo_subset_Ioo_right htu)) <;>
    obtain h₂ | h₂ := hf htu (hd.mono_right (Ioo_subset_Ioo_left hqt)) <;>
    linarith [Subtype.coe_le_coe.2 hqt, Subtype.coe_le_coe.2 htu]

theorem IsBreakSet.monotone (hf : IsBreakSet s f) : Monotone f := by
  suffices ∀ r : Finset 𝔻≥-1, ∀ ⦃t u⦄, t ≤ u → (∀ x ∈ s, x ∈ Ioo t u → x ∈ r) → f t ≤ f u from
    fun t u h ↦ this s h fun x hx _ ↦ hx
  intro r
  induction r using Finset.induction_on with
  | empty =>
    intro t u htu h
    obtain h | h := hf htu (disjoint_left.2 fun x hx hx' ↦ by simpa using h x hx hx') <;>
      linarith [Subtype.coe_le_coe.2 htu]
  | insert a r _ ih =>
    intro t u htu h
    by_cases ha : a ∈ Ioo t u
    · exact (ih ha.1.le fun x hx hx' ↦ by grind).trans (ih ha.2.le fun x hx hx' ↦ by grind)
    · exact ih htu fun x hx hx' ↦ by grind

theorem IsBreakSet.reflect (hf : IsBreakSet s f) : IsBreakSet s fun t ↦ t - f t :=
  fun _ _ htu hd ↦ by rcases hf htu hd with h | h <;> simp only [h] <;> [right; left] <;> ring

/-- An interval which doesn't meet `s` extends leftwards to one starting in `insert ⊥ s`. -/
private theorem exists_extend (hd : Disjoint (s : Set 𝔻≥-1) (Ioo t u)) :
    ∃ q ∈ insert ⊥ s, q ≤ t ∧ Disjoint (s : Set 𝔻≥-1) (Ioo q u) := by
  let F := (insert ⊥ s).filter (· ≤ t)
  obtain ⟨hq, hqt⟩ := Finset.mem_filter.1 (F.max'_mem ⟨⊥, by simp [F]⟩)
  refine ⟨_, hq, hqt, disjoint_left.2 fun p hp hp' ↦ ?_⟩
  by_cases hpt : p ≤ t
  · exact hp'.1.not_ge (F.le_max' p (by simp [F, Finset.mem_coe.1 hp, hpt]))
  · exact disjoint_left.1 hd hp ⟨not_le.1 hpt, hp'.2⟩

theorem IsBreakSet.mono (hf : IsBreakSet s f) (hs : s ⊆ s') : IsBreakSet s' f :=
  fun _ _ htu hd ↦ hf htu (hd.mono_left (Finset.coe_subset.2 hs))

theorem IsBreakSet.min (hf : IsBreakSet s f) (hg : IsBreakSet s g) :
    IsBreakSet (s ∪ (insert ⊥ s).biUnion fun q ↦
      {projIci (-1) (q + (f q - g q)), projIci (-1) (q - (f q - g q))})
      fun t ↦ min (f t) (g t) := by
  intro t u htu hd
  obtain ⟨q, hq, hqt, hq'⟩ :=
    exists_extend (hd.mono_left (Finset.coe_subset.2 Finset.subset_union_left))
  have hc := hd.mono_left <| Finset.coe_subset.2 <|
    (Finset.subset_biUnion_of_mem _ hq).trans Finset.subset_union_right
  simp [← Subtype.coe_lt_coe, coe_projIci] at hc
  have ht : t ∈ Icc q u := ⟨hqt, htu⟩
  have hu : u ∈ Icc q u := ⟨hqt.trans htu, le_rfl⟩
  obtain hF | hF := hf.linear hu.1 hq' <;> obtain hG | hG := hg.linear hu.1 hq' <;>
    simp only [hF t ht, hF u hu, hG t ht, hG u hu] <;>
    grind [mem_Ici.1 t.2, Subtype.coe_le_coe.2 hqt, Subtype.coe_le_coe.2 htu]

/-- The least `t` with `0 ≤ f t + g t`, computed from a set `s` containing the breakpoints of `f`
and `g`. The candidates are the points `q ∈ insert ⊥ s`, and the zeros `q - (f q + g q)` and
`q - (f q + g q) / 2` of `f + g` on the interval following `q`, if its slope there is `1` or `2`. -/
def crossingAux (f g : 𝔻≥-1 → Dyadic) (s : Finset 𝔻≥-1) : WithTop 𝔻≥-1 :=
  Finset.min <| ((insert ⊥ s).biUnion fun q ↦
    {q, projIci (-1) (q - (f q + g q)), projIci (-1) (q - .half * (f q + g q))}).filter
      fun t ↦ 0 ≤ f t + g t

theorem crossingAux_le_iff (hf : IsBreakSet s f) (hg : IsBreakSet s g) :
    crossingAux f g s ≤ t ↔ 0 ≤ f t + g t := by
  rw [crossingAux, Finset.min_eq_inf_withTop, Finset.inf_le_iff (WithTop.coe_lt_top t)]
  refine ⟨fun ⟨c, hc, hct⟩ ↦ (Finset.mem_filter.1 hc).2.trans
    ((hf.monotone.add hg.monotone) (WithTop.coe_le_coe.1 hct)), fun ht ↦ ?_⟩
  obtain ⟨q, hq, hqt, hd⟩ := exists_extend (s := s) (Ioo_self t ▸ disjoint_empty _)
  suffices ∃ x ∈ ({q, projIci (-1) (q - (f q + g q)), projIci (-1) (q - .half * (f q + g q))} :
      Finset 𝔻≥-1), x ≤ t ∧ 0 ≤ f x + g x by
    obtain ⟨x, hx, hxt, h0⟩ := this
    exact ⟨x, Finset.mem_filter.2 ⟨Finset.mem_biUnion.2 ⟨q, hq, hx⟩, h0⟩, WithTop.coe_le_coe.2 hxt⟩
  by_cases hq0 : 0 ≤ f q + g q
  · exact ⟨q, by simp, hqt, hq0⟩
  have hm : Dyadic.half * (f q + g q) + .half * (f q + g q) = f q + g q := by
    rw [← add_mul, show Dyadic.half + .half = 1 by decide, one_mul]
  have : (q : Dyadic) ≤ t := hqt
  have key (x : Dyadic) (hqx : q < x) (hxt : x ≤ t)
      (h : ∀ y ∈ Icc q t, (y : Dyadic) = x → 0 ≤ f y + g y) :
      projIci (-1) x ≤ t ∧ 0 ≤ f (projIci (-1) x) + g (projIci (-1) x) := by
    have := q.2
    have hI : projIci (-1) x ∈ Icc q t := by
      simp only [mem_Icc, ← Subtype.coe_le_coe, coe_projIci]; grind
    exact ⟨hI.2, h _ hI (max_eq_right (by grind))⟩
  obtain hF | hF := hf.linear hqt hd <;> obtain hG | hG := hg.linear hqt hd <;>
    have := hF t ⟨hqt, le_rfl⟩ <;> have := hG t ⟨hqt, le_rfl⟩ <;>
    first
    | linarith
    | exact ⟨_, by simp, key (q - (f q + g q)) (by linarith) (by linarith)
        fun y hy hyx ↦ by rw [hF y hy, hG y hy]; linarith⟩
    | exact ⟨_, by simp, key (q - .half * (f q + g q)) (by linarith) (by linarith)
        fun y hy hyx ↦ by rw [hF y hy, hG y hy]; linarith⟩

end Trajectory

/-- A continuous piecewise linear function `𝔻≥-1 → Dyadic` with slopes `0` or `1`. -/
structure Trajectory where
  /-- The underlying function. -/
  toFun : 𝔻≥-1 → Dyadic
  /-- A finite set containing every breakpoint of the trajectory. -/
  breaks : Trunc {s : Finset 𝔻≥-1 // Trajectory.IsBreakSet s toFun}

namespace Trajectory

variable {f g : Trajectory} {t : 𝔻≥-1}

instance : FunLike Trajectory 𝔻≥-1 Dyadic where
  coe := toFun
  coe_injective := by rintro ⟨⟩ ⟨⟩ rfl; congr; exact Subsingleton.elim ..

@[simp] theorem coe_mk (f h) : ⇑(mk f h) = f := rfl

@[ext]
protected theorem ext (h : ∀ t, f t = g t) : f = g :=
  DFunLike.coe_injective (funext h)

protected theorem monotone (f : Trajectory) : Monotone f :=
  f.breaks.out.2.monotone

/-- A common set of breakpoints for two trajectories. -/
def breaks₂ (f g : Trajectory) : Trunc {s // IsBreakSet s f ∧ IsBreakSet s g} :=
  f.breaks.bind fun s ↦ g.breaks.map fun s' ↦
    ⟨s.1 ∪ s'.1, s.2.mono Finset.subset_union_left, s'.2.mono Finset.subset_union_right⟩

/-! ### Basic trajectories -/

/-- The constant trajectory. -/
def const (c : Dyadic) : Trajectory where
  toFun _ := c
  breaks := .mk ⟨∅, fun _ _ _ _ ↦ .inl rfl⟩

@[simp] theorem const_apply (c : Dyadic) (t : 𝔻≥-1) : const c t = c := rfl

/-- The trajectory `t ↦ t - f t`. This swaps the slopes `0` and `1`. -/
def reflect (f : Trajectory) : Trajectory where
  toFun t := t - f t
  breaks := f.breaks.map fun s ↦ ⟨s.1, s.2.reflect⟩

@[simp] theorem reflect_apply (f : Trajectory) (t : 𝔻≥-1) : reflect f t = t - f t := rfl

@[simp]
theorem reflect_reflect (f : Trajectory) : reflect (reflect f) = f := by
  ext; simp

theorem apply_le_apply_add {t u : 𝔻≥-1} (f : Trajectory) (h : t ≤ u) : f u ≤ f t + (u - t) := by
  linarith [f.reflect.monotone h, reflect_apply f t, reflect_apply f u]

/-! ### Lattice structure -/

instance : Min Trajectory where
  min f g := ⟨fun t ↦ min (f t) (g t), (breaks₂ f g).map fun s ↦ ⟨_, s.2.1.min s.2.2⟩⟩

instance : Max Trajectory where
  max f g := reflect (min (reflect f) (reflect g))

@[simp] theorem inf_apply (f g : Trajectory) (t : 𝔻≥-1) : (f ⊓ g) t = min (f t) (g t) := rfl

@[simp]
theorem sup_apply (f g : Trajectory) (t : 𝔻≥-1) : (f ⊔ g) t = max (f t) (g t) :=
  (congrArg ((t : Dyadic) - ·) (min_sub_sub_left ..)).trans (sub_sub_cancel ..)

instance : PartialOrder Trajectory :=
  .lift _ DFunLike.coe_injective

theorem le_def : f ≤ g ↔ ∀ t, f t ≤ g t := .rfl

instance : DistribLattice Trajectory :=
  DFunLike.coe_injective.distribLattice _ .rfl .rfl
    (fun f g ↦ funext (sup_apply f g)) (fun f g ↦ funext (inf_apply f g))

theorem inf'_apply {ι : Type*} {s : Finset ι} (H : s.Nonempty) (f : ι → Trajectory) (t : 𝔻≥-1) :
    s.inf' H f t = s.inf' H (f · t) :=
  Finset.apply_inf'_eq_inf'_comp H (fun f : Trajectory ↦ f t) fun _ _ ↦ rfl

@[simp]
theorem reflect_le_reflect : reflect f ≤ reflect g ↔ g ≤ f :=
  forall_congr' fun _ ↦ sub_le_sub_iff_left _

@[simp]
theorem reflect_sup (f g : Trajectory) : reflect (f ⊔ g) = reflect f ⊓ reflect g :=
  reflect_reflect _

@[simp]
theorem reflect_inf (f g : Trajectory) : reflect (f ⊓ g) = reflect f ⊔ reflect g := by
  ext; simp [max_sub_sub_left]

/-! ### Intermediate value theorem -/

/-- The least `t` with `0 ≤ f t + g t`, or `⊤` if there is none. -/
def crossing (f g : Trajectory) : WithTop 𝔻≥-1 :=
  (breaks₂ f g).lift (crossingAux f g ·.1) fun s s' ↦ eq_of_forall_ge_iff fun c ↦ by
    induction c using WithTop.recTopCoe <;>
      simp [crossingAux_le_iff s.2.1 s.2.2, crossingAux_le_iff s'.2.1 s'.2.2]

theorem crossing_le_iff : crossing f g ≤ t ↔ 0 ≤ f t + g t := by
  unfold crossing
  induction breaks₂ f g using Trunc.ind with | _ s => exact crossingAux_le_iff s.2.1 s.2.2

theorem crossing_comm (f g : Trajectory) : crossing f g = crossing g f :=
  eq_of_forall_ge_iff fun t ↦ by
    induction t using WithTop.recTopCoe <;> simp [crossing_le_iff, add_comm]

/-- If `f + g` starts out nonpositive, it vanishes where it first becomes nonnegative. -/
theorem add_eq_zero_of_crossing_eq (h : crossing f g = t) (h₀ : f ⊥ + g ⊥ ≤ 0) :
    f t + g t = 0 := by
  refine le_antisymm (not_lt.1 fun hpos ↦ ?_) (crossing_le_iff.1 h.le)
  obtain rfl | ht := eq_bot_or_bot_lt t
  · linarith
  have hm : Dyadic.half * (f t + g t) + .half * (f t + g t) = f t + g t := by
    rw [← add_mul, show Dyadic.half + .half = 1 by decide, one_mul]
  set s := projIci (-1) (t - .half * (f t + g t))
  have hs : (s : Dyadic) = max (-1) (t - .half * (f t + g t)) := coe_projIci ..
  have hst : s < t := by
    rw [← Subtype.coe_lt_coe, hs]
    exact max_lt (Subtype.coe_lt_coe.2 ht) (by linarith)
  refine (crossing_le_iff.2 ?_).not_gt (h ▸ WithTop.coe_lt_coe.2 hst)
  linarith [f.apply_le_apply_add hst.le, g.apply_le_apply_add hst.le,
    le_max_right (-1 : Dyadic) (t - .half * (f t + g t))]

/-- The trajectory `t ↦ f (min t τ)`, which follows `f` until time `τ`, and is then constant. -/
def freeze (f : Trajectory) : WithTop 𝔻≥-1 → Trajectory
  | ⊤ => f
  | (τ : 𝔻≥-1) => f ⊓ const (f τ)

@[simp] theorem freeze_top (f : Trajectory) : f.freeze ⊤ = f := rfl

theorem freeze_apply (f : Trajectory) (τ t : 𝔻≥-1) : f.freeze τ t = f (min t τ) :=
  (f.monotone.map_min ..).symm

@[simp]
theorem freeze_apply_bot (f : Trajectory) (τ : WithTop 𝔻≥-1) : f.freeze τ ⊥ = f ⊥ := by
  induction τ using WithTop.recTopCoe <;> simp [freeze_apply]

@[simp]
theorem crossing_freeze (f g : Trajectory) :
    crossing (f.freeze (crossing f g)) (g.freeze (crossing f g)) = crossing f g := by
  generalize h : crossing f g = c
  induction c using WithTop.recTopCoe with
  | top => exact h
  | coe τ =>
    refine eq_of_forall_ge_iff fun c ↦ ?_
    induction c using WithTop.recTopCoe with
    | top => simp
    | coe t =>
      rw [crossing_le_iff, freeze_apply, freeze_apply, WithTop.coe_le_coe]
      obtain ht | ht := le_total t τ
      · rw [min_eq_left ht, ← crossing_le_iff, h, WithTop.coe_le_coe]
      · simpa [min_eq_right ht, ht] using crossing_le_iff.1 h.le

-- The scaffolds of `⋆` meet at `0`, and those of `½` at `-½`.
example : crossing (reflect (const 0)) (reflect (const 0)) = ↑(⟨0, by decide⟩ : 𝔻≥-1) := rfl
example : crossing (reflect (const (-1))) (reflect (const 0)) = ↑(⟨-.half, by decide⟩ : 𝔻≥-1) :=
  rfl

end Trajectory

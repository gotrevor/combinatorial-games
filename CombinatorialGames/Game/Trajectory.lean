/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
module

public import CombinatorialGames.Mathlib.Dyadic
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Finset.Union
public import Mathlib.Data.Quot
public import Mathlib.Order.Interval.Set.ProjIcc
public import Mathlib.Order.LatticeIntervals

/-!
# Trajectories

A trajectory is a continuous piecewise linear function `𝔻≥-1 → Dyadic` with finitely many
breakpoints, whose slopes are all `0` or `1`. These are the building blocks of the left and right
walls of a short game (Siegel, *Combinatorial Game Theory*, pp. 106-107).

Trajectories form a distributive lattice under pointwise `min` and `max`, and are closed under the
reflection `t ↦ t - f t`, which swaps the slopes `0` and `1`. Since a sum `f + g` of two trajectories
has slopes `0`, `1` or `2`, the least `t` with `0 ≤ f t + g t` is dyadic; we compute it as
`Trajectory.crossing`.

## Implementation notes

A trajectory is stored as its underlying function, together with a finite set of points which
contains its breakpoints. This set is wrapped in `Trunc`, so that trajectories with the same values
are equal, while the breakpoints remain available to computations such as `Trajectory.crossing`.
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
  coe_injective := by
    rintro ⟨f, s⟩ ⟨g, s'⟩ rfl
    rw [Subsingleton.elim s s']

@[simp] theorem coe_mk (f h) : ⇑(mk f h) = f := rfl

@[ext]
protected theorem ext (h : ∀ t, f t = g t) : f = g :=
  DFunLike.coe_injective (funext h)

protected theorem monotone (f : Trajectory) : Monotone f :=
  sorry

/-! ### Basic trajectories -/

/-- The constant trajectory. -/
def const (c : Dyadic) : Trajectory where
  toFun _ := c
  breaks := .mk ⟨∅, fun _ _ _ _ ↦ .inl rfl⟩

@[simp] theorem const_apply (c : Dyadic) (t : 𝔻≥-1) : const c t = c := rfl

/-- The trajectory `t ↦ t - f t`. This swaps the slopes `0` and `1`. -/
def reflect (f : Trajectory) : Trajectory where
  toFun t := t - f t
  breaks := f.breaks.map fun s ↦ ⟨s, sorry⟩

@[simp] theorem reflect_apply (f : Trajectory) (t : 𝔻≥-1) : reflect f t = t - f t := rfl

@[simp]
theorem reflect_reflect (f : Trajectory) : reflect (reflect f) = f := by
  ext; simp

/-! ### Lattice structure -/

instance : Min Trajectory where
  min f g := {
    toFun t := min (f t) (g t)
    -- Where `f` and `g` are linear with distinct slopes, they can only cross at `q ± (f q - g q)`.
    breaks := f.breaks.bind fun s ↦ g.breaks.map fun s' ↦
      ⟨s.1 ∪ s'.1 ∪ (insert ⊥ (s.1 ∪ s'.1)).biUnion fun q ↦
        {projIci (-1) (q + (f q - g q)), projIci (-1) (q - (f q - g q))}, sorry⟩ }

instance : Max Trajectory where
  max f g := reflect (min (reflect f) (reflect g))

@[simp] theorem inf_apply (f g : Trajectory) (t : 𝔻≥-1) : (f ⊓ g) t = min (f t) (g t) := rfl

@[simp]
theorem sup_apply (f g : Trajectory) (t : 𝔻≥-1) : (f ⊔ g) t = max (f t) (g t) :=
  sorry

instance : PartialOrder Trajectory :=
  .lift _ DFunLike.coe_injective

theorem le_def : f ≤ g ↔ ∀ t, f t ≤ g t := .rfl

instance : DistribLattice Trajectory :=
  DFunLike.coe_injective.distribLattice _ .rfl .rfl
    (fun f g ↦ funext (sup_apply f g)) (fun f g ↦ funext (inf_apply f g))

@[simp]
theorem reflect_le_reflect : reflect f ≤ reflect g ↔ g ≤ f :=
  sorry

@[simp]
theorem reflect_inf (f g : Trajectory) : reflect (f ⊓ g) = reflect f ⊔ reflect g :=
  sorry

@[simp]
theorem reflect_sup (f g : Trajectory) : reflect (f ⊔ g) = reflect f ⊓ reflect g :=
  sorry

/-! ### Intermediate value theorem -/

/-- The least `t` with `0 ≤ f t + g t`, or `⊤` if there is none.

On an interval where `f + g` is linear with slope `1` or `2`, its zero is at `q - (f q + g q)` or
`q - (f q + g q) / 2`. -/
def crossing (f g : Trajectory) : WithTop 𝔻≥-1 :=
  f.breaks.lift (fun s ↦ g.breaks.lift (fun s' ↦ Finset.min <|
    (insert ⊥ ((insert ⊥ (s.1 ∪ s'.1)).biUnion fun q ↦
      {projIci (-1) (q - (f q + g q)), projIci (-1) (q - .half * (f q + g q))})).filter
        (fun t ↦ 0 ≤ f t + g t)) sorry) sorry

theorem crossing_le_iff : crossing f g ≤ t ↔ 0 ≤ f t + g t :=
  sorry

-- The scaffolds of `⋆` meet at `0`, and those of `½` at `-½`.
example : crossing (reflect (const 0)) (reflect (const 0)) = ↑(⟨0, by decide⟩ : 𝔻≥-1) := rfl
example : crossing (reflect (const (-1))) (reflect (const 0)) = ↑(⟨-.half, by decide⟩ : 𝔻≥-1) :=
  rfl

end Trajectory

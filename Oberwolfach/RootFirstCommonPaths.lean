module

public import Oberwolfach.RootFirstMarkedCycles

@[expose] public section

/-! Common-path tuples with the manuscript's root-first order. Their
coordinates and the four separately supplied root spokes are unchanged. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V U E K : Type*} {tail head : E → V} {ktail khead : K → V}
    {m : ℕ} {π : Equiv.Perm V} {b : ℕ} {H₀ Hₖ : V → U → Prop}

def rootFirstSpokeType (m : ℕ) (j : Bool) (t : Fin (m+1)) : Bool :=
  decide (t=if j then 0 else 3)

theorem markedRootOrder_position_type (m : ℕ) (j : Bool) (t : Fin (m+1)) :
    markedPositionType ((markedRootOrder m j).symm t)=rootFirstSpokeType m j t := by
  have he : (markedRootOrder m j).symm t=0 ↔ t=markedRootOrder m j 0 := by
    constructor
    · intro h
      have hh := congrArg (markedRootOrder m j) h
      simpa only [Equiv.apply_symm_apply] using hh
    · intro h
      rw [h,Equiv.symm_apply_apply]
  unfold markedPositionType rootFirstSpokeType
  simp only [he]
  cases j
  · rw [markedRootOrder_marked_head];rfl
  · rfl

abbrev RootFirstCommonMarkedPath (tail head : E → V) (ktail khead : K → V)
    (m : ℕ) (π : Equiv.Perm V) (b : ℕ) (H₀ Hₖ : V → U → Prop)
    (j : Bool) (v v' : V) (u u' : U) :=
  {z : Fin m → V //
    IsRootFirstMarkedCycle tail head ktail khead m π b
      (if j then Fin.last m else 2) (Fin.cases v z) ∧
    IsRootFirstMarkedCycle tail head ktail khead m π b
      (if j then Fin.last m else 2) (Fin.cases v' z) ∧
    ∀ l : Fin m,
      (if rootFirstSpokeType m j l.succ then Hₖ (z l) u else H₀ (z l) u) ∧
      (if rootFirstSpokeType m j l.succ then Hₖ (z l) u' else H₀ (z l) u')}

def rootFirstCommonMarkedPathEquiv (j : Bool) (v v' : V) (u u' : U) :
    RootFirstCommonMarkedPath tail head ktail khead m π b H₀ Hₖ j v v' u u' ≃
      OrderedCommonMarkedPath tail head ktail khead m π b H₀ Hₖ
        (markedRootOrder m j) v v' u u' :=
  Equiv.subtypeEquivRight (fun z=>by
    simp only [rootedCycleOrder_marked_iff,markedRootOrder_position_type])

theorem rootFirstCommonMarkedPath_card_le [Fintype V]
    (hm : 3<m+1) (j : Bool) (v v' : V) (u u' : U)
    (hroot : (if j then Hₖ v u else H₀ v u) ∧ (if j then Hₖ v u' else H₀ v u') ∧
      (if j then Hₖ v' u else H₀ v' u) ∧ (if j then Hₖ v' u' else H₀ v' u')) :
    Fintype.card (RootFirstCommonMarkedPath tail head ktail khead m π b H₀ Hₖ j v v' u u')≤
      Fintype.card (MarkedReplacementPair tail head ktail khead m π b H₀ Hₖ
        ((markedRootOrder m j).symm 0) v v' u u') := by
  rw [Fintype.card_congr (rootFirstCommonMarkedPathEquiv j v v' u u')]
  apply orderedCommonMarkedPath_card_le
  simpa only [markedRootOrder_type m hm j] using hroot

theorem rootFirstCommonMarkedPath_labels (j : Bool) (v v' : V) (u u' : U)
    (z : RootFirstCommonMarkedPath tail head ktail khead m π b H₀ Hₖ j v v' u u') :
    Function.Injective z.val ∧ (∀ l,z.val l≠v ∧ z.val l≠v') := by
  have hv := permutationSeparated_injective π b _ z.property.1.1
  have hv' := permutationSeparated_injective π b _ z.property.2.1.1
  constructor
  · intro l k he
    apply Fin.succ_injective
    exact hv he
  · intro l
    constructor
    · intro he
      have hh := hv (show Fin.cases (motive:=fun _=>V) v z.val l.succ=Fin.cases (motive:=fun _=>V) v z.val 0 from he)
      exact Fin.succ_ne_zero l hh
    · intro he
      have hh := hv' (show Fin.cases (motive:=fun _=>V) v' z.val l.succ=Fin.cases (motive:=fun _=>V) v' z.val 0 from he)
      exact Fin.succ_ne_zero l hh

end Oberwolfach

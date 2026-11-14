module

public import Oberwolfach.MarkedReplacementPairs
public import Mathlib.Data.Fin.Tuple.Basic

@[expose] public section

/-! Common paths in canonical cycle coordinates. The free tuple omits the
root position. Its spoke conditions omit all four root spokes; those are
supplied separately by the four-cycle being corrected. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem markedHubCompatible_iff_positions {V U : Type*} {m : ℕ}
    (H₀ Hₖ : V → U → Prop) (C : Fin (m+1) → V) (u : U) :
    MarkedHubCompatible H₀ Hₖ C u ↔
      ∀ i,if markedPositionType i then Hₖ (C i) u else H₀ (C i) u := by
  constructor
  · intro h i
    refine Fin.cases ?_ (fun k=>?_) i
    · simpa only [markedPositionType,decide_true,ite_true] using h.1
    · simpa only [markedPositionType,Fin.succ_ne_zero,decide_false,Bool.false_eq_true,ite_false] using h.2 k
  · intro h
    constructor
    · simpa only [markedPositionType,decide_true,ite_true] using h 0
    · intro k
      simpa only [markedPositionType,Fin.succ_ne_zero,decide_false,Bool.false_eq_true,ite_false] using h k.succ

abbrev CanonicalCommonMarkedPath {V U E K : Type*}
    (tail head : E → V) (ktail khead : K → V) (m : ℕ) (π : Equiv.Perm V) (b : ℕ)
    (H₀ Hₖ : V → U → Prop) (i : Fin (m+1)) (v v' : V) (u u' : U) :=
  {z : Fin m → V //
    IsMarkedCycleTuple tail head ktail khead m π b (Fin.insertNth (α:=fun _=>V) i v z) ∧
    IsMarkedCycleTuple tail head ktail khead m π b (Fin.insertNth (α:=fun _=>V) i v' z) ∧
    ∀ k : Fin m,
      (if markedPositionType (i.succAbove k) then Hₖ (z k) u else H₀ (z k) u) ∧
      (if markedPositionType (i.succAbove k) then Hₖ (z k) u' else H₀ (z k) u')}

def canonicalCommonMarkedPath_to_pair {V U E K : Type*}
    {tail head : E → V} {ktail khead : K → V} {m : ℕ} {π : Equiv.Perm V} {b : ℕ}
    {H₀ Hₖ : V → U → Prop} {i : Fin (m+1)} {v v' : V} {u u' : U}
    (hroot : (if markedPositionType i then Hₖ v u else H₀ v u) ∧
      (if markedPositionType i then Hₖ v u' else H₀ v u') ∧
      (if markedPositionType i then Hₖ v' u else H₀ v' u) ∧
      (if markedPositionType i then Hₖ v' u' else H₀ v' u')) :
    CanonicalCommonMarkedPath tail head ktail khead m π b H₀ Hₖ i v v' u u' ↪
      MarkedReplacementPair tail head ktail khead m π b H₀ Hₖ i v v' u u' where
  toFun z := by
    have hcompat (w : V) (h : U)
        (hr : if markedPositionType i then Hₖ w h else H₀ w h)
        (hf : ∀ k : Fin m,if markedPositionType (i.succAbove k) then Hₖ (z.val k) h else H₀ (z.val k) h) :
        MarkedHubCompatible H₀ Hₖ (Fin.insertNth (α:=fun _=>V) i w z.val) h := by
      apply (markedHubCompatible_iff_positions _ _ _ _).mpr
      intro k
      by_cases hk : k=i
      · subst k;simpa only [Fin.insertNth_apply_same] using hr
      · obtain ⟨l,rfl⟩ := Fin.exists_succAbove_eq hk
        simpa only [Fin.insertNth_apply_succAbove] using hf l
    refine ⟨⟨⟨Fin.insertNth (α:=fun _=>V) i v z.val,z.property.1⟩,⟨Fin.insertNth (α:=fun _=>V) i v' z.val,z.property.2.1⟩⟩,
      Fin.insertNth_apply_same (α:=fun _=>V) i v z.val,Fin.insertNth_apply_same (α:=fun _=>V) i v' z.val,?_,
      hcompat v u hroot.1 (fun k=>(z.property.2.2 k).1),
      hcompat v u' hroot.2.1 (fun k=>(z.property.2.2 k).2),
      hcompat v' u hroot.2.2.1 (fun k=>(z.property.2.2 k).1),
      hcompat v' u' hroot.2.2.2 (fun k=>(z.property.2.2 k).2)⟩
    intro k hk
    obtain ⟨l,rfl⟩ := Fin.exists_succAbove_eq hk
    simp only [Fin.insertNth_apply_succAbove]
  inj' z w he := by
    apply Subtype.ext
    have hc := congrArg (fun P=>P.val.1.val) he
    have he' : Fin.insertNth (α:=fun _=>V) i v z.val=Fin.insertNth (α:=fun _=>V) i v w.val := hc
    exact (Fin.insertNth_inj (α:=fun _=>V) |>.mp he').2

theorem canonicalCommonMarkedPath_card_le {V U E K : Type*} [Fintype V]
    {tail head : E → V} {ktail khead : K → V} {m : ℕ} {π : Equiv.Perm V} {b : ℕ}
    {H₀ Hₖ : V → U → Prop} {i : Fin (m+1)} {v v' : V} {u u' : U}
    (hroot : (if markedPositionType i then Hₖ v u else H₀ v u) ∧
      (if markedPositionType i then Hₖ v u' else H₀ v u') ∧
      (if markedPositionType i then Hₖ v' u else H₀ v' u) ∧
      (if markedPositionType i then Hₖ v' u' else H₀ v' u')) :
    Fintype.card (CanonicalCommonMarkedPath tail head ktail khead m π b H₀ Hₖ i v v' u u')≤
      Fintype.card (MarkedReplacementPair tail head ktail khead m π b H₀ Hₖ i v v' u u') :=
  Fintype.card_le_of_injective _ (canonicalCommonMarkedPath_to_pair hroot).injective

end Oberwolfach

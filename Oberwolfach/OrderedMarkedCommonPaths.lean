module

public import Oberwolfach.MarkedCommonPaths

@[expose] public section

/-! Root-first ordered tuples and their conversion to canonical cycle
coordinates. The four root spokes are supplied only at the consumer.
Additional physical restrictions can be imposed by taking a subfamily. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def rootedCycleOrder {V : Type*} {m : ℕ} (σ : Equiv.Perm (Fin (m+1))) (v : V)
    (z : Fin m → V) : Fin (m+1) → V := fun k=>Fin.cases v z (σ k)

abbrev OrderedCommonMarkedPath {V U E K : Type*}
    (tail head : E → V) (ktail khead : K → V) (m : ℕ) (π : Equiv.Perm V) (b : ℕ)
    (H₀ Hₖ : V → U → Prop) (σ : Equiv.Perm (Fin (m+1))) (v v' : V) (u u' : U) :=
  {z : Fin m → V //
    IsMarkedCycleTuple tail head ktail khead m π b (rootedCycleOrder σ v z) ∧
    IsMarkedCycleTuple tail head ktail khead m π b (rootedCycleOrder σ v' z) ∧
    ∀ l : Fin m,
      (if markedPositionType (σ.symm l.succ) then Hₖ (z l) u else H₀ (z l) u) ∧
      (if markedPositionType (σ.symm l.succ) then Hₖ (z l) u' else H₀ (z l) u')}

def orderedCommonMarkedPath_to_pair {V U E K : Type*}
    {tail head : E → V} {ktail khead : K → V} {m : ℕ} {π : Equiv.Perm V} {b : ℕ}
    {H₀ Hₖ : V → U → Prop} {σ : Equiv.Perm (Fin (m+1))} {v v' : V} {u u' : U}
    (hroot : (if markedPositionType (σ.symm 0) then Hₖ v u else H₀ v u) ∧
      (if markedPositionType (σ.symm 0) then Hₖ v u' else H₀ v u') ∧
      (if markedPositionType (σ.symm 0) then Hₖ v' u else H₀ v' u) ∧
      (if markedPositionType (σ.symm 0) then Hₖ v' u' else H₀ v' u')) :
    OrderedCommonMarkedPath tail head ktail khead m π b H₀ Hₖ σ v v' u u' ↪
      MarkedReplacementPair tail head ktail khead m π b H₀ Hₖ (σ.symm 0) v v' u u' where
  toFun z := by
    have hcompat (w : V) (h : U)
        (hr : if markedPositionType (σ.symm 0) then Hₖ w h else H₀ w h)
        (hf : ∀ l : Fin m,if markedPositionType (σ.symm l.succ) then Hₖ (z.val l) h else H₀ (z.val l) h) :
        MarkedHubCompatible H₀ Hₖ (rootedCycleOrder σ w z.val) h := by
      apply (markedHubCompatible_iff_positions _ _ _ _).mpr
      intro k
      have hk := Fin.eq_zero_or_eq_succ (σ k)
      rcases hk with hk|⟨l,hl⟩
      · have hk' : k=σ.symm 0 := σ.injective (by simpa only [Equiv.apply_symm_apply] using hk)
        subst k
        simpa only [rootedCycleOrder,Equiv.apply_symm_apply,Fin.cases_zero] using hr
      · have hk' : k=σ.symm l.succ := σ.injective (by simpa only [Equiv.apply_symm_apply] using hl)
        subst k
        simpa only [rootedCycleOrder,Equiv.apply_symm_apply,Fin.cases_succ] using hf l
    refine ⟨⟨⟨rootedCycleOrder σ v z.val,z.property.1⟩,⟨rootedCycleOrder σ v' z.val,z.property.2.1⟩⟩,
      ?_,?_,?_,hcompat v u hroot.1 (fun l=>(z.property.2.2 l).1),
      hcompat v u' hroot.2.1 (fun l=>(z.property.2.2 l).2),
      hcompat v' u hroot.2.2.1 (fun l=>(z.property.2.2 l).1),
      hcompat v' u' hroot.2.2.2 (fun l=>(z.property.2.2 l).2)⟩
    · simp only [rootedCycleOrder,Equiv.apply_symm_apply,Fin.cases_zero]
    · simp only [rootedCycleOrder,Equiv.apply_symm_apply,Fin.cases_zero]
    · intro k hk
      have hσ : σ k≠0 := by intro he;exact hk (σ.injective (by simpa only [Equiv.apply_symm_apply] using he))
      obtain ⟨l,hl⟩ := Fin.eq_succ_of_ne_zero hσ
      simp only [rootedCycleOrder,hl,Fin.cases_succ]
  inj' z w he := by
    apply Subtype.ext
    funext l
    have hc := congrArg (fun P=>P.val.1.val (σ.symm l.succ)) he
    simpa only [rootedCycleOrder,Equiv.apply_symm_apply,Fin.cases_succ] using hc

theorem orderedCommonMarkedPath_card_le {V U E K : Type*} [Fintype V]
    {tail head : E → V} {ktail khead : K → V} {m : ℕ} {π : Equiv.Perm V} {b : ℕ}
    {H₀ Hₖ : V → U → Prop} {σ : Equiv.Perm (Fin (m+1))} {v v' : V} {u u' : U}
    (hroot : (if markedPositionType (σ.symm 0) then Hₖ v u else H₀ v u) ∧
      (if markedPositionType (σ.symm 0) then Hₖ v u' else H₀ v u') ∧
      (if markedPositionType (σ.symm 0) then Hₖ v' u else H₀ v' u) ∧
      (if markedPositionType (σ.symm 0) then Hₖ v' u' else H₀ v' u')) :
    Fintype.card (OrderedCommonMarkedPath tail head ktail khead m π b H₀ Hₖ σ v v' u u')≤
      Fintype.card (MarkedReplacementPair tail head ktail khead m π b H₀ Hₖ (σ.symm 0) v v' u u') :=
  Fintype.card_le_of_injective _ (orderedCommonMarkedPath_to_pair hroot).injective

end Oberwolfach

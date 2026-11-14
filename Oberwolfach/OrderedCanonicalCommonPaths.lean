module

public import Oberwolfach.RootFirstCommonPaths

@[expose] public section

/-! Reindexing common paths before supplying any root spokes. This preserves
all free coordinates and proves the cardinality comparison needed when the
numerical manuscript input is stated in root-first coordinates. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V U E K : Type*} {tail head : E → V} {ktail khead : K → V}
  {m : ℕ} {π : Equiv.Perm V} {b : ℕ} {H₀ Hₖ : V → U → Prop}

theorem rootedCycleOrder_reinsert (σ : Equiv.Perm (Fin (m+1))) (v w : V) (z : Fin m → V) :
    Fin.insertNth (α:=fun _=>V) (σ.symm 0) w
      (fun k=>rootedCycleOrder σ v z ((σ.symm 0).succAbove k))=rootedCycleOrder σ w z := by
  funext a
  by_cases ha : a=σ.symm 0
  · subst a
    simp only [Fin.insertNth_apply_same,rootedCycleOrder,Equiv.apply_symm_apply,Fin.cases_zero]
  · obtain ⟨k,rfl⟩ := Fin.exists_succAbove_eq ha
    rw [Fin.insertNth_apply_succAbove]
    have hs : σ ((σ.symm 0).succAbove k)≠0 := by
      intro he
      have hh := congrArg σ.symm he
      rw [Equiv.symm_apply_apply] at hh
      exact Fin.succAbove_ne _ _ hh
    obtain ⟨l,hl⟩ := Fin.eq_succ_of_ne_zero hs
    simp only [rootedCycleOrder,hl,Fin.cases_succ]

def orderedCommonMarkedPath_to_canonical
    (σ : Equiv.Perm (Fin (m+1))) (v v' : V) (u u' : U) :
    OrderedCommonMarkedPath tail head ktail khead m π b H₀ Hₖ σ v v' u u' ↪
      CanonicalCommonMarkedPath tail head ktail khead m π b H₀ Hₖ (σ.symm 0) v v' u u' where
  toFun z := by
    refine ⟨fun k=>rootedCycleOrder σ v z.val ((σ.symm 0).succAbove k),?_,?_,?_⟩
    · rw [rootedCycleOrder_reinsert]
      exact z.property.1
    · rw [rootedCycleOrder_reinsert]
      exact z.property.2.1
    · intro k
      have hs : σ ((σ.symm 0).succAbove k)≠0 := by
        intro he
        have hh := congrArg σ.symm he
        rw [Equiv.symm_apply_apply] at hh
        exact Fin.succAbove_ne _ _ hh
      obtain ⟨l,hl⟩ := Fin.eq_succ_of_ne_zero hs
      have hk : (σ.symm 0).succAbove k=σ.symm l.succ := by
        apply σ.injective
        simpa only [Equiv.apply_symm_apply] using hl
      simp only [hk,rootedCycleOrder,Equiv.apply_symm_apply,Fin.cases_succ]
      exact z.property.2.2 l
  inj' z w he := by
    apply Subtype.ext
    have hf := congrArg Subtype.val he
    have hi := congrArg (Fin.insertNth (α:=fun _=>V) (σ.symm 0) v) hf
    change Fin.insertNth (α:=fun _=>V) (σ.symm 0) v
        (fun k=>rootedCycleOrder σ v z.val ((σ.symm 0).succAbove k))=
      Fin.insertNth (α:=fun _=>V) (σ.symm 0) v
        (fun k=>rootedCycleOrder σ v w.val ((σ.symm 0).succAbove k)) at hi
    rw [rootedCycleOrder_reinsert,rootedCycleOrder_reinsert] at hi
    funext l
    have hh := congrFun hi (σ.symm l.succ)
    simpa only [rootedCycleOrder,Equiv.apply_symm_apply,Fin.cases_succ] using hh

theorem orderedCommonMarkedPath_canonical_card_le [Fintype V]
    (σ : Equiv.Perm (Fin (m+1))) (v v' : V) (u u' : U) :
    Fintype.card (OrderedCommonMarkedPath tail head ktail khead m π b H₀ Hₖ σ v v' u u')≤
      Fintype.card (CanonicalCommonMarkedPath tail head ktail khead m π b H₀ Hₖ (σ.symm 0) v v' u u') :=
  Fintype.card_le_of_injective _ (orderedCommonMarkedPath_to_canonical σ v v' u u').injective

theorem rootFirstCommonMarkedPath_canonical_card_le [Fintype V]
    (j : Bool) (v v' : V) (u u' : U) :
    Fintype.card (RootFirstCommonMarkedPath tail head ktail khead m π b H₀ Hₖ j v v' u u')≤
      Fintype.card (CanonicalCommonMarkedPath tail head ktail khead m π b H₀ Hₖ
        ((markedRootOrder m j).symm 0) v v' u u') := by
  rw [Fintype.card_congr (rootFirstCommonMarkedPathEquiv j v v' u u')]
  exact orderedCommonMarkedPath_canonical_card_le (markedRootOrder m j) v v' u u'

end Oberwolfach

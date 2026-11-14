module

public import Oberwolfach.MarkedCommonConfigurationSpokeChanges
public import Oberwolfach.SampledCommonMarkedPaths
public import Oberwolfach.CommonThinnedSpokeChanges

@[expose] public section

/-! The ordered surviving tuples with a fixed selector map injectively to
the actual common-cycle and root-first common-path families. The selector
is tested only at free ordinary labels; no root-spoke hypotheses are added. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color : Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

def selectedSpokes (H : Bool→V→U→Prop) (κ : V→Bool) (b : Bool) (v : V) (u : U) : Prop :=
  H b v u ∧ (b=false → κ v=true)

def commonSelectedClass (H : Bool→V→U→Prop) (κ : V→Bool) (u u' : U) (b : Bool) : Finset V :=
  Finset.univ.filter (fun v=>commonThinnedSpokes H κ u u' b v ())

theorem mem_commonSelectedClass (H : Bool→V→U→Prop) (κ : V→Bool) (u u' : U) (b : Bool) (v : V) :
    v∈commonSelectedClass H κ u u' b ↔ selectedSpokes H κ b v u ∧ selectedSpokes H κ b v u' := by
  simp only [commonSelectedClass,Finset.mem_filter,Finset.mem_univ,true_and,commonThinnedSpokes,selectedSpokes]
  tauto

variable (P : SimpleGraph V) (π : Equiv.Perm V) (d m : ℕ)
    (σ : RawMarkedOutcome V U Γ Color) (H : Bool→V→U→Prop) (κ : V→Bool) (u : Fin 2→U)

def selectedBase_to_common_cycle :
    {C : DenseMarkedBaseFamily P π (3*d) m
      (commonSelectedClass H κ (u 0) (u 1) false) (commonSelectedClass H κ (u 0) (u 1) true) //
        MarkedBaseRims P π (3*d) m (fun e=>σ (Sum.inl e)) C.val} ↪
      MarkedSampleCommonCycleWithSpokes P π d m σ (selectedSpokes H κ) u where
  toFun C := by
    refine ⟨⟨C.val.val,C.val.property.1,?_,?_⟩,?_,?_⟩
    · intro i
      exact ⟨⟨(C.val.val i.castSucc,C.val.val i.succ),C.property.1 i⟩,rfl,rfl⟩
    · exact ⟨⟨(C.val.val (Fin.last m),C.val.val 0),C.property.2⟩,rfl,rfl⟩
    · refine ⟨?_,fun k=>?_⟩
      · exact ((mem_commonSelectedClass H κ (u 0) (u 1) true _).mp C.val.property.2.1).1
      · exact ((mem_commonSelectedClass H κ (u 0) (u 1) false _).mp (C.val.property.2.2.1 k)).1
    · refine ⟨?_,fun k=>?_⟩
      · exact ((mem_commonSelectedClass H κ (u 0) (u 1) true _).mp C.val.property.2.1).2
      · exact ((mem_commonSelectedClass H κ (u 0) (u 1) false _).mp (C.val.property.2.2.1 k)).2
  inj' C D he := by
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun C : MarkedSampleCommonCycleWithSpokes P π d m σ (selectedSpokes H κ) u=>C.val.val) he

theorem selectedBase_card_le_common_cycle :
    Fintype.card {C : DenseMarkedBaseFamily P π (3*d) m
      (commonSelectedClass H κ (u 0) (u 1) false) (commonSelectedClass H κ (u 0) (u 1) true) //
        MarkedBaseRims P π (3*d) m (fun e=>σ (Sum.inl e)) C.val}≤
      Fintype.card (MarkedSampleCommonCycleWithSpokes P π d m σ (selectedSpokes H κ) u) :=
  Fintype.card_le_of_injective _ (selectedBase_to_common_cycle P π d m σ H κ u).injective

def selectedPath_to_common_path (hm : 2≤m) (j : Bool) (v v' : V) :
    {C : DenseRootMarkedPathFamily P π (3*d) m j
      (commonSelectedClass H κ (u 0) (u 1) false) (commonSelectedClass H κ (u 0) (u 1) true) v v' //
        MarkedPathRims P π (3*d) m j v v' (fun e=>σ (Sum.inl e)) C.val} ↪
      MarkedSampleCommonPathWithSpokes P π d m σ (selectedSpokes H κ) u j v v' where
  toFun C := by
    refine ⟨C.val.val,?_,?_,?_⟩
    · exact markedPathRims_rootCycle P π (3*d) m j v v' (fun e=>σ (Sum.inl e)) hm C.val.val false C.val.property.1 C.property
    · exact markedPathRims_rootCycle P π (3*d) m j v v' (fun e=>σ (Sum.inl e)) hm C.val.val true C.val.property.2.1 C.property
    · intro i
      rw [rootFirstSpokeType_free m hm j i]
      have hmem := C.val.property.2.2.1 i
      by_cases hc : j=false ∧ i.val=2
      · simp only [hc,ite_true,decide_true] at hmem ⊢
        exact (mem_commonSelectedClass H κ (u 0) (u 1) true _).mp hmem
      · simp only [hc,ite_false,decide_false,Bool.false_eq_true] at hmem ⊢
        exact (mem_commonSelectedClass H κ (u 0) (u 1) false _).mp hmem
  inj' C D he := by
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun C : MarkedSampleCommonPathWithSpokes P π d m σ (selectedSpokes H κ) u j v v'=>C.val) he

theorem selectedPath_card_le_common_path (hm : 2≤m) (j : Bool) (v v' : V) :
    Fintype.card {C : DenseRootMarkedPathFamily P π (3*d) m j
      (commonSelectedClass H κ (u 0) (u 1) false) (commonSelectedClass H κ (u 0) (u 1) true) v v' //
        MarkedPathRims P π (3*d) m j v v' (fun e=>σ (Sum.inl e)) C.val}≤
      Fintype.card (MarkedSampleCommonPathWithSpokes P π d m σ (selectedSpokes H κ) u j v v') :=
  Fintype.card_le_of_injective _ (selectedPath_to_common_path P π d m σ H κ u hm j v v').injective

end Oberwolfach

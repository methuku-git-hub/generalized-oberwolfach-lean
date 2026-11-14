module

public import Oberwolfach.RawMarkedBaseCycles
public import Oberwolfach.MarkedSampleArcs
public import Oberwolfach.MarkedCommonPaths

@[expose] public section

/-! The greedily counted surviving tuples embed into the common-cycle
family used by the marked correction. Both hub conditions are proved from
the actual pair classes, and the sampled arc types have their real endpoints. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V U Γ Color : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V) (π : Equiv.Perm V) (d m : ℕ)
    (σ : RawIntervalFamilyOutcome V U Γ Color) (τ : Sym2 V→Option (Bool×Bool))
    (g : Γ) (j : Color) (u : Fin 2→U)

abbrev SampledCommonMarkedCycle :=
  {C : MarkedCycleTuple
    (fun e : MarkedSampleArc P π (3*d) τ false=>e.val.1) (fun e=>e.val.2)
    (fun e : MarkedSampleArc P π (3*d) τ true=>e.val.1) (fun e=>e.val.2) m π (3*d) //
    ∀ i : Fin 2,MarkedHubCompatible (rawMarkedSpokes π d σ g j false)
      (rawMarkedSpokes π d σ g j true) C.val (u i)}

def survivingBase_to_common_cycle :
    {C : DenseMarkedBaseFamily P π (3*d) m
      (rawMarkedPairClass π d σ g j u false) (rawMarkedPairClass π d σ g j u true) //
        MarkedBaseRims P π (3*d) m τ C.val} ↪
      SampledCommonMarkedCycle P π d m σ τ g j u where
  toFun C := by
    refine ⟨⟨C.val.val,C.val.property.1,?_,?_⟩,?_⟩
    · intro i
      exact ⟨⟨(C.val.val i.castSucc,C.val.val i.succ),C.property.1 i⟩,rfl,rfl⟩
    · exact ⟨⟨(C.val.val (Fin.last m),C.val.val 0),C.property.2⟩,rfl,rfl⟩
    · intro i
      refine ⟨?_,fun k=>?_⟩
      · exact (Finset.mem_filter.mp C.val.property.2.1).2 i
      · exact (Finset.mem_filter.mp (C.val.property.2.2.1 k)).2 i
  inj' C D he := by
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun C : SampledCommonMarkedCycle P π d m σ τ g j u=>C.val.val) he

theorem survivingBase_card_le_common_cycle :
    Fintype.card {C : DenseMarkedBaseFamily P π (3*d) m
      (rawMarkedPairClass π d σ g j u false) (rawMarkedPairClass π d σ g j u true) //
        MarkedBaseRims P π (3*d) m τ C.val}≤
      Fintype.card (SampledCommonMarkedCycle P π d m σ τ g j u) :=
  Fintype.card_le_of_injective _ (survivingBase_to_common_cycle P π d m σ τ g j u).injective

end Oberwolfach

module

public import Oberwolfach.SampledMarkedPathCycles
public import Oberwolfach.RawMarkedBaseCycles
public import Oberwolfach.OrderedCanonicalCommonPaths

@[expose] public section

/-! Surviving free tuples enter the existing root-first and canonical
common-path families. No root-spoke presence is used by either map. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem rootFirstSpokeType_free (m : ℕ) (hm : 2≤m) (j : Bool) (i : Fin (m+1)) :
    rootFirstSpokeType (m+1) j i.succ=decide (j=false ∧ i.val=2) := by
  unfold rootFirstSpokeType
  cases j
  · congr 1
    apply propext
    simp only [Bool.false_eq_true,ite_false,true_and,Fin.ext_iff,Fin.val_succ,Fin.val_natCast]
    change i.val+1=3%(m+2) ↔ i.val=2
    rw [Nat.mod_eq_of_lt (show 3<m+2 by omega)]
    omega
  · simp [Fin.succ_ne_zero]

variable {V U Γ Color : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V) (π : Equiv.Perm V) (d m : ℕ) (j : Bool) (v v' : V)
    (σ : RawIntervalFamilyOutcome V U Γ Color) (τ : Sym2 V→Option (Bool×Bool))
    (g : Γ) (j₀ : Color) (u : Fin 2→U)

abbrev SampledCommonMarkedPath :=
  RootFirstCommonMarkedPath
    (fun e : MarkedSampleArc P π (3*d) τ false=>e.val.1) (fun e=>e.val.2)
    (fun e : MarkedSampleArc P π (3*d) τ true=>e.val.1) (fun e=>e.val.2) (m+1) π (3*d)
    (rawMarkedSpokes π d σ g j₀ false) (rawMarkedSpokes π d σ g j₀ true) j v v' (u 0) (u 1)

def survivingPath_to_common_path (hm : 2≤m) :
    {C : DenseRootMarkedPathFamily P π (3*d) m j
      (rawMarkedPairClass π d σ g j₀ u false) (rawMarkedPairClass π d σ g j₀ u true) v v' //
        MarkedPathRims P π (3*d) m j v v' τ C.val} ↪
      SampledCommonMarkedPath P π d m j v v' σ τ g j₀ u where
  toFun C := by
    refine ⟨C.val.val,?_,?_,?_⟩
    · exact markedPathRims_rootCycle P π (3*d) m j v v' τ hm C.val.val false C.val.property.1 C.property
    · exact markedPathRims_rootCycle P π (3*d) m j v v' τ hm C.val.val true C.val.property.2.1 C.property
    · intro i
      rw [rootFirstSpokeType_free m hm j i]
      have hmem := C.val.property.2.2.1 i
      by_cases hc : j=false ∧ i.val=2
      · simp only [hc,ite_true,decide_true] at hmem ⊢
        have hh := (Finset.mem_filter.mp hmem).2
        exact ⟨hh 0,hh 1⟩
      · simp only [hc,ite_false,decide_false,Bool.false_eq_true] at hmem ⊢
        have hh := (Finset.mem_filter.mp hmem).2
        exact ⟨hh 0,hh 1⟩
  inj' C D he := by
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun C : SampledCommonMarkedPath P π d m j v v' σ τ g j₀ u=>C.val) he

theorem survivingPath_card_le_common_path (hm : 2≤m) :
    Fintype.card {C : DenseRootMarkedPathFamily P π (3*d) m j
      (rawMarkedPairClass π d σ g j₀ u false) (rawMarkedPairClass π d σ g j₀ u true) v v' //
        MarkedPathRims P π (3*d) m j v v' τ C.val}≤
      Fintype.card (SampledCommonMarkedPath P π d m j v v' σ τ g j₀ u) :=
  Fintype.card_le_of_injective _ (survivingPath_to_common_path P π d m j v v' σ τ g j₀ u hm).injective

end Oberwolfach

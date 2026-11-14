module

public import Oberwolfach.InnerRequiredTargetsProtectedMonotone

@[expose] public section
/-! The enlarged protected set gives precisely the target coverage needed
on the first inner pair, provided the absorber avoids that pair. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype U] [DecidableEq U] [DecidableEq V]

theorem inner_protected_targets_coverage
    (I:Finset V) (J:Finset U) (Outer Y Absorber Old New:U→Finset V)
    (hAbs:∀u∈J,Disjoint (Absorber u) I)
    (hNew:∀u,innerRequiredTargets J I Outer Y Absorber Old u⊆New u):
    (∀u,Disjoint (innerRequiredTargets J I Outer Y Absorber Old u) (Outer u)) ∧
    (∀u∈J,∀v∈I,v∉Outer u→v∉Y u→v∉Old u→v∈New u):=by
  constructor
  · intro u
    by_cases hu:u∈J
    · apply Finset.disjoint_left.mpr
      intro v hv ho
      simp only [innerRequiredTargets,hu,if_true,Finset.mem_sdiff,Finset.mem_union] at hv
      exact hv.2 (Or.inl (Or.inl (Or.inl ho)))
    · simp [innerRequiredTargets,hu]
  · intro u hu v hv ho hy hold
    apply hNew u
    simp only [innerRequiredTargets,hu,if_true,Finset.mem_sdiff,Finset.mem_union]
    refine ⟨hv,?_⟩
    rintro (((hO|hY)|hA)|hOld)
    · exact ho hO
    · exact hy hY
    · exact (Finset.disjoint_left.mp (hAbs u hu)) hA hv
    · exact hold hOld
end Oberwolfach

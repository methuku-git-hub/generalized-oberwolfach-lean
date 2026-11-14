module

public import Oberwolfach.InnerRequiredTargets

@[expose] public section
/-! Protecting more spoke positions can only shrink the required inner
completion targets, so the established load and capacity bounds survive. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I V:Type} [Fintype I] [DecidableEq I] [DecidableEq V]

theorem inner_required_targets_protected_mono
    (inner:Finset I) (vertices:Finset V)
    (reserved larger selected absorber occupied:I→Finset V)
    (hprotect:∀u,reserved u⊆larger u):
    (∀u,innerRequiredTargets inner vertices larger selected absorber occupied u⊆
      innerRequiredTargets inner vertices reserved selected absorber occupied u) ∧
    (∀v,((inner.filter (fun u=>v∈innerRequiredTargets inner vertices larger selected absorber occupied u)).card)≤
      (inner.filter (fun u=>v∈innerRequiredTargets inner vertices reserved selected absorber occupied u)).card):=by
  have hsub:∀u,innerRequiredTargets inner vertices larger selected absorber occupied u⊆
      innerRequiredTargets inner vertices reserved selected absorber occupied u:=by
    intro u v hv
    by_cases hu:u∈inner
    · simp only [innerRequiredTargets,hu,if_true,Finset.mem_sdiff,Finset.mem_union] at hv ⊢
      refine ⟨hv.1,?_⟩
      rintro (((hr|hs)|ha)|ho)
      · exact hv.2 (Or.inl (Or.inl (Or.inl (hprotect u hr))))
      · exact hv.2 (Or.inl (Or.inl (Or.inr hs)))
      · exact hv.2 (Or.inl (Or.inr ha))
      · exact hv.2 (Or.inr ho)
    · simp [innerRequiredTargets,hu] at hv
  refine ⟨hsub,?_⟩
  intro v
  apply Finset.card_le_card
  intro u hu
  simp only [Finset.mem_filter] at hu ⊢
  exact ⟨hu.1,hsub u hu.2⟩
end Oberwolfach

module

public import Oberwolfach.MarkedClassSharedSelectedOrdinaryLaw
public import Oberwolfach.ClassColourBernoulli

@[expose] public section
/-! The selected ordinary physical layer is a subgraph of its class colour. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem selected_class_state_implies_membership {k:ℕ} (a:Fin k)
    (z:Σ _:Fin k,Fin 5):
    (decide ((markedPhysicalOptionIndex (classRefinedView a z))=0):Bool)=true →
    classColourMembership a z.1=true := by
  rcases z with ⟨c,i⟩
  by_cases hc:c=a
  · simp [classColourMembership,hc]
  · simp [classColourMembership,classRefinedView,markedPhysicalOptionIndex,hc]
end Oberwolfach

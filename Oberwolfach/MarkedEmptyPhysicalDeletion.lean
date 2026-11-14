module

public import Oberwolfach.MarkedNeighbourhoodPhysicalDeletion

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem rawMarkedDeleteRims_empty (σ:RawMarkedOutcome V U Γ Color):rawMarkedDeleteRims σ ∅=σ:=by
  funext e
  cases e <;> simp [rawMarkedDeleteRims]

theorem rawMarkedDeleteRims_bottom (σ:RawMarkedOutcome V U Γ Color):
    rawMarkedDeleteRims σ (⊥:SimpleGraph V).edgeFinset=σ:=by
  simpa using rawMarkedDeleteRims_empty σ

theorem markedDeletePhysicalSpokes_bottom (H:Bool→V→U→Prop):
    markedDeletePhysicalSpokes H (⊥:SimpleGraph (V⊕U))=H:=by
  funext a v u
  simp [markedDeletePhysicalSpokes]

end Oberwolfach

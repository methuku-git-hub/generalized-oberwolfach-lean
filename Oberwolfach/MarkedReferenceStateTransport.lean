module

public import Oberwolfach.MarkedReferenceDeletionState

@[expose] public section

/-! A reference-deletion state is unchanged by equal descriptions of the
underlying graph, raw outcome and spoke relations. In particular, the
actual deleted and remaining physical sets and the full validity condition
are transported together. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [LinearOrder V] [DecidableEq U]

theorem marked_reference_state_transport
    (P Q:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ)
    (σ τ:RawMarkedOutcome V U Γ Color) (H H':Bool → V → U → Prop)
    (hP:P=Q) (hσ:σ=τ) (hH:H=H')
    (X:Finset V) (Y:Finset U) (γ σloss:ℝ)
    (D:MarkedReferenceDeletion P π d σ):
    ∃ D':MarkedReferenceDeletion Q π d τ,
      (D'.Valid H' m X Y γ σloss ↔ D.Valid H m X Y γ σloss) ∧
      D'.removed=D.removed ∧ D'.remaining H'=D.remaining H:=by
  subst Q
  subst τ
  subst H'
  exact ⟨D,Iff.rfl,rfl,rfl⟩

end Oberwolfach

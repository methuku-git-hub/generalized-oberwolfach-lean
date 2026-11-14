module

public import Oberwolfach.OrdinaryEligibleCandidateSupport
public import Oberwolfach.SuccessorSequencePositionBounds

@[expose] public section
/-! Normalized seeds from the eligible host have no weight on wheels
using physically forbidden rim edges. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]

theorem ordinary_eligible_shifted_seed_support
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ) (D τ A B p:ℝ) (s:U→ℝ)
    (weight:(Fin (m+1)→V)→ℝ)
    (hw:SuccessorSequenceWeightConditions (ordinaryEligibleHost P π d) π (3*d) D τ A B weight):
    ∀W:MarkedWheel (Prod.fst:V×V→V) Prod.snd Prod.fst Prod.snd m π (3*d)
      (fun _ (_:U)=>True) (fun _ (_:U)=>True),
    weight W.1.val/(D*p^(m+1)*(s W.2.val)^m)≠0→
    ∀z∈typedMarkedOccurrenceResources W,ordinaryPhysicalEligible (U:=U) π d (ordinaryMixedPhysicalResource π z) :=by
  intro W hW
  have hweight:weight W.1.val≠0:=by intro h;simp [h] at hW
  have hparent:=successor_weight_parent_edges hw W.1.val hweight
  exact ordinary_shifted_candidate_resources_eligible P π d m (3*d) W hparent.1 hparent.2

theorem ordinary_eligible_unshifted_seed_support
    (P:SimpleGraph V) (π:Equiv.Perm V) (d ℓ:ℕ) (hℓ:1≤ℓ)
    (D p:ℝ) (s η:U→ℝ) (weight:OrdinaryCycle (ordinaryEligibleHost P π d) (ℓ+2)→ℝ):
    ∀W:OrderedOrdinaryWheel (U:=U) π (3*d) (ℓ+2),
      η W.2*physicalOrdinaryTupleWeight (π:=π) (b:=3*d) hℓ weight W.1.val/
        (((ℓ+2:ℕ):ℝ)*D*p^(ℓ+2)*(s W.2)^(ℓ+1))≠0→
    ∀z∈(orderedOrdinaryResources W).map ordinaryMarkedResourceEmbedding,
      ordinaryPhysicalEligible (U:=U) π d (ordinaryMixedPhysicalResource π z) :=by
  intro W hW
  have hweight:physicalOrdinaryTupleWeight (π:=π) (b:=3*d) hℓ weight W.1.val≠0:=by
    intro h;simp [h] at hW
  have hparent:=(physicalOrdinaryTupleWeight_support hℓ weight W.1.val hweight).2
  exact ordinary_unshifted_candidate_resources_eligible P π d (ℓ+2) (3*d) W hparent
end Oberwolfach

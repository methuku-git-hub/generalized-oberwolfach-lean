module

public import Oberwolfach.LongRetainedHubCoefficient

@[expose] public section
/-! The finite family of retained length-and-hub tests is fixed before
exposure and has at most K times the number of hubs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n:ℕ} {U:Type} [Fintype U]

def LongRetainedHubTest
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2) (K:ℕ) (θ:ℝ):Type:=
  {z:Fin K×U // θ/(100*(K:ℝ))≤longAssignedKeptFraction F hF K θ z.1 z.2}

noncomputable instance (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2) (K:ℕ) (θ:ℝ):
    Fintype (LongRetainedHubTest F hF K θ):=by
  unfold LongRetainedHubTest
  infer_instance

theorem long_retained_hub_tests_card_bound
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2) (K:ℕ) (θ:ℝ)
    (hU:Fintype.card U≤n) (hK:K≤n):
    Fintype.card (LongRetainedHubTest F hF K θ)≤n^2 :=by
  have h:Fintype.card (LongRetainedHubTest F hF K θ)≤K*Fintype.card U:=by
    have hh:=Fintype.card_le_of_injective (fun z:LongRetainedHubTest F hF K θ=>(z.val:Fin K×U)) Subtype.val_injective
    simpa only [Fintype.card_prod,Fintype.card_fin] using hh
  nlinarith
end Oberwolfach

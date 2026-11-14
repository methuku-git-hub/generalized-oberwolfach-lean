module

public import Oberwolfach.OrdinaryMixedHubWeightsGeneral
public import Oberwolfach.OrdinaryMixedHubWeights

@[expose] public section
/-! The length-two general hub weights are exactly the triangle hub weights
used by the endpoint-factor construction. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

def ordinary_triangle_hub_weights_from_length
    (Q F:SimpleGraph V) (H:V→U→Prop) (A:Finset V) (Z:Finset U) (b B η:ℝ)
    (w:OrdinaryMixedHubWeightsOfLength 2 b B η Q F H A Z):
    OrdinaryMixedHubWeights b B η Q F H A Z :=by
  exact ⟨w.weight,w.bounds,w.loads⟩
end Oberwolfach

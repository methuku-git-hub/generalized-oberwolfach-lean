module

public import Oberwolfach.OrdinaryInnerHubWeightSetupGeneral

@[expose] public section
/-! Apply the fixed inner data to any edited host whose hub potentials have
the stated target accuracy. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1500000
set_option synthInstance.maxSize 4096
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U : Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

def ordinary_hub_weights_of_setup_general
    (m:ℕ) (hm:2≤m)
    (P Q F : SimpleGraph V) (H : V → U → Prop) (A : Finset V) (Z : Finset U)
    (weight : OrdinaryCycle (P.induce (A : Set V)) (m+1) → ℝ)
    (p pR pH D δ ξ L cLo cHi b B η K : ℝ)
    (setup : OrdinaryInnerHubWeightSetupGeneral m P F A weight p pR pH D δ ξ L cLo cHi b B η K)
    (hQP : Q≤P)
    (hpotential : ∀ u : {u : U // u∉Z}, ∀ v ∈ ordinaryInducedLocalDomain A (ordinaryBoundaryHubSet H Z A u),
      |ordinaryLocalPotential (P.induce (A : Set V)) (Q.induce (A : Set V)) (F.induce (A : Set V))
        (ordinaryInducedLocalDomain A (ordinaryBoundaryHubSet H Z A u))
        (fun C => 2*weight C/(D*pR^(m+1)*pH^m)) v -
        ordinaryLocalTarget (P.induce (A : Set V)) (F.induce (A : Set V)) weight D v| ≤ ξ) :
    OrdinaryMixedHubWeightsOfLength m b B η Q F H A Z := by
  exact ordinary_mixed_hub_weights_of_length_from_potentials m hm P Q F H A Z p pR pH D δ ξ L cLo cHi b B η K
    setup.Apos hQP setup.ppos setup.pone setup.rimlo setup.rimhi setup.spokelo setup.spokehi
    setup.delta_nonneg setup.conflict_nonneg setup.lower_pos setup.upper_nonneg setup.scale_nonneg
    setup.center_lower setup.center_upper setup.regular setup.conflict weight setup.coefficients setup.edge_loads
    hpotential setup.domain_scale setup.lower_scale setup.upper_scale (by simpa only [Nat.cast_add,Nat.cast_one] using setup.error_margin)
end Oberwolfach

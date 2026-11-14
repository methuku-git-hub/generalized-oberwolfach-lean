module

public import Oberwolfach.OrdinaryHubWeightsOfSetup
public import Oberwolfach.OrdinaryCleanupParentProfiles
public import Oberwolfach.CommonEvents

@[expose] public section
/-! An event carrying exact target estimates for every later cleanup profile
also carries the corresponding mixed hub weights on the same outcome. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2000000
set_option synthInstance.maxSize 4096
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color Ω : Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [Fintype Ω]
    [DecidableEq V] [DecidableEq U]

theorem ordinary_hub_weight_event_from_targets
    (μ : FiniteLaw Ω) (E : Ω → Prop) (raw : Ω → RawWheelOutcome V U Γ Color)
    (P F : SimpleGraph V) (A : Finset V) (Z : Finset U) (π : Equiv.Perm V) (d : ℕ) (j : Color)
    (s : U → Color → ℝ) (weight : OrdinaryCycle (P.induce (A : Set V)) 3 → ℝ)
    (p pR pH D δ ξ Lconf cLo cHi b B η K density tR tH Ledit βe βh prob : ℝ)
    (setup : OrdinaryInnerHubWeightSetup P F A weight p pR pH D δ ξ Lconf cLo cHi b B η K)
    (hprob : prob ≤ μ.probability (fun z => E z ∧
      ∀ (Q : SimpleGraph V) (H : V → U → Prop),
        OrdinaryCleanupParentProfiles P Q F H π d A Z pR pH density tR tH Ledit βe βh s j (raw z) →
        ∀ u : {u : U // u ∉ Z}, ∀ v ∈ ordinaryInducedLocalDomain A (ordinaryBoundaryHubSet H Z A u),
          |ordinaryLocalPotential (P.induce (A : Set V)) (Q.induce (A : Set V)) (F.induce (A : Set V))
            (ordinaryInducedLocalDomain A (ordinaryBoundaryHubSet H Z A u))
            (fun C => 2*weight C/(D*pR^3*pH^2)) v -
            ordinaryLocalTarget (P.induce (A : Set V)) (F.induce (A : Set V)) weight D v| ≤ ξ)) :
    prob ≤ μ.probability (fun z => E z ∧
      ∀ (Q : SimpleGraph V) (H : V → U → Prop),
        OrdinaryCleanupParentProfiles P Q F H π d A Z pR pH density tR tH Ledit βe βh s j (raw z) →
        Q≤P → Nonempty (OrdinaryMixedHubWeights b B η Q F H A Z)) := by
  apply hprob.trans
  apply finiteLaw_probability_mono
  intro z hz
  refine ⟨hz.1,?_⟩
  intro Q H profile hQP
  exact ⟨ordinary_hub_weights_of_setup P Q F H A Z weight p pR pH D δ ξ Lconf cLo cHi b B η K
    setup hQP (hz.2 Q H profile)⟩
end Oberwolfach

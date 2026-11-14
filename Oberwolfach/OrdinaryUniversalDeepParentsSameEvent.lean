module

public import Oberwolfach.OrdinaryUniversalDeepParentsFromRawPrior

@[expose] public section
/-! Preserve any earlier event while converting the raw prior and universal
    hub weights into corrected parents for every later cleanup. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color Ω:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [Fintype Ω]
  [LinearOrder V] [DecidableEq U]

theorem ordinary_universal_deep_parents_same_event
    (μ:FiniteLaw Ω) (E:Ω→Prop) (sample:Ω→RawWheelOutcome V U Γ Color)
    (P F:SimpleGraph V) (A:Finset V) (Z:Finset U) (π:Equiv.Perm V) (d k:ℕ) (j:Color) (s:U→Color→ℝ)
    (weight:V→Sym2 (V⊕U)→ℝ) (triangleWeight:OrdinaryCycle P 3→ℝ)
    (γ κ b B εf η κe p pR pH density tR tH L Ledit βe βh δ ε t Kscale e:ℝ)
    (α pstar βP ηP ηH βH c Btri prob:ℝ)
    (margins:OrdinaryDeepParentMargins P F A Z γ κ b B εf η κe p pR pH density tR tH L Ledit δ ε t Kscale e)
    (parent:EndpointPhysicalParentWeights P A Aᶜ weight)
    (hprob:prob≤μ.probability (fun z=>E z ∧
      OrdinaryRawHubParentPrior d k P F A Z π j s weight triangleWeight
        α pstar βP ηP ηH βH c Btri pR pH t tR tH (sample z) ∧
      ∀(Q:SimpleGraph V) (H:V→U→Prop),
        OrdinaryCleanupParentProfiles P Q F H π d A Z pR pH density tR tH Ledit βe βh s j (sample z) →
        Q≤P → Nonempty (OrdinaryMixedHubWeights b B η Q F H A Z))) :
    prob≤μ.probability (fun z=>E z ∧
      OrdinaryRawHubParentPrior d k P F A Z π j s weight triangleWeight
        α pstar βP ηP ηH βH c Btri pR pH t tR tH (sample z) ∧
      ∀(Q:SimpleGraph V) (H:V→U→Prop),
        OrdinaryCleanupParentProfiles P Q F H π d A Z pR pH density tR tH Ledit βe βh s j (sample z) →
        Q≤P → Nonempty (MixedFreshParentDataInsideRoots γ κ b B εf η (spanningRestriction Q A) F
          (ordinaryPhysicalGraph (spanningRestriction Q A) (fun v u=>H v u∧v∈A∧u∈Z))
          (ordinaryPhysicalGraph F (fun _ _=>False)) (Function.Embedding.inl:V↪V⊕U)
          (ordinaryBoundaryHubSet H Z A) (fun i=>(ordinaryBoundaryRimSet Q A i).image Sum.inl)
          (fun i=>(ordinaryBoundaryRowSet H A Z i).image Sum.inr))) := by
  apply hprob.trans
  apply finiteLaw_probability_mono
  intro z hz
  refine ⟨hz.1,hz.2.1,?_⟩
  exact ordinary_universal_deep_parents_from_raw_prior P F A Z π d k j s weight triangleWeight
    γ κ b B εf η κe p pR pH density tR tH L Ledit βe βh δ ε t Kscale e
    α pstar βP ηP ηH βH c Btri (sample z) margins parent hz.2.1 hz.2.2
end Oberwolfach

module

public import Oberwolfach.OrdinaryDeepParentFromRawHubPrior

@[expose] public section
/-! The raw prior and adaptive hub weights produce the corrected mixed parent
    for every later admissible cleanup of that same sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem ordinary_universal_deep_parents_from_raw_prior
    (P F:SimpleGraph V) (A:Finset V) (Z:Finset U) (π:Equiv.Perm V) (d k:ℕ) (j:Color) (s:U→Color→ℝ)
    (weight:V→Sym2 (V⊕U)→ℝ) (triangleWeight:OrdinaryCycle P 3→ℝ)
    (γ κ b B εf η κe p pR pH density tR tH L Ledit βe βh δ ε t Kscale e:ℝ)
    (α pstar βP ηP ηH βH c Btri:ℝ) (σ:RawWheelOutcome V U Γ Color)
    (margins:OrdinaryDeepParentMargins P F A Z γ κ b B εf η κe p pR pH density tR tH L Ledit δ ε t Kscale e)
    (parent:EndpointPhysicalParentWeights P A Aᶜ weight)
    (event:OrdinaryRawHubParentPrior d k P F A Z π j s weight triangleWeight
      α pstar βP ηP ηH βH c Btri pR pH t tR tH σ)
    (hweights:∀(Q:SimpleGraph V) (H:V→U→Prop),
      OrdinaryCleanupParentProfiles P Q F H π d A Z pR pH density tR tH Ledit βe βh s j σ →
      Q≤P → Nonempty (OrdinaryMixedHubWeights b B η Q F H A Z)) :
    ∀(Q:SimpleGraph V) (H:V→U→Prop),
      OrdinaryCleanupParentProfiles P Q F H π d A Z pR pH density tR tH Ledit βe βh s j σ →
      Q≤P → Nonempty (MixedFreshParentDataInsideRoots γ κ b B εf η (spanningRestriction Q A) F
        (ordinaryPhysicalGraph (spanningRestriction Q A) (fun v u=>H v u∧v∈A∧u∈Z))
        (ordinaryPhysicalGraph F (fun _ _=>False)) (Function.Embedding.inl:V↪V⊕U)
        (ordinaryBoundaryHubSet H Z A) (fun i=>(ordinaryBoundaryRimSet Q A i).image Sum.inl)
        (fun i=>(ordinaryBoundaryRowSet H A Z i).image Sum.inr)) := by
  intro Q H profile hQP
  have hQ:Q≤P\F := by
    intro x y hxy
    exact ⟨hQP hxy,fun hf=>(disjoint_iff_inf_le.mp profile.forbidden_disjoint) ⟨hxy,hf⟩⟩
  obtain ⟨hw⟩:=hweights Q H profile hQP
  exact ⟨ordinary_deep_parent_from_raw_hub_prior P Q F H A Z π d k j s weight triangleWeight
    γ κ b B εf η κe p pR pH density tR tH L Ledit βe βh δ ε t Kscale e
    α pstar βP ηP ηH βH c Btri σ margins hQ profile parent event hw⟩
end Oberwolfach

module

public import Oberwolfach.OrdinaryDeepParentFromIngredients
public import Oberwolfach.OrdinaryDeepParentRimSub
public import Oberwolfach.CommonEvents

@[expose] public section
/-! The hub-weight event yields a full corrected mixed parent for every
later host satisfying the explicit deep/endpoint inputs on that same outcome. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2200000
set_option synthInstance.maxSize 4096
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color Ω:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [Fintype Ω]
  [DecidableEq V] [DecidableEq U]

theorem ordinary_deep_parent_event_from_hub_event
    (μ:FiniteLaw Ω) (E:Ω→Prop) (raw:Ω→RawWheelOutcome V U Γ Color)
    (P F:SimpleGraph V) (A:Finset V) (Z:Finset U) (π:Equiv.Perm V) (d:ℕ) (j:Color) (s:U→Color→ℝ)
    (weight:V→Sym2 (V⊕U)→ℝ)
    (γ κ b B εf η κe p pR pH density tR tH L Ledit βe βh δ ε t K prob:ℝ)
    (hprob:prob≤μ.probability (fun z=>E z ∧ ∀(Q:SimpleGraph V) (H:V→U→Prop),
      OrdinaryCleanupParentProfiles P Q F H π d A Z pR pH density tR tH Ledit βe βh s j (raw z)→
      Q≤P→Nonempty (OrdinaryMixedHubWeights b B η Q F H A Z))) :
    prob≤μ.probability (fun z=>E z ∧ ∀(Q:SimpleGraph V) (H:V→U→Prop),
      OrdinaryDeepParentIngredients P Q F H A Z π d j s weight γ κ b B εf η κe p pR pH density
        tR tH L Ledit βe βh δ ε t K (raw z)→
      Nonempty (MixedFreshParentDataInsideRoots γ κ b B εf η (spanningRestriction Q A) F
        (ordinaryPhysicalGraph (spanningRestriction Q A) (fun v u=>H v u∧v∈A∧u∈Z))
        (ordinaryPhysicalGraph F (fun _ _=>False)) (Function.Embedding.inl:V↪V⊕U)
        (ordinaryBoundaryHubSet H Z A) (fun i=>(ordinaryBoundaryRimSet Q A i).image Sum.inl)
        (fun i=>(ordinaryBoundaryRowSet H A Z i).image Sum.inr))) := by
  apply hprob.trans
  apply finiteLaw_probability_mono
  intro z hz
  refine ⟨hz.1,?_⟩
  intro Q H inputs
  have hQP:Q≤P := (ordinary_deep_parent_rim_sub P Q F H A Z π d j s weight γ κ b B εf η κe p pR pH density
    tR tH L Ledit βe βh δ ε t K (raw z) inputs).trans sdiff_le
  obtain ⟨hw⟩ := hz.2 Q H inputs.profile hQP
  exact ⟨ordinary_deep_parent_from_ingredients P Q F H A Z π d j s weight γ κ b B εf η κe p pR pH density
    tR tH L Ledit βe βh δ ε t K (raw z) inputs hw⟩
end Oberwolfach

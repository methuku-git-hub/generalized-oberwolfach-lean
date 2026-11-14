module

public import Oberwolfach.OrdinaryDeepParentFromIngredients
public import Oberwolfach.OrdinaryDeepParentRimSub
public import Oberwolfach.OrdinaryShiftedMatchingCoreEvent
public import Oberwolfach.ExpandedOrdinarySelectedLaw
public import Oberwolfach.CommonEvents

@[expose] public section
/-! A single expanded outcome keeps the checked matching core and converts
its universal hub weights into corrected mixed parents for all later hosts. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2500000
set_option synthInstance.maxSize 8192
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n K:ℕ} {U Ω:Type} [Fintype U] [Fintype Ω] [DecidableEq U]

theorem ordinary_matching_core_deep_parent_event
    (μ:FiniteLaw Ω) (E J C:Ω→Prop)
    (state:Ω→(∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e))
    (P Pmatch F:SimpleGraph (Fin n)) (A:Finset (Fin n)) (Z:Finset U)
    (π:Equiv.Perm (Fin n)) (d m:ℕ) (pMark kMark:ℝ) (q s:U→Bool→ℝ)
    (wM:MarkedWheel (Prod.fst:Fin n×Fin n→Fin n) Prod.snd Prod.fst Prod.snd m π (3*d)
      (fun _ (_:U)=>True) (fun _ (_:U)=>True)→ℝ)
    (wO:∀i:Fin K,OrderedOrdinaryWheel (U:=U) π (3*d) (longPaddedSeedExponent i+2)→ℝ)
    (tMark ξMark:ℝ) (endpointWeight:Fin n→Sym2 (Fin n⊕U)→ℝ)
    (γ κ b B εf η κe p pR pH density tR tH L Ledit βe βh δ ε t Kscale prob:ℝ)
    (hprob:prob≤μ.probability (fun z=>
      ((E z ∧ OrdinaryShiftedMatchingCoreEvent Pmatch π d m pMark kMark q s wM wO tMark ξMark (state z)) ∧
      (J z ∧ ∀(Q:SimpleGraph (Fin n)) (H:Fin n→U→Prop),
        OrdinaryCleanupParentProfiles P Q F H π d A Z pR pH density tR tH Ledit βe βh s false
          (fun e=>expandedOrdinarySelectedCollapse e (state z e))→
        Q≤P→Nonempty (OrdinaryMixedHubWeights b B η Q F H A Z))) ∧ C z)) :
    prob≤μ.probability (fun z=>
      ((E z ∧ OrdinaryShiftedMatchingCoreEvent Pmatch π d m pMark kMark q s wM wO tMark ξMark (state z)) ∧
      (J z ∧ ∀(Q:SimpleGraph (Fin n)) (H:Fin n→U→Prop),
        OrdinaryDeepParentIngredients P Q F H A Z π d false s endpointWeight γ κ b B εf η κe p pR pH density
          tR tH L Ledit βe βh δ ε t Kscale (fun e=>expandedOrdinarySelectedCollapse e (state z e))→
        Nonempty (MixedFreshParentDataInsideRoots γ κ b B εf η (spanningRestriction Q A) F
          (ordinaryPhysicalGraph (spanningRestriction Q A) (fun v u=>H v u∧v∈A∧u∈Z))
          (ordinaryPhysicalGraph F (fun _ _=>False)) (Function.Embedding.inl:Fin n↪Fin n⊕U)
          (ordinaryBoundaryHubSet H Z A) (fun i=>(ordinaryBoundaryRimSet Q A i).image Sum.inl)
          (fun i=>(ordinaryBoundaryRowSet H A Z i).image Sum.inr)))) ∧ C z) := by
  apply hprob.trans
  apply finiteLaw_probability_mono
  intro z hz
  obtain ⟨⟨⟨hE,hcore⟩,⟨hJ,hweights⟩⟩,hC⟩:=hz
  refine ⟨⟨⟨hE,hcore⟩,⟨hJ,?_⟩⟩,hC⟩
  intro Q H inputs
  have hQP:Q≤P := (ordinary_deep_parent_rim_sub P Q F H A Z π d false s endpointWeight
    γ κ b B εf η κe p pR pH density tR tH L Ledit βe βh δ ε t Kscale
    (fun e=>expandedOrdinarySelectedCollapse e (state z e)) inputs).trans sdiff_le
  obtain ⟨hw⟩:=hweights Q H inputs.profile hQP
  exact ⟨ordinary_deep_parent_from_ingredients P Q F H A Z π d false s endpointWeight
    γ κ b B εf η κe p pR pH density tR tH L Ledit βe βh δ ε t Kscale
    (fun e=>expandedOrdinarySelectedCollapse e (state z e)) inputs hw⟩
end Oberwolfach

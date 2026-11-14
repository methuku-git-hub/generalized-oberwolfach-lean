module

public import Oberwolfach.OrdinaryUniversalDeepParentsFromRawPrior
public import Oberwolfach.OrdinaryShiftedMatchingCoreEvent
public import Oberwolfach.ExpandedOrdinarySelectedLaw

@[expose] public section
/-! Keep the matching core and every earlier common-event property while the
    raw parent and adaptive hub weights yield actual corrected mixed parents. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 5000000
set_option synthInstance.maxSize 8192
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance (priority := high) matchingRawUniversalParentsFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _
variable {n K:ℕ} {U Ω:Type} [Fintype U] [Fintype Ω] [DecidableEq U]

theorem ordinary_matching_core_raw_universal_parents_same_event
    (μ:FiniteLaw Ω) (E C:Ω→Prop)
    (state:Ω→(∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e))
    (P Pmatch F:SimpleGraph (Fin n)) (A:Finset (Fin n)) (Z:Finset U)
    (π:Equiv.Perm (Fin n)) (d m kTri:ℕ) (pMark kMark:ℝ) (q s:U→Bool→ℝ)
    (wM:MarkedWheel (Prod.fst:Fin n×Fin n→Fin n) Prod.snd Prod.fst Prod.snd m π (3*d)
      (fun _ (_:U)=>True) (fun _ (_:U)=>True)→ℝ)
    (wO:∀i:Fin K,OrderedOrdinaryWheel (U:=U) π (3*d) (longPaddedSeedExponent i+2)→ℝ)
    (tMark ξMark:ℝ) (endpointWeight:Fin n→Sym2 (Fin n⊕U)→ℝ) (triangleWeight:OrdinaryCycle P 3→ℝ)
    (γ κ b B εf η κe p pR pH density tR tH L Ledit βe βh δ ε t Kscale e:ℝ)
    (α pstar βP ηP ηH βH c Btri prob:ℝ)
    (margins:OrdinaryDeepParentMargins P F A Z γ κ b B εf η κe p pR pH density tR tH L Ledit δ ε t Kscale e)
    (parent:EndpointPhysicalParentWeights P A Aᶜ endpointWeight)
    (hprob:prob≤μ.probability (fun z=>
      let raw:=fun e=>expandedOrdinarySelectedCollapse e (state z e);
      ((E z ∧ OrdinaryShiftedMatchingCoreEvent Pmatch π d m pMark kMark q s wM wO tMark ξMark (state z)) ∧
      (OrdinaryRawHubParentPrior d kTri P F A Z π false s endpointWeight triangleWeight
        α pstar βP ηP ηH βH c Btri pR pH t tR tH raw ∧
      ∀(Q:SimpleGraph (Fin n)) (H:Fin n→U→Prop),
        OrdinaryCleanupParentProfiles P Q F H π d A Z pR pH density tR tH Ledit βe βh s false raw →
        Q≤P → Nonempty (OrdinaryMixedHubWeights b B η Q F H A Z))) ∧ C z)) :
    prob≤μ.probability (fun z=>
      let raw:=fun e=>expandedOrdinarySelectedCollapse e (state z e);
      ((E z ∧ OrdinaryShiftedMatchingCoreEvent Pmatch π d m pMark kMark q s wM wO tMark ξMark (state z)) ∧
      (OrdinaryRawHubParentPrior d kTri P F A Z π false s endpointWeight triangleWeight
        α pstar βP ηP ηH βH c Btri pR pH t tR tH raw ∧
      ∀(Q:SimpleGraph (Fin n)) (H:Fin n→U→Prop),
        OrdinaryCleanupParentProfiles P Q F H π d A Z pR pH density tR tH Ledit βe βh s false raw →
        Q≤P → Nonempty (MixedFreshParentDataInsideRoots γ κ b B εf η (spanningRestriction Q A) F
          (ordinaryPhysicalGraph (spanningRestriction Q A) (fun v u=>H v u∧v∈A∧u∈Z))
          (ordinaryPhysicalGraph F (fun _ _=>False)) (Function.Embedding.inl:Fin n↪Fin n⊕U)
          (ordinaryBoundaryHubSet H Z A) (fun i=>(ordinaryBoundaryRimSet Q A i).image Sum.inl)
          (fun i=>(ordinaryBoundaryRowSet H A Z i).image Sum.inr)))) ∧ C z) := by
  apply hprob.trans
  apply finiteLaw_probability_mono
  intro z hz
  obtain ⟨⟨⟨hE,hcore⟩,hraw,hweights⟩,hC⟩:=hz
  refine ⟨⟨⟨hE,hcore⟩,hraw,?_⟩,hC⟩
  exact ordinary_universal_deep_parents_from_raw_prior P F A Z π d kTri false s endpointWeight triangleWeight
    γ κ b B εf η κe p pR pH density tR tH L Ledit βe βh δ ε t Kscale e
    α pstar βP ηP ηH βH c Btri _ margins parent hraw hweights
end Oberwolfach

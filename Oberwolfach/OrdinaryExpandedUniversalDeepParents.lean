module

public import Oberwolfach.OrdinaryExpandedAdaptiveHubWeightsProductPrior
public import Oberwolfach.OrdinaryUniversalDeepParentsFromRawPrior

@[expose] public section
/-! A full product prior containing the raw parent event is preserved while
    adaptive hub weights give corrected mixed parents for every cleanup. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 7000000
set_option synthInstance.maxSize 8192
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem ordinary_expanded_universal_deep_parents_with_prior
    (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1) (d:ℕ) (hd:2≤d)
    (q:U→Γ→ℝ) (hq:∀w g,0≤q w g) (hQ:∀w,∑g,q w g≤1/8)
    (s:U→Color→ℝ) (hs:∀w j,0≤s w j) (hS:∀w,∑j,s w j≤ intervalUncoveredProbability d (∑g,q w g))
    {R:(∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)→Type}
    [∀σ,Fintype (R σ)] (ρ:∀σ,FiniteLaw (R σ)) (ν:FiniteLaw (Sym2 V→Bool))
    (E:(Σσ,R σ)×(Sym2 V→Bool)→Prop) (a:ℝ)
    (P F:SimpleGraph V) (A:Finset V) (Z:Finset U) (π:Equiv.Perm V) (j:Color) (kTri:ℕ)
    (hconf:permutationConflictGraph π (3*d)≤F)
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (pmin pH D δreg ξ Lconf cLo cHi b Bweight η K tHub Ledit density tR tH βe βh:ℝ)
    (hcHi:0<cHi) (htHub:0<tHub) (innerWeight:OrdinaryCycle (P.induce (A:Set V)) 3→ℝ)
    (setup:OrdinaryInnerHubWeightSetup P F A innerWeight pmin (2*p) pH D δreg ξ Lconf cLo cHi b Bweight η K)
    (endpointWeight:V→Sym2 (V⊕U)→ℝ) (triangleWeight:OrdinaryCycle P 3→ℝ)
    (γ κ εf κe parentδ εparent tEndpoint Kscale e:ℝ)
    (α pstar βP ηP ηH βH c Btri:ℝ)
    (margins:OrdinaryDeepParentMargins P F A Z γ κ b Bweight εf η κe pmin (2*p) pH density
      tR tH Lconf Ledit parentδ εparent tEndpoint Kscale e)
    (parent:EndpointPhysicalParentWeights P A Aᶜ endpointWeight)
    (hEparent:∀z,E z → OrdinaryRawHubParentPrior d kTri P F A Z π j s endpointWeight triangleWeight
      α pstar βP ηP ηH βH c Btri (2*p) pH tEndpoint tR tH
      (fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e))) :
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS);
    let Bpot:=4*cHi/pmin^7;
    let err:=(Fintype.card (A:Set V):ℝ)*Fintype.card U *
      (2*Real.exp (-2*tHub^2/((4*(d:ℝ)+3)^2*((3:ℝ)^4*Bpot/Fintype.card (A:Set V))*(2*3)*((3:ℝ)^2*Bpot))));
    tHub+(3:ℝ)^2*Bpot*Ledit/Fintype.card (A:Set V)+
      2*(3*(3:ℝ)^4*Bpot*Ledit/Fintype.card (A:Set V))≤ξ →
    1-a≤((μ.sigma ρ).prod ν).probability E →
    1-a-err≤((μ.sigma ρ).prod ν).probability (fun z=>E z ∧
      let raw:=fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e);
      ∀(Q:SimpleGraph V) (H:V→U→Prop),
        OrdinaryCleanupParentProfiles P Q F H π d A Z (2*p) pH density tR tH Ledit βe βh s j raw →
        Q≤P → Nonempty (MixedFreshParentDataInsideRoots γ κ b Bweight εf η (spanningRestriction Q A) F
          (ordinaryPhysicalGraph (spanningRestriction Q A) (fun v u=>H v u∧v∈A∧u∈Z))
          (ordinaryPhysicalGraph F (fun _ _=>False)) (Function.Embedding.inl:V↪V⊕U)
          (ordinaryBoundaryHubSet H Z A) (fun i=>(ordinaryBoundaryRimSet Q A i).image Sum.inl)
          (fun i=>(ordinaryBoundaryRowSet H A Z i).image Sum.inr))) := by
  intro μ Bpot err hmargin hE
  have hh:=ordinary_expanded_adaptive_hub_weights_with_product_prior p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd
    q hq hQ s hs hS ρ ν E a P F A Z π j hconf hnoshort
    pmin pH D δreg ξ Lconf cLo cHi b Bweight η K tHub Ledit density tR tH βe βh hcHi htHub innerWeight setup hmargin hE
  apply hh.trans
  apply finiteLaw_probability_mono
  intro z hz
  refine ⟨hz.1,?_⟩
  exact ordinary_universal_deep_parents_from_raw_prior P F A Z π d kTri j s endpointWeight triangleWeight
    γ κ b Bweight εf η κe pmin (2*p) pH density tR tH Lconf Ledit βe βh parentδ εparent tEndpoint Kscale e
    α pstar βP ηP ηH βH c Btri _ margins parent (hEparent z hz.1) hz.2
end Oberwolfach

module

public import Oberwolfach.OrdinarySampleHubTargetsExpanded
public import Oberwolfach.OrdinaryHubWeightsOfSetup
public import Oberwolfach.OrdinaryTrianglePotentialCoefficientBounds

@[expose] public section
/-! Fixed inner triangle weights, a supplied earlier expanded event, a raw
prior and the reference cuts share one outcome. Every subsequent cleanup
profile on that outcome has the required hub-potential targets. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 3500000
set_option synthInstance.maxSize 4096
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem ordinary_sample_hub_weights_with_expanded_prior
    (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1) (d:ℕ) (hd:2≤d)
    (q:U→Γ→ℝ) (hq:∀u g,0≤q u g) (hQ:∀u,∑g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀u j,0≤s u j)
    (hS:∀u,∑j,s u j≤ intervalUncoveredProbability d (∑g,q u g))
    {R:(∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)→Type}
    [∀σ,Fintype (R σ)] (ρ:∀σ,FiniteLaw (R σ)) (ν:FiniteLaw (Sym2 V→Bool))
    (E:(Σσ,R σ)→Prop) (J:RawWheelOutcome V U Γ Color→Prop) (a b c:ℝ)
    (P F:SimpleGraph V) (A:Finset V) (Z:Finset U) (π:Equiv.Perm V) (j:Color) (δref href:ℝ)
    (hn:0<Fintype.card V) (hU:0<Fintype.card U) (hA:0<A.card)
    (hconf:permutationConflictGraph π (3*d)≤F)
    (hnoshort:∀ x k,0<k→k<2*d+1→(π^k) x≠x)
    (pmin pH D cLo cHi t Ledit ξ density tR tH βe βh:ℝ)
    (hpmin:0<pmin) (hpmin1:pmin≤1) (hR:pmin≤2*p) (hH:pmin≤pH) (hH1:pH≤1)
    (hcLo:0<cLo) (hcHi:0<cHi)
    (hDlo:(A.card:ℝ)/2≤D) (hDhi:D≤2*A.card) (ht:0<t)
    (weight:OrdinaryCycle (P.induce (A:Set V)) 3→ℝ)
    (δ Lconf bweight Bweight η K:ℝ)
    (setup:OrdinaryInnerHubWeightSetup P F A weight pmin (2*p) pH D δ ξ Lconf cLo cHi bweight Bweight η K):
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS);
    let raw:=rawWheelLaw (V:=V) (fun _=>2*p) (fun _=>by linarith) (fun _=>by linarith) d hd q hq hQ s hs hS;
    let μraw:=FiniteLaw.pi raw;
    let Bpot:=4*cHi/pmin^7;
    let err:=(Fintype.card (A:Set V):ℝ)*Fintype.card U *
      (2*Real.exp (-2*t^2/((4*(d:ℝ)+3)^2*((3:ℝ)^4*Bpot/Fintype.card (A:Set V))*(2*3)*((3:ℝ)^2*Bpot))));
    t+(3:ℝ)^2*Bpot*Ledit/Fintype.card (A:Set V)+
      2*(3*(3:ℝ)^4*Bpot*Ledit/Fintype.card (A:Set V))≤ξ→
    1-a≤(μ.sigma ρ).probability E→1-b≤μraw.probability J→
    1-c≤(μraw.prod ν).probability (fun z=>OrdinaryTriangleReferenceMatrixCuts P F π d j δref href z.1 z.2)→
    1-a-b-err-c≤((μ.sigma ρ).prod ν).probability (fun z=>
      let σ:=fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e);
      (E z.1 ∧ (J σ ∧ ∀ (Q : SimpleGraph V) (H : V→U→Prop),
        OrdinaryCleanupParentProfiles P Q F H π d A Z (2*p) pH density tR tH Ledit βe βh s j σ→
        Q≤P → Nonempty (OrdinaryMixedHubWeights bweight Bweight η Q F H A Z))) ∧
      OrdinaryTriangleReferenceNormalizedCuts P F π d j δref href σ z.2):=by
  intro μ raw μraw Bpot err hmargin hE hJ hC
  have hh:=ordinary_sample_hub_targets_with_expanded_prior p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS
    ρ ν E J a b c P F A Z π j δref href hn hU hA hconf hnoshort
    pmin pH D cLo cHi t Ledit ξ density tR tH βe βh hpmin hpmin1 hR hH hH1 hcLo hcHi hDlo hDhi ht
    weight setup.coefficients hmargin hE hJ hC
  apply hh.trans
  apply finiteLaw_probability_mono
  intro z hz
  obtain ⟨⟨hEz,hJz,htarget⟩,hcut⟩:=hz
  refine ⟨⟨hEz,hJz,?_⟩,hcut⟩
  intro Q H profile hQP
  exact ⟨ordinary_hub_weights_of_setup P Q F H A Z weight pmin (2*p) pH D δ ξ Lconf
    cLo cHi bweight Bweight η K setup hQP (htarget Q H profile)⟩
end Oberwolfach

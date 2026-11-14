module

public import Oberwolfach.OrdinaryMatchingCoreWithProtectedReservoir
public import Oberwolfach.OrdinarySampleHubWeightsExpanded

@[expose] public section
/-! The checked matching-core/reservoir event and the adaptive inner hub
weights are carried by one expanded sample and one reference outcome. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option synthInstance.maxSize 65536
set_option maxRecDepth 32768
set_option maxHeartbeats 20000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance (priority := high) matchingHubSameSampleFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem ordinary_matching_core_and_inner_hub_weights
    (K d m:ℕ) (hd:2≤d) (hm:3≤m) (ρ₀ BM t ξ ζ:ℝ)
    (hρ₀:0<ρ₀) (hBM:0<BM) (ht:0<t) (hξ:0<ξ) (hζ:0<ζ)
    (BO:Fin K→ℝ) (hBO:∀i,0<BO i):
    ∃N:ℕ,∀n:ℕ,N≤n→0<n→
    ∀(U:Type) [Fintype U] [DecidableEq U],Fintype.card U≤n→
    ∀(F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (hK:0<K) (i₀:Fin K) (rsv θ c ρ D:ℝ)
    (hs0:0≤rsv) (hs1:rsv≤1/100) (hθ:0<θ) (hθ1:θ≤1/100) (hc:8≤c)
    (hda:1/θ≤d) (hρlo:ρ₀≤ρ) (hρ:0<ρ) (hρ1:ρ≤1) (hD:0<D)
    (hsize:ρ*D=2*(Fintype.card U:ℝ))
    (Allowed:Set ℕ) (hAllowed:∀u,AllowedCycleLengths (F u) Allowed)
    (hsclass:rsv≤1/(2*(K:ℝ))) (hclass:∀u,factorPreparationClass (F u) K=some i₀)
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n))
    (τ A:ℝ) (weight:(Fin (m+1)→Fin n)→ℝ)
    (hw:SuccessorSequenceWeightConditions (ordinaryEligibleHost P π d) π (3*d) D τ A BM weight)
    (hDlo:(n:ℝ)/2≤D) (hDhi:D≤2*n)
    (w:∀i:Fin K,OrdinaryCycle (ordinaryEligibleHost P π d) (longPaddedSeedExponent i+2)→ℝ)
    (hw0:∀i C,0≤w i C) (hwupper:∀i C,w i C≤BO i/(n:ℝ)^(longPaddedSeedExponent i))
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (p₁ k₁ k₂ u:ℝ) (hp₁:0≤p₁) (hk₁:0≤k₁) (hk₂:0≤k₂) (hu:0≤u),
    let q:=ordinaryAssignedMarkedProbability F hF K θ c
    let s:=ordinaryAssignedSpokeProbability F hF K i₀ rsv θ c
    let p₂:=ordinaryAssignedApproxRimProbability F hF i₀ rsv θ c D;
    ∀(hq:∀u g,0≤q u g) (hQ:∀u,∑g,q u g≤1/8)
      (hs:∀u j,0≤s u j) (hS:∀u,(∑ j,s u j) ≤ intervalUncoveredProbability d (∑g,q u g))
      (hp₂:0≤p₂) (hsum:2*p₁+2*k₁+2*p₂+2*k₂+u≤1)
      {R:(∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)→Type}
      [∀σ,Fintype (R σ)] (ν:∀σ,FiniteLaw (R σ))
      (E:(Σσ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e,R σ)→Prop) (εE:ℝ)
      (rRes mRes tRes fRes aRes bRes:ℕ) (εRes:ℝ) (Fbad:SimpleGraph (Fin n)) (εA:ℝ)
      (I:Finset (Fin n)) (Z:Finset U) (hI:0<I.card)
      (pmin Dinner cLo cHi tHub Ledit ξHub density tR tH βe βh δreg Lconf bweight Bweight ηHub Kscale:ℝ)
      (hpmin:0<pmin) (hpminR:pmin≤2*p₁) (hpminH:pmin≤rsv) (hcHi:0<cHi) (htHub:0<tHub)
      (triWeight:OrdinaryCycle (P.induce (I:Set (Fin n))) 3→ℝ)
      (setup:OrdinaryInnerHubWeightSetup P Fbad I triWeight pmin (2*p₁) rsv Dinner δreg ξHub Lconf
        cLo cHi bweight Bweight ηHub Kscale)
      (hconf:permutationConflictGraph π (3*d)≤Fbad)
      (J:RawWheelOutcome (Fin n) U Bool Bool→Prop) (εJ εC δref href:ℝ) (νref:FiniteLaw (Sym2 (Fin n)→Bool)),
    let Aref:=fun σ:RawWheelOutcome (Fin n) U Bool Bool=>
      OrdinaryUniformProtectedReservoirEvent rRes mRes tRes fRes aRes bRes εRes
        (rawWheelGraph P σ\Fbad) Fbad (rawWheelSpokes π d σ false)
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=Fin n) p₁ k₁ p₂ k₂ u hp₁ hk₁ hp₂ hk₂ hu hsum d hd q hq hQ s hs hS)
    let wM:=fun (_:Unit)=>ordinaryAssignedShiftedSeed F hF i₀ rsv θ c D π d m weight
    let wO:=ordinaryAssignedUnshiftedSeed F hF i₀ rsv θ c D (ordinaryEligibleHost P π d) π d w;
    let rawLaw:=rawWheelLaw (V:=Fin n) (fun _=>2*p₁) (fun _=>by linarith) (fun _=>by linarith) d hd q hq hQ s hs hS;
    let Bpot:=4*cHi/pmin^7;
    let err:=(Fintype.card (I:Set (Fin n)):ℝ)*Fintype.card U *
      (2*Real.exp (-2*tHub^2/((4*(d:ℝ)+3)^2*((3:ℝ)^4*Bpot/Fintype.card (I:Set (Fin n)))*(2*3)*((3:ℝ)^2*Bpot))));
    tHub+(3:ℝ)^2*Bpot*Ledit/Fintype.card (I:Set (Fin n))+
      2*(3*(3:ℝ)^4*Bpot*Ledit/Fintype.card (I:Set (Fin n)))≤ξHub→
    1-εA≤(FiniteLaw.pi rawLaw).probability Aref →
    1-εE≤(μ.sigma ν).probability E→
    1-εJ≤(FiniteLaw.pi rawLaw).probability J→
    1-εC≤((FiniteLaw.pi rawLaw).prod νref).probability
      (fun z=>OrdinaryTriangleReferenceMatrixCuts P Fbad π d false δref href z.1 z.2)→
    1-((εE+εA)+ζ)-εJ-err-εC≤((μ.sigma ν).prod νref).probability (fun z=>
      let raw:=fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e);
      (((E z.1 ∧ Aref raw) ∧
        OrdinaryShiftedMatchingCoreEvent (ordinaryEligibleHost P π d) π d m p₂ k₂ q s (wM ()) wO t ξ z.1.1) ∧
        (J raw ∧ ∀ (Q:SimpleGraph (Fin n)) (H:Fin n→U→Prop),
          OrdinaryCleanupParentProfiles P Q Fbad H π d I Z (2*p₁) rsv density tR tH Ledit βe βh s false raw →
          Q≤P → Nonempty (OrdinaryMixedHubWeights bweight Bweight ηHub Q Fbad H I Z))) ∧
        OrdinaryTriangleReferenceNormalizedCuts P Fbad π d false δref href raw z.2):=by
  obtain ⟨N,hMain⟩:=ordinary_assigned_matching_core_with_protected_reservoir_event
    K d m hd hm ρ₀ BM t ξ ζ hρ₀ hBM ht hξ hζ BO hBO
  refine ⟨N,?_⟩
  intro n hn hn0 U _ _ hUn F hF hK i₀ rsv θ c ρ D hs0 hs1 hθ hθ1 hc hda hρlo hρ hρ1 hD hsize Allowed hAllowed hsclass hclass
    P π τ A weight hw hDlo hDhi w hw0 hwupper hnoshort p₁ k₁ k₂ u hp₁ hk₁ hk₂ hu q s p₂ hq hQ hs hS hp₂ hsum R _ ν E εE
    rRes mRes tRes fRes aRes bRes εRes Fbad εA I Z hI pmin Dinner cLo cHi tHub Ledit ξHub density tR tH βe βh δreg Lconf
    bweight Bweight ηHub Kscale hpmin hpminR hpminH hcHi htHub triWeight setup hconf J εJ εC δref href νref
    Aref μ wM wO rawLaw Bpot err hmargin hAref hE hJ hC
  have hMatching:=hMain n hn hn0 U hUn F hF hK i₀ rsv θ c ρ D hs0 hs1 hθ hθ1 hc hda hρlo hρ hρ1 hD hsize
    Allowed hAllowed hsclass hclass P π τ A weight hw hDlo hDhi w hw0 hwupper hnoshort
    p₁ k₁ k₂ u hp₁ hk₁ hk₂ hu hq hQ hs hS hp₂ hsum ν E εE
    rRes mRes tRes fRes aRes bRes εRes Fbad εA hAref hE
  have hUpos:0<Fintype.card U:=by
    have hreal:(0:ℝ)<Fintype.card U:=by have hh:=mul_pos hρ hD; linarith
    exact_mod_cast hreal
  have hpmin1:pmin≤1:=by linarith
  have hrsv1:rsv≤1:=by linarith
  let Ematch:=(fun z=>(E z ∧ Aref (fun e=>expandedOrdinarySelectedCollapse e (z.1 e))) ∧
    OrdinaryShiftedMatchingCoreEvent (ordinaryEligibleHost P π d) π d m p₂ k₂ q s (wM ()) wO t ξ z.1)
  have hh:=ordinary_sample_hub_weights_with_expanded_prior p₁ k₁ p₂ k₂ u hp₁ hk₁ hp₂ hk₂ hu hsum d hd q hq hQ s hs hS
    ν νref Ematch J ((εE+εA)+ζ) εJ εC P Fbad I Z π false δref href (by simpa using hn0) hUpos hI hconf hnoshort
    pmin rsv Dinner cLo cHi tHub Ledit ξHub density tR tH βe βh hpmin hpmin1 hpminR hpminH hrsv1 setup.lower_pos hcHi
    setup.center_lower setup.center_upper htHub triWeight δreg Lconf bweight Bweight ηHub Kscale setup
    hmargin hMatching hJ hC
  convert hh using 1 <;> congr!
end Oberwolfach

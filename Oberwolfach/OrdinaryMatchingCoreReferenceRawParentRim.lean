module

public import Oberwolfach.OrdinaryMatchingCoreWithReferenceEvent
public import Oberwolfach.OrdinaryUniformProtectedReservoirEvent
public import Oberwolfach.OrdinaryExpandedRawParentReferenceRim

@[expose] public section
/-! The assigned matching core and the fixed universal ordinary reservoir
are properties of the same expanded outcome and dependent second stage. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 65536
set_option maxHeartbeats 30000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance (priority := high) assignedMatchingGeneralRawPriorFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem ordinary_assigned_matching_core_reference_and_raw_parent_rim_event
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
      (Aref:RawWheelOutcome (Fin n) U Bool Bool→Prop) (εA:ℝ) (Fbad:SimpleGraph (Fin n))
      (I:Finset (Fin n)) (Z:Finset U) (k:ℕ)
      (endpointWeight:Fin n→Sym2 (Fin n⊕U)→ℝ) (triangleWeight:OrdinaryCycle P 3→ℝ)
      (α pstar βP ηP ηH βH cW BW tEnd tR tH δref href αinner εG:ℝ),
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=Fin n) p₁ k₁ p₂ k₂ u hp₁ hk₁ hp₂ hk₂ hu hsum d hd q hq hQ s hs hS)
    let wM:=fun (_:Unit)=>ordinaryAssignedShiftedSeed F hF i₀ rsv θ c D π d m weight
    let wO:=ordinaryAssignedUnshiftedSeed F hF i₀ rsv θ c D (ordinaryEligibleHost P π d) π d w;
    1-εA≤(FiniteLaw.pi (rawWheelLaw (V:=Fin n) (fun _=>2*p₁)
      (fun _=>by linarith) (fun _=>by linarith) d hd q hq hQ s hs hS)).probability Aref →
    1-εE≤(μ.sigma ν).probability E→
    let μraw:=FiniteLaw.pi (rawWheelLaw (V:=Fin n) (fun _=>2*p₁)
      (fun _=>by linarith) (fun _=>by linarith) d hd q hq hQ s hs hS)
    let νcoins:=FiniteLaw.pi (fun _ : Sym2 (Fin n)=>FiniteLaw.fairCoin)
    let Good:=fun z:RawWheelOutcome (Fin n) U Bool Bool×(Sym2 (Fin n)→Bool)=>
      OrdinaryRawHubParentPrior d k P Fbad I Z π false s endpointWeight triangleWeight
        α pstar βP ηP ηH βH cW BW (2*p₁) rsv tEnd tR tH z.1 ∧
      OrdinaryTriangleReferenceMatrixCuts P Fbad π d false δref href z.1 z.2 ∧
      OrdinaryInducedRimCutEvent I (sampledOrientation (rawWheelGraph P z.1) z.2) αinner pstar;
    1-εG≤(μraw.prod νcoins).probability Good →
    1-((εE+εA)+ζ)-εG≤((μ.sigma ν).prod νcoins).probability (fun z=>
      let raw:=fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e);
      ((E z.1 ∧ Aref raw) ∧
        OrdinaryShiftedMatchingCoreEvent (ordinaryEligibleHost P π d) π d m p₂ k₂ q s (wM ()) wO t ξ z.1.1) ∧
      Good (raw,z.2)) := by
  obtain ⟨N,hMain⟩:=ordinary_assigned_matching_core_with_reference_event K d m hd hm ρ₀ BM t ξ ζ hρ₀ hBM ht hξ hζ BO hBO
  refine ⟨N,?_⟩
  intro n hn hn0 U _ _ hUn F hF hK i₀ rsv θ c ρ D hs0 hs1 hθ hθ1 hc hda hρlo hρ hρ1 hD hsize Allowed hAllowed hsclass hclass
    P π τ A weight hw hDlo hDhi w hw0 hwupper hnoshort p₁ k₁ k₂ u hp₁ hk₁ hk₂ hu q s p₂ hq hQ hs hS hp₂ hsum R _ ν E εE
    Aref εA Fbad I Z k endpointWeight triangleWeight
    α pstar βP ηP ηH βH cW BW tEnd tR tH δref href αinner εG μ wM wO hA hE μraw νcoins Good hGood
  have hmatching:=hMain n hn hn0 U hUn F hF hK i₀ rsv θ c ρ D hs0 hs1 hθ hθ1 hc hda hρlo hρ hρ1 hD hsize
    Allowed hAllowed hsclass hclass P π τ A weight hw hDlo hDhi w hw0 hwupper hnoshort
    p₁ k₁ k₂ u hp₁ hk₁ hk₂ hu hq hQ hs hS hp₂ hsum ν E εE Aref εA hA hE
  let Ebase : (Σσ,R σ)→Prop := fun z=>(E z ∧ Aref (fun e=>expandedOrdinarySelectedCollapse e (z.1 e))) ∧
    OrdinaryShiftedMatchingCoreEvent (ordinaryEligibleHost P π d) π d m p₂ k₂ q s (wM ()) wO t ξ z.1
  let Eprior : (Σσ,R σ)×(Sym2 (Fin n)→Bool)→Prop := fun z=>Ebase z.1
  have hprior:1-((εE+εA)+ζ)≤((μ.sigma ν).prod νcoins).probability Eprior:=by
    dsimp only [Eprior]
    rw [finiteLaw_prod_first_probability]
    exact hmatching
  have hh:=ordinary_expanded_raw_parent_reference_rim_with_prior P Fbad I Z π d k hd p₁ k₁ p₂ k₂ u rsv
    hp₁ hk₁ hp₂ hk₂ hu hsum q hq hQ s hs hS false endpointWeight triangleWeight
    α pstar βP ηP ηH βH cW BW tEnd tR tH δref href αinner ν Eprior ((εE+εA)+ζ) εG hprior hGood
  exact hh

end Oberwolfach

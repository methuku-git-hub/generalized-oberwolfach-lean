module

public import Oberwolfach.OrdinaryMatchingCoreWithProtectedReservoir
public import Oberwolfach.OrdinaryAssignedProtectedReservoirHighProbability

@[expose] public section
/-! The assigned matching core and universal reservoir hold with high
probability on one expanded outcome and any dependent second stage. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 65536
set_option maxHeartbeats 50000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance (priority := high) assignedMatchingProtectedReservoirCombinedFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem ordinary_assigned_matching_core_and_protected_reservoir_high_probability
    (K d m:ℕ) (hd:2≤d) (hm:3≤m) (ρ₀ BM t ξ ζ:ℝ)
    (hρ₀:0<ρ₀) (hBM:0<BM) (ht:0<t) (hξ:0<ξ) (hζ:0<ζ)
    (BO:Fin K→ℝ) (hBO:∀i,0<BO i)
    (rRes:ℕ) (hrRes:3≤rRes) (α pmin smin L ω:ℝ)
    (hα:0<α) (hpmin:0<pmin) (hsmin:0<smin) (hsmin1:smin≤1) (hω:0<ω) (hL:0≤L):
    ∃ εabs εtrans εsample:ℝ,0<εabs ∧ 0<εtrans ∧ 0<εsample ∧
    ∀mRes:ℕ,∃aRes bRes tR:ℕ,1≤tR ∧ ∀tRes fRes:ℕ,∃N:ℕ,
    ∀n:ℕ,N≤n→0<n→
    ∀(U:Type) [Fintype U] [DecidableEq U],Fintype.card U≤n→ω*n≤(Fintype.card U:ℝ)→
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
      (Fbad:SimpleGraph (Fin n)),
    let Aref:=fun σ:RawWheelOutcome (Fin n) U Bool Bool=>
      OrdinaryUniformProtectedReservoirEvent rRes mRes tRes fRes aRes bRes εabs
        (rawWheelGraph P σ\Fbad) Fbad (rawWheelSpokes π d σ false)
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=Fin n) p₁ k₁ p₂ k₂ u hp₁ hk₁ hp₂ hk₂ hu hsum d hd q hq hQ s hs hS)
    let wM:=fun (_:Unit)=>ordinaryAssignedShiftedSeed F hF i₀ rsv θ c D π d m weight
    let wO:=ordinaryAssignedUnshiftedSeed F hF i₀ rsv θ c D (ordinaryEligibleHost P π d) π d w;
    permutationConflictGraph π (3*d)≤Fbad →
    (∀v,(Fbad.degree v:ℝ)≤L) →
    (∀v,(cycleThreshold rRes+α)*n≤(P.degree v:ℝ)) →
    (∀v,|(P.degree v:ℝ)-D|≤εsample*n) →
    pmin≤2*p₁ → smin≤rsv →
    1-εE≤(μ.sigma ν).probability E→
    1-((εE+(1/(n:ℝ)+2/(n:ℝ)^2))+ζ)≤(μ.sigma ν).probability (fun z=>
      (E z ∧ Aref (fun e=>expandedOrdinarySelectedCollapse e (z.1 e))) ∧
      OrdinaryShiftedMatchingCoreEvent (ordinaryEligibleHost P π d) π d m p₂ k₂ q s (wM ()) wO t ξ z.1) :=by
  obtain ⟨Nmatch,hMatch⟩:=ordinary_assigned_matching_core_with_protected_reservoir_event
    K d m hd hm ρ₀ BM t ξ ζ hρ₀ hBM ht hξ hζ BO hBO
  obtain ⟨εabs,εtrans,εsample,hεabs,hεtrans,hεsample,hRes⟩:=
    ordinary_assigned_protected_reservoir_high_probability rRes d hrRes hd α pmin smin L ω hα hpmin hsmin hsmin1 hω hL
  refine ⟨εabs,εtrans,εsample,hεabs,hεtrans,hεsample,?_⟩
  intro mRes
  obtain ⟨aRes,bRes,tR,htR,hRes⟩:=hRes mRes
  refine ⟨aRes,bRes,tR,htR,?_⟩
  intro tRes fRes
  obtain ⟨Nres,hRes⟩:=hRes tRes fRes
  refine ⟨max Nmatch Nres,?_⟩
  intro n hn hn0 U _ _ hUn hlo F hF hK i₀ rsv θ c ρ D hs0 hs1 hθ hθ1 hc hda hρlo hρ hρ1 hD hsize Allowed hAllowed hsclass hclass
    P π τ A weight hw hDlo hDhi w hw0 hwupper hnoshort p₁ k₁ k₂ u hp₁ hk₁ hk₂ hu q s p₂ hq hQ hs hS hp₂ hsum R _ ν E εE Fbad Aref μ wM wO hFbad hdeg hP hnear hp hRsv hE
  have hp1:2*p₁≤1:=by linarith
  have hrsv1:rsv≤1:=by linarith
  have hA:=hRes n (by omega) U hUn hlo P Fbad π hFbad hnoshort hdeg hP D hDlo hDhi hnear
    (2*p₁) hp hp1 F hF K i₀ rsv θ c hRsv hrsv1 hq hQ hs hS
  exact hMatch n (by omega) hn0 U hUn F hF hK i₀ rsv θ c ρ D hs0 hs1 hθ hθ1 hc hda hρlo hρ hρ1 hD hsize
    Allowed hAllowed hsclass hclass P π τ A weight hw hDlo hDhi w hw0 hwupper hnoshort
    p₁ k₁ k₂ u hp₁ hk₁ hk₂ hu hq hQ hs hS hp₂ hsum ν E εE
    rRes mRes tRes fRes aRes bRes εabs Fbad (1/(n:ℝ)+2/(n:ℝ)^2) hA hE
end Oberwolfach

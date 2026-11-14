module

public import Oberwolfach.OrdinaryAssignedNamedSeeds
public import Oberwolfach.OrdinaryAssignedEligibleMatchingTests
public import Oberwolfach.ExpandedRawSpokeAnyStage
public import Oberwolfach.LongAssignedSpokeFailureUniform
public import Oberwolfach.OrdinaryAssignedEligibleLoadsOnCommonEvent
public import Oberwolfach.ExpandedApproximatePositiveSpokesEvent
public import Oberwolfach.OrdinaryShiftedMixedLoadEvent
public import Oberwolfach.OrdinaryEligibleHost

@[expose] public section
/-! Add the actual assigned approximate-wheel tests on the eligible host
to any pre-existing event on the same expanded sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 65536
set_option maxHeartbeats 20000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance (priority := high) assignedEligibleMatchingBundleFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem ordinary_assigned_eligible_matching_bundle_on_common_event
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
      (E:(Σσ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e,R σ)→Prop) (εE:ℝ),
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=Fin n) p₁ k₁ p₂ k₂ u hp₁ hk₁ hp₂ hk₂ hu hsum d hd q hq hQ s hs hS)
    let wM:=fun (_:Unit)=>ordinaryAssignedShiftedSeed F hF i₀ rsv θ c D π d m weight
    let wO:=ordinaryAssignedUnshiftedSeed F hF i₀ rsv θ c D (ordinaryEligibleHost P π d) π d w;
    1-εE≤(μ.sigma ν).probability E→
    1-(εE+ζ)≤(μ.sigma ν).probability (fun z=>
      ((E z ∧ OrdinaryShiftedMixedLoadEvent (ordinaryEligibleHost P π d) π d m
        (fun i:Fin K=>longPaddedSeedExponent i+1) p₂ k₂ q s
        (fun _ _=>True) (fun _ _=>True) wM (fun _=>true) (fun _=>true)
        wO (fun _=>true) (fun _=>true) t (fun _=>t) z.1) ∧
      OrdinaryExpandedHubTotalEvent (ordinaryEligibleHost P π d) π d
        (fun i:Fin K=>longPaddedSeedExponent i+1) p₂ k₂ q s wO (fun _=>true) (fun _=>true) (fun _=>t) z.1 ∧
      (∀g j v u,rawMarkedPairSpokes π d (fun e=>rawExpandedApproximateCollapse e (z.1 e)) g j true v u→q u g≠0)) ∧
      (∀b u,|rawMarkedRestrictedSpokeCol π d (fun e=>z.1 (Sum.inr e)) true true b u Finset.univ-
        (if b then q u true else s u true)*(n:ℝ)|<ξ*n)) :=by
  obtain ⟨N₁,hN₁⟩:=ordinary_assigned_eligible_matching_tests_on_common_event K d m hd hm ρ₀ BM t (ζ/2)
    hρ₀ hBM ht (by positivity) BO hBO
  obtain ⟨N₂,hN₂⟩:=eventually_assigned_spoke_failure_below d ξ (ζ/2) hξ (by positivity)
  refine ⟨max N₁ N₂,?_⟩
  intro n hn hn0 U _ _ hUn F hF hK i₀ rsv θ c ρ D hs0 hs1 hθ hθ1 hc hda hρlo hρ hρ1 hD hsize Allowed hAllowed hsclass hclass
    P π τ A weight hw hDlo hDhi w hw0 hwupper hnoshort p₁ k₁ k₂ u hp₁ hk₁ hk₂ hu q s p₂ hq hQ hs hS hp₂ hsum R _ ν E εE μ wM wO hE
  let Etests:=fun z=>
    (E z ∧ OrdinaryShiftedMixedLoadEvent (ordinaryEligibleHost P π d) π d m
      (fun i:Fin K=>longPaddedSeedExponent i+1) p₂ k₂ q s
      (fun _ _=>True) (fun _ _=>True) wM (fun _=>true) (fun _=>true)
      wO (fun _=>true) (fun _=>true) t (fun _=>t) z.1) ∧
    OrdinaryExpandedHubTotalEvent (ordinaryEligibleHost P π d) π d
      (fun i:Fin K=>longPaddedSeedExponent i+1) p₂ k₂ q s wO (fun _=>true) (fun _=>true) (fun _=>t) z.1 ∧
    (∀g j v u,rawMarkedPairSpokes π d (fun e=>rawExpandedApproximateCollapse e (z.1 e)) g j true v u→q u g≠0)
  have htests:=hN₁ n (by omega) hn0 U hUn F hF hK i₀ rsv θ c ρ D hs0 hs1 hθ hθ1 hc hda hρlo hρ hρ1 hD hsize
    Allowed hAllowed hsclass hclass P π τ A weight hw hDlo hDhi w hw0 hwupper hnoshort
    p₁ k₁ k₂ u hp₁ hk₁ hk₂ hu hq hQ hs hS hp₂ hsum ν E εE hE
  change 1-(εE+ζ/2)≤(μ.sigma ν).probability Etests at htests
  letI:Nonempty (Fin n):=⟨⟨0,hn0⟩⟩
  have hcounts:=expanded_raw_spoke_hub_counts_any_stage π d hd false true true p₁ k₁ p₂ k₂ u
    hp₁ hk₁ hp₂ hk₂ hu hsum q hq hQ s hs hS hnoshort (ξ*n) (by positivity) ν Etests (εE+ζ/2) htests
  have hfailure:=hN₂ n (by omega) U hUn
  have hnum:1-(εE+ζ)≤1-(εE+ζ/2)-4*(Fintype.card U:ℝ)*Real.exp
      (-2*(ξ*(n:ℝ))^2/((4*(d:ℝ)+3)^2*(n:ℝ))):=by linarith
  apply hnum.trans
  simpa only [Fintype.card_fin] using hcounts
end Oberwolfach

module

public import Oberwolfach.OrdinaryAssignedNamedSeeds
public import Oberwolfach.ExpandedOrdinaryHubTotalsAddEvent
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
local instance (priority := high) assignedEligibleTotalsFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem ordinary_assigned_eligible_hub_totals_on_common_event
    (K d m:ℕ) (hd:2≤d) (hm:3≤m) (ρ₀ BM t ζ:ℝ)
    (hρ₀:0<ρ₀) (hBM:0<BM) (ht:0<t) (hζ:0<ζ)
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
    1-(εE+ζ)≤(μ.sigma ν).probability (fun z=>E z ∧
      OrdinaryExpandedHubTotalEvent (ordinaryEligibleHost P π d) π d
        (fun i:Fin K=>longPaddedSeedExponent i+1) p₂ k₂ q s
        wO (fun _=>true) (fun _=>true) (fun _=>t) z.1) :=by
  let pstar:=min (1/2:ℝ) (ρ₀/4)
  let BOseed:=fun i:Fin K=>2*BO i/pstar^(2*(longPaddedSeedExponent i+2))
  have hpstar:0<pstar:=by dsimp [pstar];positivity
  have hBOseed:∀i,0<BOseed i:=by
    intro i
    dsimp [BOseed]
    exact div_pos (mul_pos (by norm_num) (hBO i)) (pow_pos hpstar _)
  obtain ⟨N,_,hN⟩:=expanded_ordinary_hub_totals_add_to_event (Fin K) d hd
    (fun i=>longPaddedSeedExponent i+1) (fun i=>by have hh:=long_padded_seed_exponent_positive i;omega)
    BOseed (fun _=>t) hBOseed (fun _=>ht) ζ hζ
  refine ⟨N,?_⟩
  intro n hn hn0 U _ _ hUn F hF hK i₀ rsv θ c ρ D hs0 hs1 hθ hθ1 hc hda hρlo hρ hρ1 hD hsize Allowed hAllowed hsclass hclass
    P π τ A weight hw hDlo hDhi w hw0 hwupper hnoshort p₁ k₁ k₂ u hp₁ hk₁ hk₂ hu q s p₂ hq hQ hs hS hp₂ hsum R _ ν E εE μ wM wO hE
  have hb:=ordinary_assigned_named_seed_bounds hn0 F hF hK i₀ rsv θ c ρ₀ ρ D d m hd (by omega)
    hs0 hs1 hθ hθ1 hc hda hρ₀ hρlo hρ hρ1 hD hsize Allowed hAllowed hsclass hclass
    (ordinaryEligibleHost P π d) π τ A BM weight hw hDlo hDhi hBM.le BO (fun i=>(hBO i).le) w hw0 hwupper
  have hO:∀i W,0≤wO i W ∧ wO i W≤BOseed i/(Fintype.card (Fin n):ℝ)^(longPaddedSeedExponent i+1):=by
    intro i W
    simpa only [wO,BOseed,pstar,Fintype.card_fin] using hb.2.2 i W
  have hh:=hN (Fin n) U Bool Bool (by simpa using hn) (by simpa using hUn)
    (ordinaryEligibleHost P π d) π p₁ k₁ p₂ k₂ u hp₁ hk₁ hp₂ hk₂ hu hsum q hq hQ s hs hS hnoshort
    wO hO (fun _=>true) (fun _=>true) ν E εE hE
  exact hh
end Oberwolfach

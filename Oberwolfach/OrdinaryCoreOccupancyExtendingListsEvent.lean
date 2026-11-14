module

public import Oberwolfach.OrdinaryCoreOccupancyListTestsEvent
public import Oberwolfach.OrdinarySelectedProtectedListsAfterDeletion
public import Oberwolfach.ExpandedSelectedTwoPathsAndEvent
public import Oberwolfach.ExpandedSelectedNeighbourAndEvent
public import Oberwolfach.ExpandedIntervalOccupancyAndEvent
public import Oberwolfach.OrdinaryAssignedMarkedProbabilityUpperGeneral
public import Oberwolfach.ExpandedRawStartsAnyStage
public import Oberwolfach.OrdinaryStartFailureUniform
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
local instance (priority := high) assignedMatchingCoreListsFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem ordinary_assigned_core_occupancy_and_extending_lists_on_common_event
    (K d m:ℕ) (hd:2≤d) (hm:3≤m) (ρ₀ BM t ξ ζ:ℝ)
    (hρ₀:0<ρ₀) (hBM:0<BM) (ht:0<t) (hξ:0<ξ) (hζ:0<ζ)
    (BO:Fin K→ℝ) (hBO:∀i,0<BO i):
    ∃N:ℕ,∀n:ℕ,N≤n→0<n→
    ∀(U:Type) [Fintype U] [DecidableEq U],Fintype.card U≤n→
    ∀(F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (hK:0<K) (i₀:Fin K) (rsv θ c ρ D:ℝ)
    (hs0:0≤rsv) (hs1:rsv≤1/100) (hθ:0<θ) (hθ1:θ≤1/100) (hc:8≤c) (hcEq:c=(m:ℝ)+1)
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
    (p₁ k₁ k₂ u:ℝ) (hp₁:0≤p₁) (hk₁:0≤k₁) (hk₂:0≤k₂) (hu:0≤u)
    (γList pstarList βList lamList ζDel:ℝ) (hγList:0≤γList) (hpstarList:0≤pstarList)
    (hpstar: pstarList≤p₁) (hβList:0≤βList) (hlamList:0≤lamList) (hζDel:0≤ζDel)
    (hdegList:∀x,(1/2+γList)*n≤(P.degree x:ℝ))
    (herrorList:(n:ℝ)^(3/4:ℝ)+2*(2*((3*d:ℕ):ℝ)+1)≤γList*pstarList^2*n)
    (hmarginList:βList*n+(n:ℝ)^(3/4:ℝ)≤(γList*pstarList^2)*n*(θ/2))
    (hbudgetList:(lamList+2*ζDel)*n+((n:ℝ)+2*(n:ℝ)^(3/4:ℝ))/d≤βList*n),
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
    1-(εE+4*ζ)≤(μ.sigma ν).probability (fun z=>
      E z ∧ OrdinaryShiftedMatchingCoreEvent (ordinaryEligibleHost P π d) π d m p₂ k₂ q s (wM ()) wO t ξ z.1 ∧
      (∀v,((rawIntervalExtendedAnyHubSet π d (fun e=>z.1 (Sum.inr e)) v).card:ℝ)≤
        4*(Fintype.card U:ℝ)/c+4*(n:ℝ)^(3/4:ℝ)) ∧
      ∀(tret:ℕ) (Jret:StartRetentionOutcome (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) false) tret)
        (Del:SimpleGraph (Fin n)),(∀x,(Del.degree x:ℝ)≤ζDel*n)→∀w,
        IsExtendingList (fun x y=>rawSelectedPhysicalRelation P π d (fun e=>z.1 (Sum.inl e)) x y ∧ ¬Del.Adj x y)
          (rawIntervalProtectedUnassignedList π d (fun e=>z.1 (Sum.inr e)) false true tret Jret w) lamList) :=by
  obtain ⟨N,hN⟩:=ordinary_assigned_core_occupancy_and_list_tests_on_common_event K d m hd hm ρ₀ BM t ξ ζ hρ₀ hBM ht hξ hζ BO hBO
  refine ⟨max N 2,?_⟩
  intro n hn hn0 U _ _ hUn F hF hK i₀ rsv θ c ρ D hs0 hs1 hθ hθ1 hc hcEq hda hρlo hρ hρ1 hD hsize Allowed hAllowed hsclass hclass
    P π τ A weight hw hDlo hDhi w hw0 hwupper hnoshort p₁ k₁ k₂ u hp₁ hk₁ hk₂ hu γList pstarList βList lamList ζDel hγList hpstarList hpstar hβList hlamList hζDel hdegList herrorList hmarginList hbudgetList
    q s p₂ hq hQ hs hS hp₂ hsum R _ ν E εE μ wM wO hE
  have hh:=hN n (by omega) hn0 U hUn F hF hK i₀ rsv θ c ρ D hs0 hs1 hθ hθ1 hc hda hρlo hρ hρ1 hD hsize
    Allowed hAllowed hsclass hclass P π τ A weight hw hDlo hDhi w hw0 hwupper hnoshort p₁ k₁ k₂ u hp₁ hk₁ hk₂ hu
    hq hQ hs hS hp₂ hsum ν E εE hE
  apply hh.trans
  apply finiteLaw_probability_mono
  intro z hz
  obtain ⟨hE',hcore,hOcc,hNeighbour,hPaths⟩:=hz
  refine ⟨hE',hcore,hOcc,?_⟩
  intro tret Jret Del hDel
  have hStarts:∀v g,|rawIntervalHubStartCount π d g (fun e=>z.1 (Sum.inr e)) v-
      (n:ℝ)*ordinaryAssignedMarkedProbability F hF K θ ((m:ℝ)+1) v g/d|<(n:ℝ)^(3/4:ℝ)/d:=by
    have hh:=hcore.2.2.2
    have hdec:instDecidableEqFin n=assignedMatchingCoreListsFin n:=Subsingleton.elim _ _
    rw [hdec] at hh
    simpa only [q,hcEq,rawExpandedApproximateCollapse,id_eq] using hh
  have hNeighbour':∀v i,|rawIntervalUnassignedHubCountOn π d (fun e=>z.1 (Sum.inr e)) v
      (rawSelectedNeighbourTestSet P π d (fun e=>z.1 (Sum.inl e)) i)-
      (rawSelectedNeighbourTestSet P π d (fun e=>z.1 (Sum.inl e)) i).card*
        (1-(∑g,ordinaryAssignedMarkedProbability F hF K θ ((m:ℝ)+1) v g)-
          (∑j,ordinaryAssignedSpokeProbability F hF K i₀ rsv θ ((m:ℝ)+1) v j))|<(n:ℝ)^(3/4:ℝ):=by
    simpa only [q,s,hcEq] using hNeighbour
  have hm7:7≤m:=by
    have hmR:(7:ℝ)≤m:=by linarith [hc,hcEq]
    exact_mod_cast hmR
  exact ordinary_assigned_selected_protected_lists_after_deletion (by omega) hK m d hm7 hd F hF Allowed hAllowed i₀ rsv θ ρ D
    hs0 hs1 hθ hθ1 hda hρ hρ1 hD hsize hsclass hclass P π (fun e=>z.1 (Sum.inl e)) (fun e=>z.1 (Sum.inr e))
    tret Jret γList pstarList p₁ βList lamList ζDel hγList hpstarList hpstar hβList hlamList hζDel hdegList herrorList hmarginList hbudgetList
    hPaths hNeighbour' hStarts Del hDel
end Oberwolfach

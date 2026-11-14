module

public import Oberwolfach.OrdinaryClassReserveBound
public import Oberwolfach.CandidateOrdinaryAssignedRetainedEventRootTargetsNative
public import Oberwolfach.OrdinaryAssignedRetainedEventRootTargetsNative
public import Oberwolfach.OrdinaryCandidateClassReservation
public import Oberwolfach.CandidateOrdinaryAssignedApproximateDensityBoundsDirectReserve
public import Oberwolfach.CandidateOrdinaryAssignedEligibleFiberNormalizationDirectReserve
public import Oberwolfach.CandidateOrdinaryAssignedNamedSeedsDirectReserve
public import Oberwolfach.OrdinaryShiftedRetainedEventRootTargets
public import Oberwolfach.OrdinaryAssignedNonretainedZero
public import Oberwolfach.OrdinaryAssignedEligibleFiberNormalization
public import Oberwolfach.OrdinaryAssignedNamedSeeds
public import Oberwolfach.OrdinaryAssignedSeedFactorization
public import Oberwolfach.OrdinaryCycleSumInstance

@[expose] public section
/-! On the ordinary assigned-weight load event, the realized mixed wheel
hypergraph has near-unit physical degrees on the same expanded sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]

theorem ordinary_assigned_retained_event_root_targets_native_candidate_direct_reserve
    (hn:0<n) (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (hK:0<K) (i₀:Fin K) (rsv θ ρ D:ℝ) (d m:ℕ) (hd:2≤d) (hm:7≤m)
    (hs0:0≤rsv) (hs1:rsv≤1/100) (hθ:0<θ) (hθ1:θ≤1/100)
    (hda:1/θ≤d) (hρ:0<ρ) (hρ1:ρ≤1) (hD:0<D) (hsize:ρ*D=2*(Fintype.card U:ℝ))
    (Allowed:Set ℕ) (hAllowed:∀u,AllowedCycleLengths (F u) Allowed)
    (hClassReserve:OrdinaryClassReserveBound F hF i₀ rsv)
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n))
    (τ ε A BM t:ℝ) (ht:0≤t)
    (weight:(Fin (m+1)→Fin n)→ℝ)
    (hw:SuccessorSequenceWeightConditions (ordinaryEligibleHost P π d) π (3*d) D τ A BM weight)
    (w:∀i:Fin K,OrdinaryCycle (ordinaryEligibleHost P π d) (longPaddedSeedExponent i+2)→ℝ)
    (hw0:∀i C,0≤w i C) (B:Fin K→ℝ) (hB:∀i,0≤B i)
    (hb:∀i C,w i C≤B i/(n:ℝ)^(longPaddedSeedExponent i))
    (he:∀i∈longRetainedSeedIndices F hF K θ,∀x y,(∑C,if C.val.val.Adj x y then w i C else 0)=if (ordinaryEligibleHost P π d).Adj x y then 1 else 0)
    (hdeg:∀x,|((ordinaryEligibleHost P π d).degree x:ℝ)-D|≤ε*(n:ℝ))
    (hbudgetS:∀i∈longRetainedSeedIndices F hF K θ,6*((longPaddedSeedExponent i+2:ℕ):ℝ)^4*(B i)*(2*(3*d))+ε*(n:ℝ)≤τ*D)
    (hbudgetR:∀i∈longRetainedSeedIndices F hF K θ,5*((longPaddedSeedExponent i+2:ℕ):ℝ)^4*(B i)*(2*(3*d))/(n:ℝ)≤τ)
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (k₂:ℝ) (hk₂:0≤k₂)
    (σ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e):
    let c:ℝ:=(m:ℝ)+1
    let q:=ordinaryAssignedMarkedProbability F hF K θ c
    let s:=ordinaryAssignedSpokeProbability F hF K i₀ rsv θ c
    let p₂:=ordinaryAssignedApproxRimProbability F hF i₀ rsv θ c D
    let η:=fun i u=>ordinaryAssignedFrequencyCoefficient F hF K i₀ rsv θ c u i
    let wM:=ordinaryAssignedShiftedSeed F hF i₀ rsv θ c D π d m weight
    let wO:=ordinaryAssignedUnshiftedSeed F hF i₀ rsv θ c D (ordinaryEligibleHost P π d) π d w
    let raw:RawMarkedOutcome (Fin n) U Bool Bool:=fun e=>rawExpandedApproximateCollapse e (σ e)
    let st:=typedMarkedResourceState (ordinaryShiftedPairRims (ordinaryEligibleHost P π d) π d raw) (rawMarkedPairSpokes π d raw true true)
    let R:=ordinaryMixedGenericResources
      (fun W:MarkedWheel (Prod.fst:Fin n×Fin n→Fin n) Prod.snd Prod.fst Prod.snd m π (3*d)
        (fun _ (_:U)=>True) (fun _ (_:U)=>True)=>typedMarkedOccurrenceResources W)
      (fun i (W:OrderedOrdinaryWheel (U:=U) π (3*d) (longPaddedSeedExponent i+2))=>orderedOrdinaryResources W)
    let seed:=ordinaryMixedGenericWeight wM wO;
    ∀(hq:∀u g,0≤q u g) (hQ:∀u,∑g,q u g≤1/8)
      (hs:∀u j,0≤s u j) (hS:∀u,∑j,s u j≤ intervalUncoveredProbability d (∑g,q u g))
      (hsum:2*p₂+2*k₂≤1),
    OrdinaryShiftedMixedLoadEvent (ordinaryEligibleHost P π d) π d m (fun i:Fin K=>longPaddedSeedExponent i+1) p₂ k₂ q s
      (fun _ _=>True) (fun _ _=>True) (fun _:Unit=>wM) (fun _=>true) (fun _=>true)
      wO (fun _=>true) (fun _=>true) t (fun _=>t) σ→
    (∀x u,rawMarkedPairSpokes π d raw true true true x u→q u true≠0)→
    ∀i root,st root=true→
      |resourcePatternLoad (R i) (seed i) (fun _ _=>true) root st-
        ordinaryMixedIdealTarget (m:ℝ) D p₂ (ordinaryAssignedLongWeight F hF K θ c)
          (ordinaryAssignedShortWeight F hF K i₀ rsv θ c) η i root|≤
        t+τ*ordinaryMixedIdealTarget (m:ℝ) D p₂ (ordinaryAssignedLongWeight F hF K θ c)
          (ordinaryAssignedShortWeight F hF K i₀ rsv θ c) η i root :=by
  intro c q s p₂ η wM wO raw st R seed hq hQ hs hS hsum hevent hpositive
  have hc:8≤c:=by dsimp [c];exact_mod_cast (show 8≤m+1 by omega)
  have hdens:=ordinary_assigned_approximate_density_bounds_candidate_direct_reserve hn F hF K hK i₀ rsv θ c ρ D d hd
    hs0 hs1 hθ hθ1 hc hda hρ hρ1 hD hsize Allowed hAllowed hClassReserve
  have hp:0<p₂:=by
    have hh:=lt_of_lt_of_le hdens.1 hdens.2.1
    simpa only [p₂,ordinaryAssignedApproxRimProbability] using hh
  have hspos:∀u,0<s u true:=by
    intro u
    have hh:=lt_of_lt_of_le hdens.1 (hdens.2.2.2.1 u).1
    simpa only [s,ordinaryAssignedSpokeProbability,if_true] using hh
  have hη:∀i u,0≤η i u:=by
    intro i u
    exact (hdens.2.2.2.2 i u).1
  have hzero:∀i∉longRetainedSeedIndices F hF K θ,∀u,η i u=0:=by
    intro i hi u
    exact ordinary_assigned_nonretained_coefficient_zero F hF i₀ rsv θ c hs0 i hi u
  have hfirst:=ordinary_shifted_retained_event_root_targets (ordinaryEligibleHost P π d) π p₂ k₂ hp hk₂ hsum d hd
    q hq hQ s hs hS hnoshort m (by omega) longPaddedSeedExponent long_padded_seed_exponent_positive
    (by simpa using hn) D τ ε A BM t hD ht hspos weight hw η hη (longRetainedSeedIndices F hF K θ) hzero
  have hsecond:=hfirst w hw0 B hB
  have hthird:=hsecond (by intro i C;simpa only [Fintype.card_fin] using hb i C)
  have he':letI:DecidableEq (Fin n):=Classical.decEq _;
      ∀i∈longRetainedSeedIndices F hF K θ,∀x y,(∑C,if C.val.val.Adj x y then w i C else 0)=if (ordinaryEligibleHost P π d).Adj x y then 1 else 0:=by
    intro i hi x y
    have hh:=ordinary_cycle_edge_sum_fin_decidable n (longPaddedSeedExponent i+2) (ordinaryEligibleHost P π d) (w i) x y
    exact hh.trans (he i hi x y)
  have hfourth:=hthird he' 
  have hfifth:=hfourth (by simpa only [Fintype.card_fin] using hdeg)
  have hsixth:=hfifth (by simpa only [Fintype.card_fin] using hbudgetS)
  have hh:=hsixth (by simpa only [Fintype.card_fin] using hbudgetR) σ
  have hM:=ordinary_assigned_shifted_seed_factorization F hF i₀ rsv θ c D π d m weight
  have hO:=ordinary_assigned_unshifted_seed_factorization F hF i₀ rsv θ c D (ordinaryEligibleHost P π d) π d w
  change wM=_ at hM
  change wO=_ at hO
  rw [hM,hO] at hevent
  have hh':=hh hevent hpositive
  change wM=(fun W=>weight W.1.val/(D*p₂^(m+1)*(s W.2.val true)^m)) at hM
  change wO=(fun i W=>η i W.2*physicalOrdinaryTupleWeight (π:=π) (b:=3*d) (long_padded_seed_exponent_positive i) (w i) W.1.val/
    (((longPaddedSeedExponent i+2:ℕ):ℝ)*D*p₂^(longPaddedSeedExponent i+2)*(s W.2 true)^(longPaddedSeedExponent i+1))) at hO
  rw [←hM,←hO] at hh'
  convert hh' using 1 <;> (try simp only [R,seed,q,s,ordinaryAssignedMarkedProbability,
    ordinaryAssignedSpokeProbability,ite_true]) <;> congr! 5 <;> simp only [st,raw]
  unfold resourcePatternLoad
  apply Finset.sum_congr
  · ext x; simp
  · intro x hx
    congr! 5 <;>
      (try (ext t; cases t <;>
        simp [typedMarkedOccurrenceResources_rim,typedMarkedOccurrenceResources_spoke]))
end Oberwolfach

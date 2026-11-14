module

public import Oberwolfach.OrdinaryClassReserveBound
public import Oberwolfach.CandidateOrdinaryAssignedMassAfterBoundedDeletion
public import Oberwolfach.OrdinaryAssignedMassAfterBoundedDeletion
public import Oberwolfach.OrdinaryCandidateClassReservation
public import Oberwolfach.CandidateOrdinaryAssignedPhysicalMassAfterDeletionDirectReserve
public import Oberwolfach.OrdinaryAssignedPhysicalMassAfterDeletion
public import Oberwolfach.OrdinaryMixedRootTargetsAfterDeletion
public import Oberwolfach.OrdinaryShiftedDeletedHubCard
public import Oberwolfach.OrdinaryMixedHubRootTarget
public import Oberwolfach.PhysicalSampledHubFrequencyMargin
public import Oberwolfach.LongRetainedPaddedIndexSet

@[expose] public section
/-! Every retained ordinary factor-frequency test has positive mass among
the realized physical matching candidates. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]

theorem ordinary_assigned_retained_mass_after_bounded_deletion_candidate_direct_reserve
    (hn:0<n) (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (Allowed:Set ℕ) (hAllowed:∀u,AllowedCycleLengths (F u) Allowed)
    (hK3:3≤K) (i₀:Fin K) (rsv θ c:ℝ)
    (hs0:0≤rsv) (hs1:rsv≤1/100) (hθ:0<θ) (hθ1:θ≤1/100) (hc:8≤c)
    (hClassReserve:OrdinaryClassReserveBound F hF i₀ rsv)
    (b:U→ℝ) (hbdef:∀u,b u=ordinaryAssignedShortWeight F hF K i₀ rsv θ c u)
    (hb:∀u,0<b u ∧ b u≤1) (pstar:ℝ) (hpstar:0<pstar) (hbstar:∀u,pstar≤b u)
    (π:Equiv.Perm (Fin n)) (d m:ℕ) (hm:3≤m)
    (wM:MarkedWheel (Prod.fst:Fin n×Fin n→Fin n) Prod.snd Prod.fst Prod.snd m π (3*d)
      (fun _ (_:U)=>True) (fun _ (_:U)=>True)→ℝ)
    (wO:∀i:Fin K,OrderedOrdinaryWheel (U:=U) π (3*d) (longPaddedSeedExponent i+2)→ℝ)
    (BM:ℝ) (hBM:0≤BM) (hwM:∀W,0≤wM W ∧ wM W≤BM/(n:ℝ)^m)
    (BO:Fin K→ℝ) (hBO:∀i,0≤BO i)
    (hwO:∀i W,0≤wO i W ∧ wO i W≤BO i/(n:ℝ)^(longPaddedSeedExponent i+1))
    (hU:Fintype.card U≤n) (P:SimpleGraph (Fin n))
    (σ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e) (Del:SimpleGraph (Fin n)) (δ:ℝ) (hDel:∀x,(Del.degree x:ℝ)≤δ)
    (a:U→ℝ) (D p:ℝ) (τ t countErr:ℝ) (hτ:τ≤1/2) (hcountErr:countErr≤pstar*n/2):
    let raw:RawMarkedOutcome (Fin n) U Bool Bool:=fun e=>rawExpandedApproximateCollapse e (σ e)
    let raw':=rawMarkedDeleteRims raw Del.edgeFinset
    let old:=typedMarkedResourceState (ordinaryShiftedPairRims P π d raw) (rawMarkedPairSpokes π d raw true true)
    let state:=typedMarkedResourceState (ordinaryShiftedPairRims P π d raw') (rawMarkedPairSpokes π d raw' true true)
    let R:=ordinaryMixedGenericResources
      (fun W:MarkedWheel (Prod.fst:Fin n×Fin n→Fin n) Prod.snd Prod.fst Prod.snd m π (3*d)
        (fun _ (_:U)=>True) (fun _ (_:U)=>True)=>typedMarkedOccurrenceResources W)
      (fun i (W:OrderedOrdinaryWheel (U:=U) π (3*d) (longPaddedSeedExponent i+2))=>orderedOrdinaryResources W)
    let w:=ordinaryMixedGenericWeight wM wO
    let hub:=ordinaryMixedGenericWheelHub (U:=U) (K:=K) π (3*d) m longPaddedSeedExponent
    let C:Option (Fin K)→ℝ:=fun i=>match i with
      | none=>22*((m:ℝ)+1)^4*BM
      | some i=>10*((longPaddedSeedExponent i:ℝ)+2)^4*BO i
    let totalErr:=t+(∑i,C i)*δ/(n:ℝ);
    (totalErr≤θ/(800*(K:ℝ)))→
    (∀i v,old v=true→
      |resourcePatternLoad (R i) (w i) (fun _ _=>true) v old-
        ordinaryMixedIdealTarget (m:ℝ) D p a b (fun i u=>ordinaryAssignedFrequencyCoefficient F hF K i₀ rsv θ c u i) i v|≤
        t+τ*ordinaryMixedIdealTarget (m:ℝ) D p a b (fun i u=>ordinaryAssignedFrequencyCoefficient F hF K i₀ rsv θ c u i) i v)→
    (∀u,|rawMarkedRestrictedSpokeCol π d (fun e=>σ (Sum.inr e)) true true false u Finset.univ-b u*n|≤countErr)→
    ∀z:OrdinaryAssignedRetainedHubTest F hF i₀ rsv θ,
      θ*(n:ℝ)/(1600*(K:ℝ)*(K:ℝ))≤
        ∑c:PhysicalSampledCandidate (mixedCandidateResources R) state,
          ordinaryAssignedRetainedHubIndicator F hF i₀ rsv θ π (3*d) m longPaddedSeedExponent z c.val*
            mixedCandidateWeight w c.val :=by
  intro raw raw' old state R w hub C totalErr ht hload hcount
  let target:=ordinaryMixedIdealTarget (V:=Fin n) (m:ℝ) D p a b (fun i u=>ordinaryAssignedFrequencyCoefficient F hF K i₀ rsv θ c u i)
  have hnew:=ordinary_mixed_root_targets_after_deletion P Del π d m hm hn hU longPaddedSeedExponent
    long_padded_seed_exponent_positive wM BM hBM hwM wO BO hBO hwO raw true true δ hDel target τ t hload
  apply ordinary_assigned_retained_mass_after_rim_deletion_candidate_direct_reserve hn F hF Allowed hAllowed hK3 i₀ rsv θ c hs0 hs1 hθ hθ1 hc hClassReserve
    b hbdef hb pstar hpstar hbstar π d m wM wO P σ Del.edgeFinset a D p τ totalErr countErr hτ ht hcountErr
  · intro i v hv
    have hh:=hnew i v hv
    convert hh using 1 <;> (try simp only [target,totalErr,C,raw,raw',state,R,w]) <;> congr! 5
    all_goals (rename_i j hj; cases j <;> rfl)
  · exact hcount
end Oberwolfach

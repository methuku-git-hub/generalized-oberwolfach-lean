module

public import Oberwolfach.OrdinaryAssignedRelativeMassAfterDeletion
public import Oberwolfach.OrdinaryCandidateClassReservation
public import Oberwolfach.CandidateOrdinaryAssignedPhysicalMassAfterDeletion
public import Oberwolfach.CandidateOrdinaryAssignedRelativeMassFromTargets
public import Oberwolfach.OrdinaryAssignedRelativeMassFromTargets
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

theorem ordinary_assigned_relative_mass_after_bounded_deletion_candidate
    (hn:0<n) (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (Allowed:Set ℕ) (hAllowed:∀u,AllowedCycleLengths (F u) Allowed)
    (hK3:3≤K) (i₀:Fin K) (rsv θ c:ℝ)
    (hs0:0≤rsv) (hs1:rsv≤1/100) (hθ:0<θ) (hθ1:θ≤1/100) (hc:8≤c)
    (hsclass:rsv≤1/(2*(K:ℝ))) (hclass:∀u,i₀∈factorShortCandidates (F u) K)
    (b:U→ℝ) (hbdef:∀u,b u=ordinaryAssignedShortWeight F hF K i₀ rsv θ c u)
    (hb:∀u,0<b u ∧ b u≤1) (pstar lam:ℝ) (hpstar:0<pstar) (hbstar:∀u,pstar≤b u) (hlam:0≤lam)
    (π:Equiv.Perm (Fin n)) (d m:ℕ) (hm:3≤m)
    (wM:MarkedWheel (Prod.fst:Fin n×Fin n→Fin n) Prod.snd Prod.fst Prod.snd m π (3*d)
      (fun _ (_:U)=>True) (fun _ (_:U)=>True)→ℝ)
    (wO:∀i:Fin K,OrderedOrdinaryWheel (U:=U) π (3*d) (longPaddedSeedExponent i+2)→ℝ)
    (BM:ℝ) (hBM:0≤BM) (hwM:∀W,0≤wM W ∧ wM W≤BM/(n:ℝ)^m)
    (BO:Fin K→ℝ) (hBO:∀i,0≤BO i)
    (hwO:∀i W,0≤wO i W ∧ wO i W≤BO i/(n:ℝ)^(longPaddedSeedExponent i+1))
    (hU:Fintype.card U≤n) (P:SimpleGraph (Fin n))
    (σ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e) (Del:SimpleGraph (Fin n)) (δ:ℝ) (hDel:∀x,(Del.degree x:ℝ)≤δ)
    (a:U→ℝ) (D p:ℝ) (τ t countErr:ℝ) (hτ0:0≤τ) (ht0:0≤t) (hcount0:0≤countErr)
    (hτ:τ≤lam*pstar/4) (hcountErr:countErr≤lam*pstar*n/4):
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
    (totalErr≤lam*(θ/(100*(K:ℝ)))/4)→
    (∀i v,old v=true→
      |resourcePatternLoad (R i) (w i) (fun _ _=>true) v old-
        ordinaryMixedIdealTarget (m:ℝ) D p a b (fun i u=>ordinaryAssignedFrequencyCoefficient F hF K i₀ rsv θ c u i) i v|≤
        t+τ*ordinaryMixedIdealTarget (m:ℝ) D p a b (fun i u=>ordinaryAssignedFrequencyCoefficient F hF K i₀ rsv θ c u i) i v)→
    (∀u,|rawMarkedRestrictedSpokeCol π d (fun e=>σ (Sum.inr e)) true true false u Finset.univ-b u*n|≤countErr)→
    ∀z:OrdinaryAssignedRetainedHubTest F hF i₀ rsv θ,
      |((longPaddedSeedExponent z.val.1+2:ℕ):ℝ)*
        (∑c:PhysicalSampledCandidate (mixedCandidateResources R) state,
          ordinaryAssignedRetainedHubIndicator F hF i₀ rsv θ π (3*d) m longPaddedSeedExponent z c.val*
            mixedCandidateWeight w c.val)-
        (1-θ)*ordinaryAssignedKeptFraction F hF K i₀ rsv θ z.val.2 z.val.1*n|≤
        lam*ordinaryAssignedKeptFraction F hF K i₀ rsv θ z.val.2 z.val.1*n :=by
  intro raw raw' old state R w hub C totalErr ht hload hcount
  let target:=ordinaryMixedIdealTarget (V:=Fin n) (m:ℝ) D p a b (fun i u=>ordinaryAssignedFrequencyCoefficient F hF K i₀ rsv θ c u i)
  have hnew:=ordinary_mixed_root_targets_after_deletion P Del π d m hm hn hU longPaddedSeedExponent
    long_padded_seed_exponent_positive wM BM hBM hwM wO BO hBO hwO raw true true δ hDel target τ t hload
  have hδ:0≤δ:=(Nat.cast_nonneg (Del.degree ⟨0,hn⟩)).trans (hDel ⟨0,hn⟩)
  have hC0:∀i,0≤C i:=by
    intro i
    cases i with
    | none => dsimp [C];positivity
    | some i => dsimp [C];have hh:=hBO i;positivity
  have hsumC:0≤∑i,C i:=Finset.sum_nonneg (fun i _=>hC0 i)
  have herr0:0≤totalErr:=by
    dsimp only [totalErr]
    exact add_nonneg ht0 (div_nonneg (mul_nonneg hsumC hδ) (Nat.cast_nonneg n))
  apply ordinary_assigned_retained_mass_relative_from_targets_candidate hn F hF Allowed hAllowed (by omega) i₀ rsv θ c
    hs0 hs1 hθ hθ1 hc hsclass hclass b hbdef pstar lam hpstar hbstar hlam π d m wM wO state a D p
    τ totalErr countErr hτ0 herr0 hcount0 hτ ht hcountErr
  · intro i v hv
    have hh:=hnew i v hv
    convert hh using 1 <;> (try simp only [target,totalErr,C,raw,raw',state,R,w]) <;> congr! 5
    all_goals (rename_i j hj; cases j <;> rfl)
  · intro u
    have hh:=ordinary_shifted_deleted_hub_card P π d σ true true Del.edgeFinset u
    have hc':((restrictedResourceSubset (Function.Embedding.subtype (fun v=>v∈bernoulliVertexSet state))
        (ordinaryCommonHubSpokeRoots u)).card:ℝ)=
        rawMarkedRestrictedSpokeCol π d (fun e=>σ (Sum.inr e)) true true false u Finset.univ:=by
      convert hh using 1 <;> congr! 5
    rw [hc']
    exact hcount u
end Oberwolfach

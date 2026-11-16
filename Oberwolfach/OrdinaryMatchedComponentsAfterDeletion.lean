module

public import Oberwolfach.OrdinaryAssignedRelativeMassAfterDeletion
public import Oberwolfach.OrdinaryMatchedComponentAssignment
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

set_option backward.isDefEq.respectTransparency true in
theorem ordinary_assigned_matched_components_after_deletion
    (hn:0<n) (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (Allowed:Set ℕ) (hAllowed:∀u,AllowedCycleLengths (F u) Allowed)
    (hK3:3≤K) (i₀:Fin K) (rsv θ c:ℝ)
    (hs0:0≤rsv) (hs1:rsv≤1/100) (hθ:0<θ) (hθ1:θ≤1/100) (hc:8≤c)
    (hsclass:rsv≤1/(2*(K:ℝ))) (hclass:∀u,factorPreparationClass (F u) K=some i₀)
    (b:U→ℝ) (hbdef:∀u,b u=ordinaryAssignedShortWeight F hF K i₀ rsv θ c u)
    (hb:∀u,0<b u ∧ b u≤1) (pstar lam:ℝ) (hpstar:0<pstar) (hbstar:∀u,pstar≤b u) (hlam:0≤lam)
    (π:Equiv.Perm (Fin n)) (d m:ℕ) (hm:3≤m)
    (wM:MarkedWheel (Prod.fst:Fin n×Fin n→Fin n) Prod.snd Prod.fst Prod.snd m π (3*d)
      (fun _ (_:U)=>True) (fun _ (_:U)=>True)→ℝ)
    (wO:∀i:Fin K,OrderedOrdinaryWheel (U:=U) π (3*d) (longPaddedSeedExponent i+2)→ℝ)
    (BM:ℝ) (hBM:0≤BM) (hwM:∀W,0≤wM W ∧ wM W≤BM/(n:ℝ)^m)
    (BO:Fin K→ℝ) (hBO:∀i,0≤BO i)
    (hwO:∀i W,0≤wO i W ∧ wO i W≤BO i/(n:ℝ)^(longPaddedSeedExponent i+1))
    (hU:Fintype.card U≤n) (P:SimpleGraph (Fin n)) (D:ℝ)
    (weights:∀i:Fin K,OrdinaryCycle P (longPaddedSeedExponent i+2)→ℝ)
    (hNamed:wO=ordinaryAssignedUnshiftedSeed F hF i₀ rsv θ c D P π d weights)
    (σ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e) (Del:SimpleGraph (Fin n)) (δ:ℝ) (hDel:∀x,(Del.degree x:ℝ)≤δ)
    (a:U→ℝ) (p:ℝ) (τ t countErr:ℝ) (hτ0:0≤τ) (ht0:0≤t) (hcount0:0≤countErr)
    (hτ:τ≤lam*pstar/4) (hcountErr:countErr≤lam*pstar*n/4)
    (Cres:∀u,Finset (F u).ConnectedComponent)
    (hCres:∀u c,c∈Cres u→Fintype.card c=i₀.val+1)
    (hres:∀u,((i₀.val+1:ℕ):ℝ)*((Cres u).card:ℝ)=rsv*n)
    (γ:ℝ) (hγ:0≤γ) (hslack:lam+γ*(1-θ+lam)<θ):
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
    ∀L:Finset (PhysicalSampledCandidate (mixedCandidateResources R) state),
    let mass:=fun z:OrdinaryAssignedRetainedHubTest F hF i₀ rsv θ=>
      ∑x:PhysicalSampledCandidate (mixedCandidateResources R) state,
        ordinaryAssignedRetainedHubIndicator F hF i₀ rsv θ π (3*d) m longPaddedSeedExponent z x.val*mixedCandidateWeight w x.val;
    (∀x∈L,0<mixedCandidateWeight w x.val)→
    (∀z,(1-γ)*mass z≤∑x∈L,ordinaryAssignedRetainedHubIndicator F hF i₀ rsv θ π (3*d) m longPaddedSeedExponent z x.val)→
    (∀z,(∑x∈L,ordinaryAssignedRetainedHubIndicator F hF i₀ rsv θ π (3*d) m longPaddedSeedExponent z x.val)≤(1+γ)*mass z)→
    ∀u,∃f:↥(L.filter (fun x=>x.val.1.isSome ∧ hub x.val.1 x.val.2=u))↪↥(Finset.univ\Cres u),
      ∀x,Fintype.card (f x).val=((x.val.val.1).getD i₀).val+1 :=by
  intro raw raw' old state R w hub C totalErr ht hload hcount L mass hsupp hlo hhi
  have hrelative:=ordinary_assigned_relative_mass_after_bounded_deletion hn F hF Allowed hAllowed hK3 i₀ rsv θ c
    hs0 hs1 hθ hθ1 hc hsclass hclass b hbdef hb pstar lam hpstar hbstar hlam π d m hm wM wO BM hBM hwM BO hBO hwO
    hU P σ Del δ hDel a D p τ t countErr hτ0 ht0 hcount0 hτ hcountErr ht hload hcount
  subst wO
  apply ordinary_matched_component_assignment hn F hF Allowed hAllowed (by omega) i₀ rsv θ c D hs0 hθ
    P π d m weights wM R state Cres hCres hres L lam γ hγ hslack
  · exact hsupp
  · intro z
    have hh:=hrelative z
    convert hh using 1 <;> (try simp only [mass,R,w,raw,raw',state]) <;> congr! 5
  · intro z
    convert hlo z using 1 <;> (try simp only [mass]) <;> congr! 5
  · intro z
    convert hhi z using 1 <;> (try simp only [mass]) <;> congr! 5
end Oberwolfach

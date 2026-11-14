module

public import Oberwolfach.OrdinarySelectedPostDemandColumnTargetResult
public import Oberwolfach.OrdinarySelectedPostDemandTargetResult
public import Oberwolfach.OrdinaryPackageApproximateOccupied
public import Oberwolfach.OrdinaryPackageOldRimOccupancy
public import Oberwolfach.OrdinaryUnusedSpokeColumnFromPhysicalRow
public import Oberwolfach.OrdinaryMatchedSpokeWheelPack
public import Oberwolfach.OrdinaryUncoveredTargetColumnFromTests
public import Oberwolfach.OrdinaryInnerTargetFluctuationEventually
public import Oberwolfach.OrdinaryZeroRetentionPrior

@[expose] public section

/-! The actual matching also bounds each target column, avoiding a bound on
the whole first-level hub set. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 45000000
set_option synthInstance.maxSize 65536
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
attribute [local instance 100000] Finset.decidableDforallFinset

theorem ordinary_selected_post_demand_target_columns_eventually
    (θ δplace a γ:ℝ) (hθ:0≤θ) (hδ:0<δplace) (hθδ:θ≤δplace/8):
    ∃N:ℕ,∀{n K:ℕ},N≤n→∀{U:Type} [Fintype U] [DecidableEq U],Fintype.card U≤n→
    ∀(F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (Cres:∀u,Finset (F u).ConnectedComponent) (i₀:Fin K) (rsv lam:ℝ)
    (m d:ℕ) (π:Equiv.Perm (Fin n)) (P Del Target Protect Bad:SimpleGraph (Fin n))
    (Inner:Finset (Fin n)) (Hubs:Finset U) (bRate z:ℝ)
    (σ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)
    (tret:ℕ) (Jret:StartRetentionOutcome (rawStartHubSet π d (fun e=>σ (Sum.inr e)) false) tret)
    (q s:U→Bool→ℝ),
    OrdinaryZeroRetentionEvent π d false σ→
    (∀w,1-(∑g,q w g)-(∑j,s w j)≤2*θ)→
    (∀v∈Inner,|rawIntervalUnassignedColumnCount π d (fun e=>σ (Sum.inr e)) v Hubs-
      ∑w∈Hubs,(1-(∑g,q w g)-(∑j,s w j))|<(Inner.card:ℝ)^(3/4:ℝ))→
    2*((max a γ)*n)≤δplace*n/8→
    OrdinarySelectedPostDemandTargetResult F hF Cres i₀ rsv θ lam a γ m d π P Del Target Protect Bad Inner Hubs bRate z σ tret Jret→
    OrdinarySelectedPostDemandColumnTargetResult F hF Cres i₀ rsv θ lam a γ m d π P Del Target Protect Bad Inner Hubs bRate z δplace σ tret Jret :=by
  obtain ⟨N,hfluct⟩:=ordinary_inner_target_fluctuation_eventually δplace hδ
  refine ⟨N,?_⟩
  intro n K hn U _ _ hU F hF Cres i₀ rsv lam m d π P Del Target Protect Bad Inner Hubs bRate z σ tret Jret q s
    hzero hslack hlocal hmatching htarget
  unfold OrdinarySelectedPostDemandTargetResult at htarget
  unfold OrdinarySelectedPostDemandColumnTargetResult
  obtain ⟨L,hL,hrows,hlocalRim,hmass,pk,hocc,hpack,hTargets,hrest⟩:=htarget
  refine ⟨L,hL,hrows,hlocalRim,hmass,pk,hocc,hpack,hTargets,?_,hrest⟩
  let raw:RawMarkedOutcome (Fin n) U Bool Bool:=fun e=>rawExpandedApproximateCollapse e (σ e)
  let rawI:RawIntervalFamilyOutcome (Fin n) U Bool Bool:=fun e=>raw (Sum.inr e)
  let raw':=rawMarkedDeleteRims raw Del.edgeFinset
  let Rim:=ordinaryShiftedPairRims (ordinaryEligibleHost P π d) π d raw'
  let H:=rawMarkedPairSpokes π d raw' true true
  let Image:=fun u=>((pk u).data.oldDomain\bufferedPathStrictInterior (fun _=>(m+1)*d) (pk u).inner).image (pk u).ψ
  have hFin:(fun (a b:Fin n)=>Classical.propDecidable (a=b))=instDecidableEqFin n:=Subsingleton.elim _ _
  have hno:∀w x,¬rawIntervalColouredStart π d (fun e=>rawI (w,e)) x false:=by
    have hh:=hzero.1
    rw [hFin] at hh
    simpa only [rawI,raw,rawExpandedApproximateCollapse,id_eq] using hh
  have hempty:∀u,IsEmpty (retainedMarkedIndex π d rawI false tret Jret u):=by
    have hgood:=hzero.2
    rw [hFin] at hgood
    have hh:=(hgood tret Jret 0 (by norm_num)).2
    convert hh using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _
  have happrox:∀w x,rawIntervalFamilyState π d rawI (x,w)=some (Sum.inl true)→x∈Image w:=by
    intro w x hx
    have hh:=ordinary_package_approximate_occupied π d m rawI w tret Jret _ _ _ _ _ _ _ _ (pk w) (hocc w)
    exact hh x hx
  have hcol:∀v,(((Finset.univ:Finset U).filter (fun w=>v∈ordinaryUnusedTrueSpokes π d rawI Image w)).card:ℝ)≤(max a γ)*n:=by
    intro v
    have hh:=ordinary_unused_spoke_column_le_physical_row (K:=K) π d m Rim H L v Image (by
      intro u hu c hc x hx hcx
      obtain ⟨edge,he,hv⟩:=ordinary_matched_spoke_in_wheel_pack (K:=K) π d m Rim H L u
        (pk u).marker (pk u).hGood c hc x v hx hcx
      letI:=hempty u
      exact ordinary_package_old_rim_occupancy m d π _ _ _ _ _ _ _ _ (pk u) edge he v hv)
    have heq:(Finset.univ.filter (fun w=>v∈ordinaryUnusedTrueSpokes π d rawI Image w))=
        Finset.univ.filter (fun w=>H false v w ∧ v∉Image w):=by
      ext w
      simp [ordinaryUnusedTrueSpokes,H,rawMarkedPairSpokes,rawMarkedSpokes,raw',rawMarkedDeleteRims,rawI]
      intro _
      congr! 10 <;> exact Subsingleton.elim _ _
    rw [heq]
    have hv:(((Finset.univ.filter (fun w=>H false v w ∧ v∉Image w)).card:ℝ))≤
      (((physicalSampledRow (ordinaryMixedPhysicalResource (U:=U) π)
        (typedMarkedResourceState Rim H) (ordinaryPhysicalRow (.inr (.inl v))))\
          L.biUnion (physicalSampledCandidateSet (ordinaryMixedPhysicalResource (U:=U) π) _ _)).card:ℝ):=by exact_mod_cast hh
    exact hv.trans (hrows (.inr (.inl v)))
  have hlocal':∀v∈Inner,|rawIntervalUnassignedColumnCount π d rawI v Hubs-
      ∑w∈Hubs,(1-(∑g,q w g)-(∑j,s w j))|<(Inner.card:ℝ)^(3/4:ℝ):=by
    convert hlocal using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _
  have hinner:=ordinary_uncovered_target_column_from_tests π d rawI Inner Hubs Image hno happrox q s θ ((max a γ)*n)
    hslack hlocal' hcol
  have hHubNat:Hubs.card≤n:=(Finset.card_le_univ Hubs).trans hU
  have hHub:(Hubs.card:ℝ)≤n:=by exact_mod_cast hHubNat
  have hn0:(0:ℝ)≤n:=by positivity
  have hθHub:=mul_le_mul_of_nonneg_left hHub (show 0≤2*θ by positivity)
  have hδn:0≤δplace*n:=mul_nonneg hδ.le hn0
  have hθn:=mul_le_mul_of_nonneg_right hθδ hn0
  have hpow:=hfluct n hn Inner
  intro v
  by_cases hv:v∈Inner
  · have hh:=hinner v hv
    have hbudget:2*θ*Hubs.card+(Inner.card:ℝ)^(3/4:ℝ)+(max a γ)*n≤δplace*n/2:=by
      nlinarith only [hθHub,hθn,hmatching,hpow,hδn]
    convert hh.trans hbudget using 1 <;>
      congr! 10 <;> exact Subsingleton.elim _ _
  · have hz:0≤δplace*n/2:=by positivity
    have hemptyTargets:∀u,v∉ordinaryInnerSpokeTargets Inner Hubs
        (fun x w=>x∈rawReservedSpokeList π d (fun e=>σ (Sum.inr e)) w) u:=by
      intro u hu
      have hh:=(ordinary_inner_spoke_targets_bounds Inner Hubs
        (fun x w=>x∈rawReservedSpokeList π d (fun e=>σ (Sum.inr e)) w)).1
      have hs:ordinaryInnerSpokeTargets Inner Hubs
          (fun x w=>x∈rawReservedSpokeList π d (fun e=>σ (Sum.inr e)) w) u⊆Inner:=by
        by_cases hu':u∈Hubs <;> simp [ordinaryInnerSpokeTargets,hu']
      exact hv (hs hu)
    simpa [hemptyTargets] using hz
end Oberwolfach

module

public import Oberwolfach.OrdinaryFixedTargetMatchingEmbeddingTrackedShape

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 45000000
set_option synthInstance.maxSize 65536
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
attribute [local instance 100000] Finset.decidableDforallFinset

theorem ordinary_fixed_target_matching_embedding_tracked_eventually
    (m d:ℕ) (hm:7≤m) (hd:2≤d) (θ δ:ℝ) (hθ:0<θ) (hδ:0<δ):
    OrdinaryFixedTargetMatchingEmbeddingTrackedShape m d hm hd θ δ hθ hδ :=by
  unfold OrdinaryFixedTargetMatchingEmbeddingTrackedShape
  have hcapTheorem:=ordinary_packaged_capacity_from_matching m d hm (by omega) θ hθ (δ/8) (by positivity)
  unfold OrdinaryPackagedCapacityFromMatchingShape at hcapTheorem
  obtain ⟨N,hN⟩:=hcapTheorem
  refine ⟨N,?_⟩
  intro n K hnN hn hK U _ _ hUn F₀ hF₀ Allowed hAllowed i₀ rsv hrs0 hrs1 hθ1 hClass Cres hsize hres π hnoshort
    P S σ Inner Hubs Kabs lamMatch a γ ζret κ b z ρ₀ smin lamList p hζret hmatch0 hmatchUpper hκ hrate hsizeBudget
    hρ hs hb αCap hcapacity hInner hUlo hHubs herror hbα hbδ hD hNsmall hRowRate hHubsδ hlamList hlamList1 hδbound
    hnβ hnδ hq hcounts hzero hboundary s htests htarget Sample Conf Ref Protect G Del J
  have hα:0<αCap:=by dsimp [αCap];positivity
  unfold OrdinaryFixedTargetMatchingInputs at htarget
  obtain ⟨hAbsSub,havoid,hAbs,hDel,hG,hsep,hdegree,hDelDegree,hext,hfamily⟩:=htarget
  have hfamily' := hfamily 0 J
  unfold OrdinarySelectedMatchingFamilyResult at hfamily'
  obtain ⟨L,hL,hrows,hmass,pk,hpack⟩:=hfamily'
  let raw:RawMarkedOutcome (Fin n) U Bool Bool:=fun e=>rawExpandedApproximateCollapse e (σ e)
  have hstarts:∀w x,¬rawIntervalColouredStart π d (fun e=>raw (Sum.inr (w,e))) x false:=by
    have hsigma:=hzero.1
    have hFin:(fun (a b:Fin n)=>Classical.propDecidable (a=b))=instDecidableEqFin n:=Subsingleton.elim _ _
    rw [hFin] at hsigma
    simpa only [raw,rawExpandedApproximateCollapse,id_eq] using hsigma
  have hret:=retention_good_and_empty_roots_of_no_starts π d (fun e=>raw (Sum.inr e)) false 0 J hstarts
    (fun _:Unit=>Finset.univ) (fun _:Unit=>Finset.univ) ζret hζret
  have hgood:=hret.1
  have hempty:=hret.2
  let raw':=rawMarkedDeleteRims raw Del.edgeFinset
  let Rim:=ordinaryShiftedPairRims (ordinaryEligibleHost P π d) π d raw'
  let T:=ordinaryInnerSpokeTargets Inner Hubs (rawWheelSpokes π d (fun e=>expandedOrdinarySelectedCollapse e (σ e)) false)
  let Old:=fun u=>(pk u).data.oldDomain\bufferedPathStrictInterior (fun _=>(m+1)*d) (pk u).inner
  let OldIm:=fun u=>(Old u).image (pk u).ψ
  have hn0:(0:ℝ)≤n:=by positivity
  have hrowκ:∀u,(((physicalSampledRow (ordinaryMixedPhysicalResource (U:=U) π)
      (typedMarkedResourceState Rim (rawMarkedPairSpokes π d raw true true)) (ordinaryPhysicalRow (.inr (.inr u))))\
      L.biUnion (physicalSampledCandidateSet (ordinaryMixedPhysicalResource (U:=U) π) _ _)).card:ℝ)≤κ*n:=by
    intro u
    exact (hrows (.inr (.inr u))).trans (mul_le_mul_of_nonneg_right hκ hn0)
  have hbound:=hN (n:=n) (K:=K) hnN (U:=U) hn hK F₀ hF₀ Allowed hAllowed i₀ rsv hrs0 hrs1 hθ1 hClass π hnoshort
    raw 0 J ζret (lamMatch+γ*(1-θ+lamMatch)) κ hgood Cres hsize hres hcounts Rim L _ _ _ pk
    (fun u=>(hmass u).1) hq hζret hmatch0 hrate hrowκ δ hsizeBudget
    (lamMatch+γ*(1-θ+lamMatch)) hmatch0 hmatchUpper (fun u=>(hmass u).2)
    αCap b z hα hb hcapacity G Inner hdegree hInner
  have hsmall:∀u,(Fintype.card {x // x∈(pk u).data.remaining}:ℝ)≤δ*n:=fun u=>(hbound u).1
  have hcap:∀u,8*(residualSubtypeSet (pk u).data.remaining (pk u).data.prescribed).card+
      8*⌈4*(G.edgeFinset.card:ℝ)/(αCap*n)⌉₊+4*(T u\OldIm u).card+10≤
        Fintype.card {x // x∈(pk u).data.remaining}:=by
    apply ordinary_inner_target_capacity Inner T OldIm _ _ _ (fun u=>(havoid u).2.2.1)
    exact fun u=>(hbound u).2
  have hloadTheorem:=ordinary_packaged_forced_load_from_boundary (K:=K)
    (X:=fun u=>{x:Fin n | (F₀ u).connectedComponentMk x∉Cres u}) π d m (by omega) Rim raw 0 J
  unfold OrdinaryPackagedForcedLoadFromBoundaryShape at hloadTheorem
  have hbn:b*n≤δ*n/8:=by
    have hh:b*n≤(δ/8)*n:=mul_le_mul_of_nonneg_right hbδ hn0
    simpa only [div_mul_eq_mul_div] using hh
  have hload:=hloadTheorem L _ _ _ _ pk δ a γ hδ.le hUn hD hNsmall hRowRate
    (fun v=>hrows (.inr (.inl v))) hboundary T OldIm Hubs G (fun v=>(hdegree v).trans hbn)
    (fun u=>(havoid u).2.2.2) hHubsδ
  have hHost:ordinaryEligibleHost P π d≤P:=by intro x y h;exact h.1
  have hpair:=htests.2.2
  have hβ:0<lamList/2:=by positivity
  have hbδ':b≤δ:=by linarith
  obtain ⟨M,f,hM,hEnd,hGedges,hT,hOld,hAbsAvoid,hEdges,hDisjoint,hLocal,New,hpart,hpair,hcover,hnew⟩:=
    ordinary_reserved_packaged_target_embedding_tracked hn F₀ hF₀ Cres m d π σ P (ordinaryEligibleHost P π d) Del (S\Protect) G
      hHost hG hDel hsep _ _ _ _ _ _ pk hempty hpack Inner Hubs (ordinaryReservoirSpokeLabels Kabs) hAbsSub
      ρ₀ smin b hρ hs hb hUlo hHubs herror hpair hbα hAbs hdegree hcap
      (lamList/2) δ hβ hlamList1 hδ hδbound hbδ' hnβ hnδ hUn hsmall hload hext
  unfold OrdinarySelectedMatchingEmbeddingTrackedResult
  exact ⟨L,hL,hrows,hmass,pk,hpack,hsmall,M,f,hM,hEnd,hGedges,hT,hOld,hAbsAvoid,hEdges,hDisjoint,hLocal,New,hpart,hpair,hcover,hnew⟩
end Oberwolfach

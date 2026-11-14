module

public import Oberwolfach.OrdinaryTrackedComplementFromPostmatchingShape
public import Oberwolfach.OrdinaryPostmatchingComplementLocalAbsorber
public import Oberwolfach.OrdinaryCompletedActualComplementRemainder
public import Oberwolfach.OrdinaryForbiddenComplementLeSample

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

theorem ordinary_tracked_complement_from_postmatching {n q K:ℕ}
    (Fs:Fin q→SimpleGraph (Fin n)) (hFs:∀u,(Fs u).IsRegularOfDegree 2)
    (C:∀u,Finset (Fs u).ConnectedComponent) (i₀:Fin K) (r m d:ℕ)
    (rsv θ lamMatch a γ δ:ℝ) (P S:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n))
    (σ:∀e:RawWheelCoordinate (Fin n) (Fin q),RawExpandedMarkedCoordinateState Bool Bool e)
    (Inner:Finset (Fin n)) (Hubs:Finset (Fin q))
    (Kabs:Finset (Sym2 (Fin n)⊕(Fin n×Fin q))):
    OrdinaryTrackedComplementFromPostmatchingShape Fs hFs C i₀ r m d rsv θ lamMatch a γ δ P S π σ Inner Hubs Kabs :=by
  unfold OrdinaryTrackedComplementFromPostmatchingShape
  intro Sample Bad Reference Href Protect Del J hn hδ hS hsize hCard hzero hA hReserveTarget hAgreement htracked
    p k p₂ k₂ u t δDel κ edit e tcol hk hk₂ hu ht hδDel hκ hedit hκrow hDel hEdit hcolour hRefBalance hRefColumns
    LF newLoss κref Lrim Lspoke
  unfold OrdinarySelectedPostmatchingEmbeddingTrackedResult at htracked
  obtain ⟨L,hL,hrows,hmass,pk,hpack,hsmall,M,f,hM,hEnds,hMsub,hT,hfold,hAvoidAbs,hRim,hdis,hLocal,New,hpart,hpair,hcover,hnew⟩:=htracked
  let raw:RawMarkedOutcome (Fin n) (Fin q) Bool Bool:=fun e=>rawExpandedApproximateCollapse e (σ e)
  have hstarts:∀w x,¬rawIntervalColouredStart π d (fun e=>raw (Sum.inr (w,e))) x false:=by
    have hsigma:=hzero.1
    have hFin:(fun (x y:Fin n)=>Classical.propDecidable (x=y))=instDecidableEqFin n:=Subsingleton.elim _ _
    rw [hFin] at hsigma
    simpa only [raw,rawExpandedApproximateCollapse,id_eq] using hsigma
  have hret:=retention_good_and_empty_roots_of_no_starts π d (fun e=>raw (Sum.inr e)) false 0 J hstarts
    (fun _:Unit=>Finset.univ) (fun _:Unit=>Finset.univ) 0 (by norm_num)
  have hempty:=hret.2
  have hhost:ordinaryEligibleHost P π d≤P:=by intro x y h;exact h.1
  obtain ⟨hreg,hCycle,_,_,_,hdir,_⟩:=ordinary_reserved_package_inputs Fs hFs C m d π (fun e=>σ (Sum.inr e))
    _ _ _ _ _ _ _ pk
  have hOldAvoid:∀w,Disjoint ((pk w).data.oldDomain.image (pk w).ψ)
      (rawReservedSpokeList π d (fun e=>σ (Sum.inr e)) w):=by
    intro w
    exact ordinary_matched_package_old_avoids_reserve_when_empty _ _ _ _ _ _ _ _ _ _ _ _ (pk w) (hempty w)
  have hHref:∀w v,Href v w→v∈rawReservedSpokeList π d (fun e=>σ (Sum.inr e)) w:=by
    intro w v hv
    have hh:rawIntervalFamilyState π d (fun e=>σ (Sum.inr e)) (v,w)=some (Sum.inr false):=
      (ordinary_reference_spoke_projection π d σ false v w).mp hv
    simpa only [rawReservedSpokeList,rawIntervalOrdinaryOuter,Finset.mem_filter,Finset.mem_univ,true_and] using hh
  have hAvoidLocal:=ordinary_sample_local_reference_avoidance π d σ Inner Hubs (fun w=>f w) hLocal
  have hRef:Reference≤Sample:=sdiff_le.trans (ordinary_shared_sample_reference_graph_le_class P σ)
  obtain ⟨hProtect,hInnerProtect,hReserveProtect,_⟩:=ordinary_matching_protect_choice Reference Inner Kabs
  have hBadRef:Disjoint Reference Bad:=by
    apply disjoint_iff_inf_le.mpr
    intro x y h
    exact (h.1.2 h.2).elim
  have hLocalResult:=ordinary_postmatching_complement_local_pair_and_absorber S Sample Reference Protect Bad Inner Hubs Href Fs C f
    (fun w=>(pk w).data.deletedEdges.image (Sym2.map (pk w).ψ)) New Kabs hRef hBadRef hAgreement hProtect hInnerProtect hA
    hReserveProtect hReserveTarget hRim hpart hcover hAvoidLocal hAvoidAbs hT
  have hBad:∀x,(Bad.degree x:ℝ)≤LF:=by
    intro x
    dsimp [Bad,LF]
    exact_mod_cast permutationConflictGraph_degree_le π (3*d) x
  have hUncovered:∀x,(((Sample\Reference)\ordinaryEmbeddedComplements Fs C f).degree x:ℝ)≤κref:=by
    intro x
    have hh:=ordinary_same_sample_uncovered_conflict_reference_degree (K:=K) Fs C f
      (fun w=>(pk w).data.deletedEdges.image (Sym2.map (pk w).ψ)) New hpart P Del Bad π d m σ
      p k p₂ k₂ u t δDel κ LF hk hk₂ hu hcolour
      (by intro x; convert hDel x using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _) hBad L (fun w=>(pk w).marker)
      (fun w=>(pk w).hGood) (fun w edge he=>(pk w).hAllRims edge he)
      (fun v=>(hrows (.inl v)).trans hκrow) x
    rw [←ordinary_shared_sample_reference_graph_eq_state_zero] at hh
    convert hh using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  have hUsed:=ordinary_used_selected_reference_degree_from_old P (ordinaryEligibleHost P π d) Del Reference hhost π d σ sdiff_le
    Fs C f (fun w=>(pk w).data) hempty (fun w=>(pk w).hs₁) (fun w=>(pk w).ψ) New hdir hpart newLoss hnew
  have hC:∀w x y,((Fs w).induce {x | (Fs w).connectedComponentMk x∉C w}).Adj x y→S.Adj (f w x) (f w y):=by
    intro w x y hxy
    exact (hRim w x y hxy).1
  have hκref:0≤κref:=by dsimp [κref,LF];positivity
  have hnewLoss:0≤newLoss:=by dsimp [newLoss];positivity
  have hRemaining:∀w,(((pk w).data.remaining).card:ℝ)≤δ*n:=by
    intro w
    simpa only [Fintype.card_coe] using hsmall w
  have hPhysical:=ordinary_matched_complement_physical_edit S Sample Reference hRef hS Fs hFs C hsize f hC hdis
    (fun w=>(pk w).data) hreg hCycle (fun w=>(pk w).ψ) hfold Href
    (fun w=>rawReservedSpokeList π d (fun e=>σ (Sum.inr e)) w) hHref hOldAvoid New hpart hpair
    rsv edit κref newLoss e tcol newLoss (δ*n) hedit hκref hnewLoss hCard hEdit
    (by intro x;convert hUncovered x using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _)
    hUsed (by intro x;convert hRefBalance x using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _) hRefColumns
    hnew hRemaining Kabs hLocalResult.1
  have hSample:Sample≤P:=by intro x y hxy;exact hxy.1
  have hsub: (S\ordinaryEmbeddedComplements Fs C f)≤Sample :=
    (ordinary_completed_actual_complement_remainder Fs C f (fun w=>(pk w).data.deletedEdges.image (Sym2.map (pk w).ψ))
      New S Sample Reference Protect Bad Inner hRef hProtect hBadRef hInnerProtect hAgreement hRim hpart hcover).1
  refine ⟨f,?_,hsub,hsub.trans hSample⟩
  unfold OrdinaryTrackedComplementFor
  exact ⟨hC,hdis,hLocalResult.1,hLocalResult.2.1,hLocalResult.2.2.1,hLocalResult.2.2.2,hPhysical⟩
end Oberwolfach

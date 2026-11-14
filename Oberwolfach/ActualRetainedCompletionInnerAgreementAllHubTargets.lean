module

public import Oberwolfach.BufferedInnerAgreementAllHubTargets
public import Oberwolfach.RetainedOrdinaryAvoidsIntervalRoots
public import Oberwolfach.FirstVortexResidualCompletion
public import Oberwolfach.RetainedMarkedRootUniformity
public import Oberwolfach.ProtectedPairAllowedEdges

@[expose] public section
/-! The completion and its factor maps preserve every retained ordinary spoke
on the first inner vertex/hub pair. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U]

theorem actual_retained_completion_inner_agreement_all_hub_targets
    (π:Equiv.Perm V) (d c:ℕ) (hd:0<d) (σ:RawIntervalFamilyOutcome V U Bool Bool)
    (t:ℕ) (Jret:StartRetentionOutcome (rawStartHubSet π d σ false) t)
    (F:U→SimpleGraph V) (hF:∀u,(F u).IsRegularOfDegree 2)
    (K L:U→Type) [∀u,DecidableEq (K u)] [∀u,DecidableEq (L u)]
    (data:∀u,ActualResidualData (K:=K u) (J:=L u) (F u))
    (inner:∀u,retainedMarkedIndex π d σ false t Jret u→Fin (c*d+1)↪V)
    (ψ:U→V→V) (I:Finset V) (J:Finset U) (absorber:U→Finset V)
    (Kbad:SimpleGraph V) (assign:Sym2 V→U) (orient:Sym2 V→V×V)
    (BB:∀u,Finset {x // x∈(data u).remaining}) (g Φ:∀u,{x // x∈(data u).remaining}→V)
    (fC:∀u,{x // x∉bufferedPathStrictInterior (fun _=>c*d) (inner u)}↪V)
    (hCycle:∀u,(data u).t.biUnion (fun j=>((data u).C j).support.toFinset)⊆(data u).Cembed)
    (hDR:∀u,Disjoint (bufferedPathStrictInterior (fun _=>c*d) (inner u)) (data u).remaining)
    (hC:∀u (x:{x // x∉bufferedPathStrictInterior (fun _=>c*d) (inner u)}),x.val∈(data u).oldDomain→fC u x=ψ u x.val)
    (hR:∀u (x:{x // x∈(data u).remaining}) (hx:x.val∉bufferedPathStrictInterior (fun _=>c*d) (inner u)),fC u ⟨x.val,hx⟩=Φ u x)
    (hStart:∀u i (hx:inner u i 0∉bufferedPathStrictInterior (fun _=>c*d) (inner u)),fC u ⟨inner u i 0,hx⟩=i.val)
    (hEnd:∀u i (hx:inner u i (Fin.last (c*d))∉bufferedPathStrictInterior (fun _=>c*d) (inner u)),fC u ⟨inner u i (Fin.last (c*d)),hx⟩=(π^d) i.val)
    (hOld:∀u,Disjoint (((data u).oldDomain\bufferedPathStrictInterior (fun _=>c*d) (inner u)).image (ψ u))
      (Finset.univ.filter (fun v=>retainedRawMarkedSpokes π d σ false t Jret false false false v u)))
    (hAbs:∀u,Disjoint (absorber u) I)
    (hBB:∀u,(BB u).image (g u)=
      (residualSubtypeSet (data u).remaining (data u).prescribed).image (fun x=>ψ u x.1) ∪
      prescribedMatchingEndpoints (prescribedAssignedArcs Kbad assign orient u) ∪
      innerRequiredTargets Finset.univ I (fun u=>Finset.univ.filter (fun v=>retainedRawMarkedSpokes π d σ false t Jret false false false v u))
        (retainedFinalMarkedAt π d σ t Jret) absorber (fun u=>((data u).oldDomain\bufferedPathStrictInterior (fun _=>c*d) (inner u)).image (ψ u)) u)
    (hEndList:∀u v,v∈prescribedMatchingEndpoints (prescribedAssignedArcs Kbad assign orient u)→
      ∃e∈Kbad.edgeFinset,v∈e.toFinset ∧ u∈protectedPairEdgeHubs (rawReservedSpokeList π d σ) J e)
    (hag:∀u x,x∈BB u→Φ u x=g u x)
    (hfree:∀u x,x∉BB u→Φ u x∈rawReservedSpokeList π d σ u\(I∪retainedFinalMarkedAt π d σ t Jret u)):
    ∀u∈J,∀v∈I,
      let Y:=markedIntervalRootSet π (fun _:retainedMarkedIndex π d σ false t Jret u=>d) Subtype.val
      let End:=Finset.univ.image (fun i:retainedMarkedIndex π d σ false t Jret u=>(π^d) i.val)
      let R:=Finset.univ\(outsideBufferedPathImage (fun _=>c*d) (inner u) (fC u)∪End);
      (v∈R\Y↔retainedRawMarkedSpokes π d σ false t Jret false false false v u):=by
  let Y:=fun u=>markedIntervalRootSet π (fun _:retainedMarkedIndex π d σ false t Jret u=>d) Subtype.val
  let End:=fun u=>Finset.univ.image (fun i:retainedMarkedIndex π d σ false t Jret u=>(π^d) i.val)
  let Outer:=fun u=>Finset.univ.filter (fun v=>retainedRawMarkedSpokes π d σ false t Jret false false false v u)
  let Old:=fun u=>((data u).oldDomain\bufferedPathStrictInterior (fun _=>c*d) (inner u)).image (ψ u)
  let Anchor:=fun u=>(residualSubtypeSet (data u).remaining (data u).prescribed).image (fun x=>ψ u x.1)
  let Endpoints:=fun u=>prescribedMatchingEndpoints (prescribedAssignedArcs Kbad assign orient u)
  let Lists:=fun u=>rawReservedSpokeList π d σ u\(I∪retainedFinalMarkedAt π d σ t Jret u)
  let R:=fun u=>Finset.univ\(outsideBufferedPathImage (fun _=>c*d) (inner u) (fC u)∪End u)
  have hY:∀u,Y u=retainedFinalMarkedAt π d σ t Jret u:=by
    intro u; ext v
    simpa only [Y,retainedFinalMarkedAt,Finset.mem_filter,Finset.mem_univ,true_and] using
      retained_marked_root_membership π d hd σ false t Jret u v
  have hAnchor:∀u,Anchor u⊆Old u:=by
    intro u v hv
    obtain ⟨x,hx,hxv⟩:=Finset.mem_image.mp hv
    have hp:x.val∈(data u).prescribed:=(Finset.mem_filter.mp hx).2
    have hh: (data u).oldDomain∩(data u).remaining=(data u).prescribed :=(data u).graph_facts (hF u) |>.2.2.2.2.2
    have ho:x.val∈(data u).oldDomain:=by
      have hx':x.val∈(data u).oldDomain∩(data u).remaining:=by rw [hh];exact hp
      exact (Finset.mem_inter.mp hx').1
    have hi:x.val∉bufferedPathStrictInterior (fun _=>c*d) (inner u):=fun h=>(Finset.disjoint_left.mp (hDR u)) h x.property
    exact Finset.mem_image.mpr ⟨x.val,Finset.mem_sdiff.mpr ⟨ho,hi⟩,hxv⟩
  have hEndpoints:∀u∈J,Endpoints u=∅:=by
    intro u hu
    apply Finset.Subset.antisymm ?_ (Finset.empty_subset _)
    intro v hv
    obtain ⟨e,_,_,he⟩:=hEndList u v hv
    exact False.elim ((Finset.mem_filter.mp he).2.1 hu)
  have hstarts:∀u i (hx:inner u i 0∉bufferedPathStrictInterior (fun _=>c*d) (inner u)),fC u ⟨inner u i 0,hx⟩∈Y u:=by
    intro u i hx
    rw [hStart u i hx]
    exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,Finset.mem_image.mpr ⟨⟨0,hd⟩,Finset.mem_univ _,by simp⟩⟩
  have hends:∀u i (hx:inner u i (Fin.last (c*d))∉bufferedPathStrictInterior (fun _=>c*d) (inner u)),fC u ⟨inner u i (Fin.last (c*d)),hx⟩∈End u:=by
    intro u i hx
    rw [hEnd u i hx]
    exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
  have hbb:∀u,(BB u).image (g u)=Anchor u∪Endpoints u∪innerRequiredTargets Finset.univ I Outer Y absorber Old u:=by
    intro u
    simpa only [Y,Outer,Old,Anchor,Endpoints,hY] using hBB u
  have hLI:∀u,Disjoint (Lists u) I:=by
    intro u
    apply Finset.disjoint_left.mpr
    intro v hv hi
    exact (Finset.mem_sdiff.mp hv).2 (Finset.mem_union_left _ hi)
  have hh:=buffered_inner_completion_agreement_all_hub_targets I J (fun u=>retainedMarkedIndex π d σ false t Jret u)
    (fun _ _=>c*d) inner (fun u=>(data u).oldDomain) (fun u=>(data u).remaining) Y End Outer R absorber Lists Anchor Endpoints
    ψ Φ (fun u=>fC u) BB g (fun u=>(data u).old_domain_union_remaining (hCycle u)) hDR hC hR hstarts hends
    (fun _=>rfl) (fun u=>(retained_ordinary_avoids_interval_roots π d σ t Jret u).1)
    (fun u=>(hOld u).symm) (fun u=>(retained_ordinary_avoids_interval_roots π d σ t Jret u).2) hAbs hAnchor hEndpoints hbb hag hfree hLI
  intro u hu v hv
  simpa only [R,Y,Outer,Finset.mem_filter,Finset.mem_univ,true_and] using hh u hu v hv
end Oberwolfach

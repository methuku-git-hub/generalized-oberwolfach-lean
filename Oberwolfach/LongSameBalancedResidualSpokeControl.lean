module

public import Oberwolfach.LongSelectedClassDynamicSameBalancedImageLoad
public import Oberwolfach.LongResidualSpokeCompletionControl
public import Oberwolfach.MarkedBufferedReservedProtection
public import Oberwolfach.ReservedSpokeAvoidsRetainedMarked
public import Oberwolfach.ActualBufferedComplementFullEdgeExact
public import Oberwolfach.BufferedSourceWalkFromSupport
public import Oberwolfach.LongFactorComplementProvenance
public import Oberwolfach.LongSelectedClassDynamicSourceSameBalanced
public import Oberwolfach.ActualBufferedCanonicalEdgeSplitParameters
public import Oberwolfach.LongPackedSmallExactArcs
public import Oberwolfach.BufferedCanonicalArcsFromDirectedComplement

@[expose] public section
/-! The balanced complement and the correction packing are formed from the
same completion maps, hence their residual directed arc sets agree. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance sameBalancedPhysicalFactorDataSpokeControlFin (n:ℕ):DecidableEq (Fin n):=selectedAlignedSourceWithLoadFin n

theorem long_same_balanced_physical_residual_with_factor_data_spoke_control
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (hU:0<Fintype.card U) (F:U→SimpleGraph (Fin n)) (hF:∀w,(F w).IsRegularOfDegree 2)
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d m:ℕ) (ℓ:Fin K→ℕ)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (t:ℕ)
    (Jret:StartRetentionOutcome (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false) t)
    (σ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)
    (H:Finset U) (I:Finset (Fin n)) (Kbad:Finset (Sym2 (Fin n))→SimpleGraph (Fin n)) (Used DelG Reserve:SimpleGraph (Fin n)) (absorber:U→Finset (Fin n))
    (δ:ℝ) (Sclass:SimpleGraph (Fin n)) (Mhost:Fin n→Fin n→ℕ) (Dhost:Fin n→Fin n→Prop)
    (Extra:(U→Finset (Fin n))→Finset (Sym2 (Fin n))→Prop) (ρ₀ θ δglobal:ℝ)
    (hd:2≤d) (hDhostM:∀x y,Dhost x y→Mhost x y=1)
    (hphysical:∀x y,Mhost x y+Mhost y x=if Sclass.Adj x y then 1 else 0)
    (hPackEq:∀occupied Pack,Extra occupied Pack→Pack=Used.edgeFinset):
    let T:=bernoulliVertexSet (longRawHubState P π d raw true true)
    let e:{z // z∈T}↪_:=Function.Embedding.subtype _
    ∀M:Finset (RestrictedResource (mixedCandidateResources (longRawSeedResources (U:=U) π d m ℓ)) e),
    LongSelectedClassDynamicSourceSameBalancedImageLoad hU F P π d m ℓ raw t Jret σ H I Sclass Kbad Used DelG Reserve absorber δ Mhost Dhost Extra ρ₀ θ δglobal M →
    ∃(Pack:Finset (Sym2 (Fin n))) (Enew:U→Finset (Sym2 (Fin n))) (A:Finset (Fin n×Fin n)) (R:U→Finset (Fin n)),
      Pack=Used.edgeFinset ∧ Pack⊆Used.edgeFinset ∧ Pack⊆(longApproximatePhysicalGraph P π d σ).edgeFinset ∧
      (Kbad Pack).edgeFinset⊆Finset.univ.biUnion Enew ∧
      (∀w,Disjoint (Enew w) (spanningRestriction (Sclass\Used) I\Kbad Pack).edgeFinset) ∧
      (∀v,((prescribedPhysicalUnion Enew).degree v:ℝ)≤5*Real.sqrt δglobal*Fintype.card (Fin n)) ∧
      let Small:=SimpleGraph.fromEdgeSet (↑Pack:Set (Sym2 (Fin n)))⊔prescribedPhysicalUnion Enew
      let Y:=fun w=>markedIntervalRootSet π (fun _:retainedMarkedIndex π d (fun e=>raw (Sum.inr e)) false t Jret w=>d) Subtype.val
      Small.edgeFinset=A.image (fun a=>s(a.1,a.2)) ∧
      (∀a∈A,Mhost a.1 a.2=1) ∧
      (∀v,((orientationMatrixArcs Mhost\A).filter (fun a=>a.1=v)).card=(Finset.univ.filter (fun w=>v∈R w)).card ∧
        ((orientationMatrixArcs Mhost\A).filter (fun a=>a.2=v)).card=(Finset.univ.filter (fun w=>v∈R w)).card) ∧
      (∀w,Y w⊆R w ∧ (R w).card=(m+1)*(Y w).card) ∧
      (∀x y,Small.Adj x y→¬Reserve.Adj x y) ∧
      LongFactorComplementProvenance F Sclass P π d m raw t Jret Pack Enew A R ∧
      LongResidualSpokeCompletionControl π d raw t Jret R θ δglobal:=by
  intro T e M hsource
  letI:Nonempty U:=Fintype.card_pos_iff.mp hU
  have hdec:selectedClassDynamicSameBalancedImageLoadFin n=sameBalancedPhysicalFactorDataSpokeControlFin n:=Subsingleton.elim _ _
  have hdecK:selectedClassDynamicSameBalancedImageLoadFin K=sameBalancedPhysicalFactorDataSpokeControlFin K:=Subsingleton.elim _ _
  try rw [hdec] at hsource
  try rw [hdecK] at hsource
  rcases hsource with ⟨Dsrc,orig,hPair,hValid,hUnion,hArcs,E,hAlign,hLate,ext,hChunkRest1⟩
  rcases hChunkRest1 with ⟨inner,ψ,assign,data,hprops,pieces,hpieceEdge,hpieceArc,Pack,hExact,hChunkRest2⟩
  rcases hChunkRest2 with ⟨hload,hOldDisj,hOldPack,hApprox,hSelected,hassign,hsize,hUsed,hExtra,hcapacity,hChunkRest3⟩
  rcases hChunkRest3 with ⟨hupper,hglobal,hcompletion,piecesNew,Φ,fC,hgraphNew,hC,hR,hZ,hChunkRest4⟩
  rcases hChunkRest4 with ⟨hImage,hYavoid,hstart,hfinish,hSpokes,hsourceTail,hCover,hDirected,hHost,hPacked,hChunkRest5⟩
  rcases hChunkRest5 with ⟨⟨hinnerA,hdisA,hσ,hdegrees⟩,hKcover,hJavoid,hPackAvoid,hEunion,hLoss,hReserve⟩
  let Enew:=fun w=>((prescribedDependentGraph piecesNew w).edgeFinset).image (Sym2.map (Φ w))
  let old:=fun w=>((data w).deletedEdges\(Finset.univ.biUnion (fun i:{i // i∈(data w).s₁}=>((data w).path (.inl i)).edges.toFinset))).image (Sym2.map (ψ w))
  let tail:=fun w=>bufferedOrientedTailEmbedding (fun _=>(m+1)*d) (fun i=>ext w (.inl i)) (inner w) (hinnerA w) (hdisA w) (fC w)
  let head:=fun w=>bufferedOrientedHeadEmbedding (fun _=>(m+1)*d) (fun i=>ext w (.inl i)) (inner w) (hinnerA w) (hdisA w) (factorCycleOrientation (F w) (E w)) (hσ w) (fC w)
  let arcs:=fun w=>Finset.univ.image (fun x=>(tail w x,head w x))
  let A:=Finset.univ.biUnion arcs
  let R:=fun w=>Finset.univ\(outsideBufferedPathImage (fun _=>(m+1)*d) (inner w) (fC w) ∪
    Finset.univ.image (fun j:retainedMarkedIndex π d (fun e=>raw (Sum.inr e)) false t Jret w=>(π^d) j.val))
  have hsplit:∀w,(arcs w).image (fun a=>s(a.1,a.2))=old w∪Enew w:=by
    intro w
    rcases hprops w with ⟨hc,hd',hs,hcycle,hsupp,hinner,hmarker,hocc,hdr,hinj,hold,hreserved,hs2,ht,hT,hlen,hverts,hOrd,hMarked,hdis,hOldAvoid,hDirection,hOldDirected⟩
    have hcy:(data w).t.biUnion (fun j=>((data w).C j).support.toFinset)⊆(data w).Cembed:=by rw [hcycle]
    have hnew:∀(x:{x // x∉bufferedPathStrictInterior (fun _=>(m+1)*d) (inner w)}) (hx:x.val∈(data w).remaining),fC w x=Φ w ⟨x.val,hx⟩:=by
      intro x hx
      exact hR w ⟨x.val,hx⟩ x.property
    have hh:=actual_buffered_canonical_edge_split_with_parameters (data w) (hF w) hcy (m+1) d hc hd' hs (ext w) (inner w) hsupp hinner (hdisA w) (E w) (fun i k=>hDirection (.inl i) k) (hσ w) (fC w) (ψ w) (Φ w) (hC w) hnew
    have hgraphEdges:(prescribedDependentGraph piecesNew w).edgeFinset=((data w).graph.induce (↑(data w).remaining:Set (Fin n))).edgeFinset:=by
      ext edge
      simp only [SimpleGraph.mem_edgeFinset]
      rw [hgraphNew w]
      rfl
    rw [←hgraphEdges] at hh
    simpa only [arcs,tail,head,old,Enew,Finset.image_image,Function.comp_def] using hh
  have hCompSplit:∀w,(((F w).induce {x | x∉bufferedPathStrictInterior (fun _=>(m+1)*d) (inner w)}).edgeFinset).image (Sym2.map (fC w))=old w∪Enew w:=by
    intro w
    rcases hprops w with ⟨hc,hd',hs,hcycle,hsupp,hinner,hmarker,hocc,hdr,hinj,hold,hreserved,hs2,ht,hT,hlen,hverts,hOrd,hMarked,hdis,hOldAvoid,hDirection,hOldDirected⟩
    have hcy:(data w).t.biUnion (fun j=>((data w).C j).support.toFinset)⊆(data w).Cembed:=by rw [hcycle]
    have hnew:∀(x:{x // x∉bufferedPathStrictInterior (fun _=>(m+1)*d) (inner w)}) (hx:x.val∈(data w).remaining),fC w x=Φ w ⟨x.val,hx⟩:=by
      intro x hx
      exact hR w ⟨x.val,hx⟩ x.property
    have hh:=actual_buffered_complement_full_edge_exact (data w) (hF w) hcy (m+1) d hc hd' hs (ext w) (inner w) hsupp hinner (fC w) (ψ w) (Φ w) (hC w) hnew
    have hgraphEdges:(prescribedDependentGraph piecesNew w).edgeFinset=((data w).graph.induce (↑(data w).remaining:Set (Fin n))).edgeFinset:=by
      ext edge
      simp only [SimpleGraph.mem_edgeFinset]
      rw [hgraphNew w]
      rfl
    rw [←hgraphEdges] at hh
    exact hh
  have hwalk:∀w i,∃p:(F w).Walk (ext w (.inl i) 0) (ext w (.inl i) (Fin.last ((m+1)*d+4))),
      p.length=(m+1)*d+4 ∧ p.support=List.ofFn (ext w (.inl i)):=by
    intro w i
    have hsupp:= (hprops w).2.2.2.2.1 (.inl i)
    exact buffered_source_walk_from_support (F w) ((m+1)*d) (ext w (.inl i)) ((data w).P (.inl i)) hsupp
  have hValid':∀w p,p∈orig w→p.OriginalValid (Dsrc w):=by
    intro w p hp
    obtain ⟨a,xs,heq,hv⟩:=hValid w p hp
    exact hv
  have hOrient:∀w x y,(F w).Adj x y→Dsrc w x y∨Dsrc w y x:=by
    intro w
    exact (actual_source_orientation_covers_and_has_unique_incoming (F w) (orig w) (Dsrc w)
      (hPair w) (hValid' w) (hUnion w).2 (hArcs w)).1
  have hClassHost:∀w x y,(F w).Adj x.1 y.1→Sclass.Adj (fC w x) (fC w y):=by
    intro w x y hxy
    have hp:=hphysical (fC w x) (fC w y)
    by_contra hn
    rw [if_neg hn] at hp
    rcases hOrient w x.1 y.1 hxy with ha|ha
    · have hm:=hDhostM _ _ (hDirected w x y hxy ha)
      omega
    · have hm:=hDhostM _ _ (hDirected w y x hxy.symm ha)
      omega
  have hSmall:=long_packed_small_exact_arcs Used Pack Enew old arcs hUsed hExact hEunion hsplit
  have hA:∀a∈A,Mhost a.1 a.2=1:=by
    intro a ha
    obtain ⟨w,_,hw⟩:=Finset.mem_biUnion.mp ha
    obtain ⟨x,_,rfl⟩:=Finset.mem_image.mp hw
    exact hDhostM _ _ (buffered_canonical_arcs_from_directed_complement (F w) (hF w) (E w) (fun _=>(m+1)*d)
      (fun i=>ext w (.inl i)) (inner w) (hinnerA w) (hdisA w) (hσ w) (fC w) (Dsrc w) (hAlign w) Dhost (hDirected w) x)
  refine ⟨Pack,Enew,A,R,hPackEq _ Pack hExtra,hUsed,hApprox,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · convert hKcover using 1 <;> congr! 6 <;> exact Subsingleton.elim _ _
  · convert hJavoid using 1 <;> congr! 6 <;> exact Subsingleton.elim _ _
  · convert hLoss using 1 <;> congr! 6 <;> exact Subsingleton.elim _ _
  · exact hSmall
  · exact hA
  · intro v
    simpa only [A,arcs,R,Finset.mem_sdiff,Finset.mem_univ,true_and] using hdegrees v
  · intro w
    exact ⟨(hSpokes w).1,(hSpokes w).2.1⟩
  · convert hReserve using 1 <;> congr! 6 <;> exact Subsingleton.elim _ _
  · constructor
    · exact ⟨(fun w i=>ext w (.inl i)),inner,fC,E,hinnerA,hdisA,hwalk,hσ,old,hExact,hOldDisj,rfl,hsplit,hCompSplit,(fun _=>rfl),hYavoid,hstart,hfinish,hClassHost,hHost,hPacked⟩
    · let C:=fun w=>Finset.univ.image (Φ w)
      refine ⟨C,?_,?_,?_⟩
      · intro v
        simpa only [C,Fintype.card_fin] using hImage v
      · intro w
        have hc:((C w).card:ℝ)≤(data w).remaining.card:=by
          have hn:(C w).card≤Fintype.card {x // x∈(data w).remaining}:=by
            exact (Finset.card_image_le).trans (by simp)
          simpa only [Fintype.card_coe] using (show ((C w).card:ℝ)≤Fintype.card {x // x∈(data w).remaining} by exact_mod_cast hn)
        exact hc.trans (hupper w)
      · intro w v hv hnot
        rcases hprops w with ⟨hc,hd',hs,hcycle,hsupp,hinner,hmarker,hocc,hdr,hinj,hold,hreserved,hs2,ht,hT,hlen,hverts,hOrd,hMarked,hdis,hOldAvoid,hDirection,hOldDirected⟩
        let Y:=markedIntervalRootSet π (fun _:retainedMarkedIndex π d (fun e=>raw (Sum.inr e)) false t Jret w=>d) Subtype.val
        let B:=Finset.univ.image (fun j:retainedMarkedIndex π d (fun e=>raw (Sum.inr e)) false t Jret w=>(π^d) j.val)
        let L:=rawReservedSpokeList π d (fun e=>raw (Sum.inr e)) w
        have hcover:(data w).oldDomain∪(data w).remaining=Finset.univ:=(data w).old_domain_union_remaining (by rw [hcycle])
        have hB:Disjoint B L:=by
          apply Finset.disjoint_left.mpr
          intro x hx hl
          obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp hx
          have hh:=(raw_reserved_spoke_list_avoids_old_labels π d (fun e=>raw (Sum.inr e)) t Jret w).2 (.inl i) ⟨d,by omega⟩
          exact hh (by simpa only [retainedAndRawIntervalRoot] using hl)
        have hY:Disjoint Y L:=by
          apply Finset.disjoint_left.mpr
          intro x hx hl
          have hx':x∈retainedFinalMarkedAt π d (fun e=>raw (Sum.inr e)) t Jret w:=by
            simpa only [Y,retainedFinalMarkedAt,Finset.mem_filter,Finset.mem_univ,true_and] using
              (retained_marked_root_membership π d (by omega) (fun e=>raw (Sum.inr e)) false t Jret w x).mp hx
          exact (Finset.disjoint_left.mp (reserved_spoke_avoids_retained_marked π d (fun e=>raw (Sum.inr e)) t Jret w)) hl hx'
        have hh:=marked_buffered_reserved_protection (fun _=>(m+1)*d) (inner w) (data w).oldDomain (data w).remaining (ψ w) (Φ w) (fC w)
          hcover (hC w) (hR w) L B Y hreserved hB hY v hv hnot
        exact hh
end Oberwolfach

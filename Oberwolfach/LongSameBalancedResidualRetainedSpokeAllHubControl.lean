module

public import Oberwolfach.LongSelectedRetainedClassDynamicSameBalancedAllHubBudget
public import Oberwolfach.ActualRetainedCompletionProtectsRawSpokes
public import Oberwolfach.LongResidualSpokeRetainedLoss
public import Oberwolfach.LongRetentionMismatchLocal
public import Oberwolfach.LongSelectedRetainedClassDynamicSameBalancedTrackedOuter
public import Oberwolfach.LongResidualSpokeCompletionOuterControl
public import Oberwolfach.LongRetainedProtectedInnerTargets
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
local instance sameBalancedPhysicalRetainedFactorDataAllHubFin (n:ℕ):DecidableEq (Fin n):=selectedAlignedSourceWithLoadFin n

theorem long_same_balanced_physical_residual_with_all_hub_spoke_control
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (hU:0<Fintype.card U) (F:U→SimpleGraph (Fin n)) (hF:∀w,(F w).IsRegularOfDegree 2)
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d m:ℕ) (ℓ:Fin K→ℕ)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (t:ℕ)
    (Jret:StartRetentionOutcome (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false) t)
    (σ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)
    (H:Finset U) (I:Finset (Fin n)) (Kbad:Finset (Sym2 (Fin n))→SimpleGraph (Fin n)) (Used DelG Reserve:SimpleGraph (Fin n)) (absorber:U→Finset (Fin n))
    (δ:ℝ) (Sclass:SimpleGraph (Fin n)) (Mhost:Fin n→Fin n→ℕ) (Dhost:Fin n→Fin n→Prop)
    (Extra:(U→Finset (Fin n))→Finset (Sym2 (Fin n))→Prop) (ρ₀ θ δglobal Pbound ζ:ℝ)
    (hd:2≤d) (hDhostM:∀x y,Dhost x y→Mhost x y=1)
    (hphysical:∀x y,Mhost x y+Mhost y x=if Sclass.Adj x y then 1 else 0)
    (hPackEq:∀occupied Pack,Extra occupied Pack→Pack=Used.edgeFinset)
    (hrows:RetainedRestrictionLocalGood π d (fun e=>raw (Sum.inr e)) false t I Finset.univ ζ Jret):
    let T:=bernoulliVertexSet (longRawHubState P π d raw true true)
    let e:{z // z∈T}↪_:=Function.Embedding.subtype _
    ∀M:Finset (RestrictedResource (mixedCandidateResources (longRawSeedResources (U:=U) π d m ℓ)) e),
    LongSelectedRetainedClassDynamicSourceSameBalancedAllHubBudget hU F P π d m ℓ raw t Jret σ H I Sclass Kbad Used DelG Reserve absorber δ Mhost Dhost Extra ρ₀ θ δglobal Pbound M →
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
      LongResidualSpokeCompletionControl π d raw t Jret R θ δglobal ∧
      (∀w,((I.filter (fun v=>retainedRawMarkedSpokes π d (fun e=>raw (Sum.inr e)) false t Jret false false false v w ∧ v∉R w\Y w)).card:ℝ)≤
        ζ*I.card+Pbound+2*(⌈4*((Kbad Pack).edgeFinset.card:ℝ)/(((ρ₀/4)/40000)*Fintype.card (Fin n))⌉₊:ℕ)) ∧
      (∀w v,v∈I→v∈R w\Y w → retainedRawMarkedSpokes π d (fun e=>raw (Sum.inr e)) false t Jret false false false v w) ∧
      (∀w∈H,∀v∈I,v∈R w\Y w↔retainedRawMarkedSpokes π d (fun e=>raw (Sum.inr e)) false t Jret false false false v w):=by
  intro T e M hsource
  letI:Nonempty U:=Fintype.card_pos_iff.mp hU
  have hdec:selectedRetainedClassDynamicSameBalancedAllHubBudgetFin n=sameBalancedPhysicalRetainedFactorDataAllHubFin n:=Subsingleton.elim _ _
  have hdecK:selectedRetainedClassDynamicSameBalancedAllHubBudgetFin K=sameBalancedPhysicalRetainedFactorDataAllHubFin K:=Subsingleton.elim _ _
  try rw [hdec] at hsource
  try rw [hdecK] at hsource
  rcases hsource with ⟨Dsrc,orig,hPair,hValid,hUnion,hArcs,E,hAlign,hLate,ext,hChunkRest1⟩
  rcases hChunkRest1 with ⟨inner,ψ,assign,data,hprops,hpres,pieces,hpieceEdge,hpieceArc,Pack,hChunkRest2⟩
  rcases hChunkRest2 with ⟨hExact,hload,hOldDisj,hOldPack,hApprox,hSelected,hassign,hsize,hUsed,hExtra,hChunkRest3⟩
  rcases hChunkRest3 with ⟨hcapacity,hupper,hglobal,hallload,hcompletion,piecesNew,Φ,fC,hgraphNew,hC,hChunkRest4⟩
  rcases hChunkRest4 with ⟨hR,hZ,hImage,hYavoid,hstart,hfinish,hSpokes,hsourceTail,hCover,hDirected,hChunkRest5⟩
  rcases hChunkRest5 with ⟨hHost,hPacked,hFirst,hNoNew,hTracked,hLocal,⟨hinnerA,hdisA,hσ,hdegrees⟩,hKcover,hJavoid,hPackAvoid,hChunkRest6⟩
  rcases hChunkRest6 with ⟨hEunion,hLoss,hReserve⟩
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
  · refine ⟨?_,?_,?_,hNoNew,hFirst⟩
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
      · have hCycle:∀w,(data w).t.biUnion (fun j=>((data w).C j).support.toFinset)⊆(data w).Cembed:=by
          intro w;rw [(hprops w).2.2.2.1]
        have hprotect:=actual_retained_completion_protects_raw_spokes π d (m+1) (by omega) (fun e=>raw (Sum.inr e)) t Jret F
          (fun w=>retainedMarkedIndex π d (fun e=>raw (Sum.inr e)) false t Jret w ⊕
            {a:Fin n // rawIntervalColouredStart π d (fun e=>raw (Sum.inr (w,e))) a true})
          (fun w=>{a:LongRawSelectedOrdinary π d m ℓ e M // (assign a).1=w})
          data inner ψ Φ fC hCycle (fun w=>(hprops w).2.2.2.2.2.2.2.2.1) hC hR hstart hfinish
          (fun w=>(hprops w).2.2.2.2.2.2.2.2.2.2.2.1)
        simpa only [C,R] using hprotect
    · intro w
      have hCycle:∀w,(data w).t.biUnion (fun j=>((data w).C j).support.toFinset)⊆(data w).Cembed:=by
        intro w;rw [(hprops w).2.2.2.1]
      have hprotect:=actual_retained_completion_protects_raw_spokes π d (m+1) (by omega) (fun e=>raw (Sum.inr e)) t Jret F
        (fun w=>retainedMarkedIndex π d (fun e=>raw (Sum.inr e)) false t Jret w ⊕
          {a:Fin n // rawIntervalColouredStart π d (fun e=>raw (Sum.inr (w,e))) a true})
        (fun w=>{a:LongRawSelectedOrdinary π d m ℓ e M // (assign a).1=w})
        data inner ψ Φ fC hCycle (fun w=>(hprops w).2.2.2.2.2.2.2.2.1) hC hR hstart hfinish
        (fun w=>(hprops w).2.2.2.2.2.2.2.2.2.2.2.1)
      have hprotect':∀w v,v∈rawReservedSpokeList π d (fun e=>raw (Sum.inr e)) w→v∉Finset.univ.image (Φ w)→
          v∈R w\markedIntervalRootSet π (fun _:retainedMarkedIndex π d (fun e=>raw (Sum.inr e)) false t Jret w=>d) Subtype.val:=by
        simpa only [R] using hprotect
      have hl:=long_residual_spoke_retained_loss π d raw t Jret R (fun w=>Finset.univ.image (Φ w)) I hprotect' w
      have hm:=long_retention_mismatch_local π d raw t Jret I ζ hrows w
      have hi:(((I∩Finset.univ.image (Φ w))∩(Finset.univ.filter (fun v=>retainedRawMarkedSpokes π d (fun e=>raw (Sum.inr e)) false t Jret false false false v w))).card:ℝ)≤
          ((residualSubtypeSet (data w).remaining (data w).prescribed).card:ℝ)+
            2*(⌈4*((Kbad Pack).edgeFinset.card:ℝ)/(((ρ₀/4)/40000)*Fintype.card (Fin n))⌉₊:ℕ):=by
        have hh:=hLocal w
        have hh':((((Finset.univ.image (Φ w))∩I)∩(Finset.univ.filter (fun v=>retainedRawMarkedSpokes π d (fun e=>raw (Sum.inr e)) false t Jret false false false v w))).card:ℝ)≤
          ((residualSubtypeSet (data w).remaining (data w).prescribed).card:ℝ)+
            2*(⌈4*((Kbad Pack).edgeFinset.card:ℝ)/(((ρ₀/4)/40000)*Fintype.card (Fin n))⌉₊:ℕ):=by exact_mod_cast hh
        simpa only [Finset.inter_comm] using hh'
      linarith [hpres w]
end Oberwolfach

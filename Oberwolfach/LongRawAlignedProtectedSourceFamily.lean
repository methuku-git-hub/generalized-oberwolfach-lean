module

public import Oberwolfach.ResidualActualLateContinuation
public import Oberwolfach.ResidualActualLateIndicesComplementAligned
public import Oberwolfach.LongRawSourcePackedProtectedFamily
public import Oberwolfach.LongRawSourceEmbeddingFromEventProtectedList
public import Oberwolfach.LongRawMatchingActualOldPacking
public import Oberwolfach.LongRawComponentAssignmentFromMaps
public import Oberwolfach.LongAssignedActualIntervalCapacityDecidable
public import Oberwolfach.LongAssignedPaddedLengths

@[expose] public section
/-! Actual long source paths and their old embeddings from one matching,
the original class hypothesis, and the same-outcome hub start counts. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 40000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance longRawAlignedProtectedSourceDecEqFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem long_raw_protected_sources_with_aligned_residual_pieces
    {N K:ℕ} {U:Type} [Fintype U] [DecidableEq U] [Nonempty (Fin N)]
    (F:U→SimpleGraph (Fin N)) (hF:∀w,(F w).IsRegularOfDegree 2) (hU:0<Fintype.card U)
    (Allowed:Set ℕ) (hAllowed:∀w,AllowedCycleLengths (F w) Allowed)
    (hn:0<N) (hK:3≤K) (hclass:∀w,factorPreparationClass (F w) K=none)
    (P₀:SimpleGraph (Fin N)) (π:Equiv.Perm (Fin N)) (d m:ℕ) (hd:2≤d) (hm:7≤m)
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (θ:ℝ) (hθ:0<θ)
    (hcut:5/(((m:ℝ)+1)*(d:ℝ)+5)+((m:ℝ)+1)*(d:ℝ)/(K+1)≤θ/2)
    (hlarge:8*((m:ℝ)+1)/θ<(N:ℝ)^((1:ℝ)/4))
    (raw:RawMarkedOutcome (Fin N) U Bool Bool) (t:ℕ)
    (Jret:StartRetentionOutcome (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false) t)
    (hcounts:∀w g,|rawIntervalHubStartCount π d g (fun e=>raw (Sum.inr e)) w-
      (N:ℝ)*longAssignedIntervalProbability F hF K m θ w g/d|<(N:ℝ)^(3/4:ℝ)/d)
    : letI:Nonempty U:=Fintype.card_pos_iff.mp hU
      ∃(Dsrc:∀w,Fin N→Fin N→Prop) (orig:∀w,List (PrescribedSourcePiece (Fin N))),
      (∀w,(orig w).Pairwise (fun p q=>Disjoint p.vertices.toFinset q.vertices.toFinset)) ∧
      (∀w p,p∈orig w→∃a xs,p=.cycle a xs ∧ p.OriginalValid (Dsrc w)) ∧
      (∀w,sourcePieceVerticesUnion (orig w)=Finset.univ ∧ sourcePieceEdgesUnion (orig w)=(F w).edgeFinset) ∧
      (∀w x y,Dsrc w x y↔(x,y)∈sourcePieceArcsUnion (orig w)) ∧
      ∃E:∀w (C:(F w).ConnectedComponent),SimpleGraph.cycleGraph (Fintype.card C) ≃g C.toSimpleGraph,
        (∀w x,Dsrc w x (factorCycleOrientation (F w) (E w) x)) ∧
        LateComplementContinuation (V:=Fin N) F Dsrc ∧
    let ℓ:=longAssignedPaddedLength (K:=K)
    let state:=longRawHubState P₀ π d raw true true
    let e:{z // z∈bernoulliVertexSet state}↪_:=Function.Embedding.subtype _
    let R:=longRawSeedResources (U:=U) π d m ℓ
    ∀M:Finset (RestrictedResource (mixedCandidateResources R) e),
    (∀x∈M,∀y∈M,x≠y→Disjoint (restrictedResourceSet (mixedCandidateResources R) e x)
      (restrictedResourceSet (mixedCandidateResources R) e y))→
    LongRawOrdinaryComponentMapsProperty F π d m ℓ e M→
    ∃assign:LongRawSelectedOrdinary π d m ℓ e M↪(Σw,(F w).ConnectedComponent),
    ∃(data:∀w,ActualResidualData
      (K:=(retainedMarkedIndex π d (fun e=>raw (Sum.inr e)) false t Jret w) ⊕
        {a:Fin N // rawIntervalColouredStart π d (fun e=>raw (Sum.inr (w,e))) a true})
      (J:={a:LongRawSelectedOrdinary π d m ℓ e M // (assign a).1=w}) (F w))
      (ext:∀w,(retainedMarkedIndex π d (fun e=>raw (Sum.inr e)) false t Jret w ⊕
        {a:Fin N // rawIntervalColouredStart π d (fun e=>raw (Sum.inr (w,e))) a true})→Fin ((m+1)*d+5)↪Fin N)
      (inner:∀w,retainedMarkedIndex π d (fun e=>raw (Sum.inr e)) false t Jret w→Fin ((m+1)*d+1)↪Fin N)
      (ψ:∀w,Fin N→Fin N),
    (∀w,(data w).c=m+1 ∧ (data w).d=d ∧ (data w).s₁=firstSumIndices ∧
      (data w).Cembed=(data w).t.biUnion (fun j=>((data w).C j).support.toFinset) ∧
      (∀i,((data w).P i).support=List.ofFn (ext w i)) ∧
      (∀a k,inner w a k=ext w (.inl a) ⟨k.val+2,by omega⟩) ∧
      Disjoint (bufferedPathStrictInterior (fun _=>(m+1)*d) (inner w)) (data w).remaining ∧
      Set.InjOn (ψ w) (↑((data w).oldDomain\bufferedPathStrictInterior (fun _=>(m+1)*d) (inner w)):Set (Fin N)) ∧
      ActualOldArcContainment (data w) (ψ w) (E w)
        (fun x y=>({x,y}:Finset (Fin N))∈longRawPhysicalHubRims P₀ π d m ℓ raw true true M w) ∧
      Disjoint (((data w).oldDomain\bufferedPathStrictInterior (fun _=>(m+1)*d) (inner w)).image (ψ w))
        (rawIntervalProtectedUnassignedList π d (fun e=>raw (Sum.inr e)) false true t Jret w)) ∧
    ∃(pieces:∀w,List (PrescribedSourcePiece {x // x∈(data w).remaining})),
      (∀w,prescribedDependentGraph pieces w=((data w).graph).induce (↑(data w).remaining:Set (Fin N))) ∧
      (∀w x y,prescribedDependentDigraph pieces w x y ↔ Dsrc w x.1 y.1 ∧ (data w).graph.Adj x.1 y.1) ∧
    let old:=fun w=>((data w).deletedEdges\(Finset.univ.biUnion
      (fun i:{i // i∈(data w).s₁}=>((data w).path (.inl i)).edges.toFinset))).image (Sym2.map (ψ w))
    ∃Pack:Finset (Sym2 (Fin N)),
      (∀w z,w≠z→Disjoint (old w) (old z)) ∧ (∀w,old w⊆Pack) :=by
  letI:Nonempty U:=Fintype.card_pos_iff.mp hU
  obtain ⟨Dsrc,orig,hpair,hcycles,hwhole,hArcs,E,halign,hres⟩:=
    actual_factor_late_indices_complement_with_aligned_orders (V:=Fin N) F hF
  refine ⟨Dsrc,orig,hpair,hcycles,hwhole,hArcs,E,halign,hres,?_⟩
  intro ℓ state e R M hmatch hmaps
  have hvalid:∀w p,p∈orig w→p.OriginalValid (Dsrc w):=by
    intro w p hp
    obtain ⟨a,xs,rfl,hv⟩:=hcycles w p hp
    exact hv
  obtain ⟨assign,data,ext,inner,ψ,hprops,Pack,hdis,hsub⟩:=
    long_raw_protected_source_family_and_old_packing F hF E Allowed hAllowed hn hK hclass P₀ π d m hd hm hnoshort θ hθ hcut hlarge raw t Jret hcounts orig Dsrc hpair hvalid (fun w=>(hwhole w).2) hArcs halign M hmatch hmaps
  let Ktype:=fun w:U=>(retainedMarkedIndex π d (fun e=>raw (Sum.inr e)) false t Jret w) ⊕
    {a:Fin N // rawIntervalColouredStart π d (fun e=>raw (Sum.inr (w,e))) a true}
  let Jtype:=fun w:U=>{a:LongRawSelectedOrdinary π d m ℓ e M // (assign a).1=w}
  obtain ⟨pieces,hgraph,harcs,_⟩:=hres Ktype Jtype data
  exact ⟨assign,data,ext,inner,ψ,hprops,pieces,hgraph,harcs,Pack,hdis,hsub⟩
end Oberwolfach

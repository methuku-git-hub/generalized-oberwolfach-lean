module

public import Oberwolfach.LongSelectedRetainedClassDynamicHostSameEmbeddingImageLoad
public import Oberwolfach.FirstVortexResidualCompletionOrientedTracked
public import Oberwolfach.ResidualDegreesFromRetainedBalancedExplicit
public import Oberwolfach.LongSelectedOrientedSourceHostComplement
public import Oberwolfach.ActualInnerTargetsCovered
public import Oberwolfach.ActualBufferedOrientationComplement
public import Oberwolfach.ActualSumEndpointAgreement
public import Oberwolfach.RetainedSpokesFromComplement
public import Oberwolfach.LongSelectedProtectedSourceResidualCompletion
public import Oberwolfach.ActualResidualComplementAvoidsRoots
public import Oberwolfach.LongSelectedAlignedSourceResidualCompletion
public import Oberwolfach.ActualResidualCompletionComplement

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance selectedRetainedClassDynamicSameBalancedTrackedLocalFin (n:ℕ):DecidableEq (Fin n):=selectedAlignedSourceWithLoadFin n

def LongSelectedRetainedClassDynamicSourceSameBalancedTrackedLocal
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (hU:0<Fintype.card U) (F:U→SimpleGraph (Fin n)) (P:SimpleGraph (Fin n))
    (π:Equiv.Perm (Fin n)) (d m:ℕ) (ℓ:Fin K→ℕ)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (t:ℕ)
    (Jret:StartRetentionOutcome (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false) t)
    (σ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)
    (H:Finset U) (A:Finset (Fin n)) (Sclass:SimpleGraph (Fin n)) (Kbad:Finset (Sym2 (Fin n))→SimpleGraph (Fin n)) (Used DelG Reserve:SimpleGraph (Fin n)) (absorber:U→Finset (Fin n)) (δ:ℝ)
    (Mhost:Fin n→Fin n→ℕ) (Dhost:Fin n→Fin n→Prop)
    (Extra:(U→Finset (Fin n))→Finset (Sym2 (Fin n))→Prop) (ρ₀ θ δglobal:ℝ):
    let T:=bernoulliVertexSet (longRawHubState P π d raw true true)
    let e:{z // z∈T}↪_:=Function.Embedding.subtype _
    ∀M:Finset (RestrictedResource (mixedCandidateResources (longRawSeedResources (U:=U) π d m ℓ)) e), Prop :=
    letI:Nonempty U:=Fintype.card_pos_iff.mp hU
    let T:=bernoulliVertexSet (longRawHubState P π d raw true true)
    let e:{z // z∈T}↪_:=Function.Embedding.subtype _
    fun M=>
      ∃(Dsrc:∀w,Fin n→Fin n→Prop) (orig:∀w,List (PrescribedSourcePiece (Fin n))),
      (∀w,(orig w).Pairwise (fun p q=>Disjoint p.vertices.toFinset q.vertices.toFinset)) ∧
      (∀w p,p∈orig w→∃a xs,p=.cycle a xs ∧ p.OriginalValid (Dsrc w)) ∧
      (∀w,sourcePieceVerticesUnion (orig w)=Finset.univ ∧ sourcePieceEdgesUnion (orig w)=(F w).edgeFinset) ∧
      (∀w x y,Dsrc w x y↔(x,y)∈sourcePieceArcsUnion (orig w)) ∧
      ∃E:∀w (C:(F w).ConnectedComponent),SimpleGraph.cycleGraph (Fintype.card C) ≃g C.toSimpleGraph,
        (∀w x,Dsrc w x (factorCycleOrientation (F w) (E w) x)) ∧
        LateComplementContinuation (V:=Fin n) F Dsrc ∧
    ∃(ext:∀w:U,(retainedMarkedIndex π d (fun e=>raw (Sum.inr e)) false t Jret w ⊕
        {a:Fin n // rawIntervalColouredStart π d (fun e=>raw (Sum.inr (w,e))) a true})→Fin ((m+1)*d+5)↪Fin n)
      (inner:∀w:U,retainedMarkedIndex π d (fun e=>raw (Sum.inr e)) false t Jret w→Fin ((m+1)*d+1)↪Fin n)
      (ψ:∀w:U,Fin n→Fin n) ,
    ∃assign:LongRawSelectedOrdinary π d m ℓ e M↪(Σw,(F w).ConnectedComponent),
    ∃(data:∀w:U,ActualResidualData
      (K:=(retainedMarkedIndex π d (fun e=>raw (Sum.inr e)) false t Jret w) ⊕
        {a:Fin n // rawIntervalColouredStart π d (fun e=>raw (Sum.inr (w,e))) a true})
      (J:={a:LongRawSelectedOrdinary π d m ℓ e M // (assign a).1=w}) (F w)) ,
    (∀w,(data w).c=m+1 ∧ (data w).d=d ∧ (data w).s₁=firstSumIndices ∧
      (data w).Cembed=(data w).t.biUnion (fun j=>((data w).C j).support.toFinset) ∧
      (∀i,((data w).P i).support=List.ofFn (ext w i)) ∧
      (∀a k,inner w a k=ext w (.inl a) ⟨k.val+2,by omega⟩) ∧
      (∀i (j:Fin (d+1)),bufferedMarker (m+1) d (ext w i) j∈(data w).prescribed→
        ψ w (bufferedMarker (m+1) d (ext w i) j)=(π^j.val)
          (retainedAndRawIntervalRoot π d (fun e=>raw (Sum.inr e)) false true t Jret w i)) ∧
      (∀i∈(data w).s₂,∀j:Fin (d+1),∃x∈(data w).oldDomain\bufferedPathStrictInterior (fun _=>(m+1)*d) (inner w),
        ψ w x=(π^j.val) (retainedAndRawIntervalRoot π d (fun e=>raw (Sum.inr e)) false true t Jret w i)) ∧
      Disjoint (bufferedPathStrictInterior (fun _=>(m+1)*d) (inner w)) (data w).remaining ∧
      Set.InjOn (ψ w) (↑((data w).oldDomain\bufferedPathStrictInterior (fun _=>(m+1)*d) (inner w)):Set (Fin n)) ∧
      ActualOldArcContainment (data w) (ψ w) (E w)
        (fun x y=>({x,y}:Finset (Fin n))∈longRawPhysicalHubRims P π d m ℓ raw true true M w) ∧
      Disjoint (((data w).oldDomain\bufferedPathStrictInterior (fun _=>(m+1)*d) (inner w)).image (ψ w))
        (Finset.univ.filter (fun v=>retainedRawMarkedSpokes π d (fun e=>raw (Sum.inr e)) false t Jret false false false v w)) ∧
      (data w).s₂=secondSumIndices ∧ (data w).t=Finset.univ ∧
      (∀i,(data w).T i=packedPhysicalSpokePositions _ _ _ _ m (3*d) d π
        (rawMarkedPairSpokes π d raw true true false) (rawMarkedPairSpokes π d raw true true true)
        (longRawMarkedWheelsAtHub P π d m ℓ raw true true M w) w
        (retainedAndRawIntervalRoot π d (fun e=>raw (Sum.inr e)) false true t Jret w i)) ∧
      (∀j,((data w).C j).length=ℓ (longRawSelectedOrdinaryPayload π d m ℓ e M j.val).1) ∧
      (∀j,((data w).C j).toSubgraph.verts=
        (assignedComponentAtHub F (fun a=>(assign a).1) (fun a=>(assign a).2) w j).supp) ∧
      (∀j:{a:LongRawSelectedOrdinary π d m ℓ e M // (assign a).1=w},∀x∈Finset.univ.image ((longRawSelectedOrdinaryWheel π d m ℓ e M j.val).val.1.val),
        x∈((data w).oldDomain\bufferedPathStrictInterior (fun _=>(m+1)*d) (inner w)).image (ψ w)) ∧
      (∀W∈longRawMarkedWheelsAtHub P π d m ℓ raw true true M w,∀i:Fin (m+1),
        W.1.val i∈((data w).oldDomain\bufferedPathStrictInterior (fun _=>(m+1)*d) (inner w)).image (ψ w)) ∧
      (∀i j,i≠j→Disjoint (Finset.univ.image (ext w i)) (Finset.univ.image (ext w j))) ∧
      (∀x,x∈(data w).oldDomain→x∉bufferedPathFullDomain (fun _=>(m+1)*d) (inner w)→
        ψ w x∉markedIntervalRootSet π (fun _:retainedMarkedIndex π d (fun e=>raw (Sum.inr e)) false t Jret w=>d) Subtype.val) ∧
      (∀i (j:Fin ((m+1)*d+4)),factorCycleOrientation (F w) (E w) (ext w i j.castSucc)=ext w i j.succ) ∧
      ActualOldArcContainment (data w) (ψ w) (E w) (rawMixedPhysicalArc P π d raw)) ∧
    ∃(pieces:∀w,List (PrescribedSourcePiece {x // x∈(data w).remaining})),
      (∀w,prescribedDependentGraph pieces w=((data w).graph).induce (↑(data w).remaining:Set (Fin n))) ∧
      (∀w x y,prescribedDependentDigraph pieces w x y ↔ Dsrc w x.1 y.1 ∧ (data w).graph.Adj x.1 y.1) ∧
    let old:=fun w=>((data w).deletedEdges\(Finset.univ.biUnion
      (fun i:{i // i∈(data w).s₁}=>((data w).path (.inl i)).edges.toFinset))).image (Sym2.map (ψ w))
    ∃Pack:Finset (Sym2 (Fin n)),
      Pack=Finset.univ.biUnion old ∧
    (let occupied:=fun w=>((data w).oldDomain\bufferedPathStrictInterior (fun _=>(m+1)*d) (inner w)).image (ψ w)
     let Z:=innerRequiredTargets H A (rawReservedSpokeList π d (fun e=>raw (Sum.inr e)))
       (retainedFinalMarkedAt π d (fun e=>raw (Sum.inr e)) t Jret) absorber occupied
     ∀v∈A,((H.filter (fun w=>v∈(residualSubtypeSet (data w).remaining (data w).prescribed).image (fun x=>ψ w x.1))).card:ℝ)+
       (Kbad Pack).degree v+((H.filter (fun w=>v∈Z w)).card:ℝ)≤δ*(A.card:ℝ)) ∧
      (∀w z,w≠z→Disjoint (old w) (old z)) ∧ (∀w,old w⊆Pack) ∧
      Pack⊆(longApproximatePhysicalGraph P π d σ).edgeFinset ∧
      (∀x y,rawSelectedPhysicalRelation P π d (fun e=>σ (Sum.inl e)) x y→s(x,y)∉Pack) ∧
      (∀a,(assign a).1=(longRawSelectedOrdinaryWheel π d m ℓ e M a).val.2) ∧
      (∀a,Fintype.card (assign a).2=ℓ (longRawSelectedOrdinaryPayload π d m ℓ e M a).1) ∧
      Pack⊆Used.edgeFinset ∧
      Extra (fun w=>((data w).oldDomain\bufferedPathStrictInterior (fun _=>(m+1)*d) (inner w)).image (ψ w)) Pack ∧
      (let occupied:=fun w=>((data w).oldDomain\bufferedPathStrictInterior (fun _=>(m+1)*d) (inner w)).image (ψ w)
       let Z:=innerRequiredTargets H A (rawReservedSpokeList π d (fun e=>raw (Sum.inr e)))
         (retainedFinalMarkedAt π d (fun e=>raw (Sum.inr e)) t Jret) absorber occupied
       ∀w,8*(residualSubtypeSet (data w).remaining (data w).prescribed).card+
         8*⌈4*((Kbad Pack).edgeFinset.card:ℝ)/(((ρ₀/4)/40000)*Fintype.card (Fin n))⌉₊+4*(Z w).card+10≤
           Fintype.card {x // x∈(data w).remaining}) ∧
      (∀w,((data w).remaining.card:ℝ)≤10*θ*n) ∧
      (let occupied:=fun w=>((data w).oldDomain\bufferedPathStrictInterior (fun _=>(m+1)*d) (inner w)).image (ψ w)
       let Z:=innerRequiredTargets H A (rawReservedSpokeList π d (fun e=>raw (Sum.inr e)))
         (retainedFinalMarkedAt π d (fun e=>raw (Sum.inr e)) t Jret) absorber occupied
       ∀v,((Finset.univ.filter (fun w=>v∈(residualSubtypeSet (data w).remaining (data w).prescribed).image (fun x=>ψ w x.1))).card:ℝ)+
         (Kbad Pack).degree v+((Finset.univ.filter (fun w=>v∈Z w)).card:ℝ)≤δglobal*n) ∧
      (let occupied:=fun w=>((data w).oldDomain\bufferedPathStrictInterior (fun _=>(m+1)*d) (inner w)).image (ψ w)
       let Z:=innerRequiredTargets H A (fun w=>Finset.univ.filter (fun v=>retainedRawMarkedSpokes π d (fun e=>raw (Sum.inr e)) false t Jret false false false v w))
         (retainedFinalMarkedAt π d (fun e=>raw (Sum.inr e)) t Jret) absorber occupied
       let Interiors:=fun w=>bufferedPathStrictInterior (fun _=>(m+1)*d) (inner w)
       let Jbad:=spanningRestriction (Sclass\Used) A\(Kbad Pack)
       let Lbad:=protectedPairEdgeHubs (rawReservedSpokeList π d (fun e=>raw (Sum.inr e))) H
       let Bad:=fun v:Fin n=>Finset.univ.filter (fun w=>v∈retainedFinalMarkedAt π d (fun e=>raw (Sum.inr e)) t Jret w)
       let Dfree:=fun x y=>rawSelectedPhysicalRelation P π d (fun e=>σ (Sum.inl e)) x y ∧ ¬DelG.Adj x y
       let Dstar:=Dhost
       let Lists:=fun w=>rawReservedSpokeList π d (fun e=>raw (Sum.inr e)) w\
         (A∪retainedFinalMarkedAt π d (fun e=>raw (Sum.inr e)) t Jret w)
       let FinalEdges:=fun w=>Finset.univ.biUnion (fun i:{i // i∈(data w).s₁}=>((data w).path (.inl i)).edges.toFinset)
       FirstVortexResidualCompletionOrientedTracked F Dsrc _ _ data Interiors ψ (Kbad Pack) Jbad Lbad Bad Z Dfree Dstar Pack Lists FinalEdges δglobal ((ρ₀/4)/40000) ∧
       ∃(piecesNew:∀w,List (PrescribedSourcePiece {x // x∈(data w).remaining}))
        (Φ:∀w,{x // x∈(data w).remaining}→Fin n) (fC:∀w,{x // x∉Interiors w}↪Fin n),
        (∀w,prescribedDependentGraph piecesNew w=((data w).graph).induce (↑(data w).remaining:Set (Fin n))) ∧
        (∀w (x:{x // x∉Interiors w}),x.val∈(data w).oldDomain→fC w x=ψ w x.val) ∧
        (∀w (x:{x // x∈(data w).remaining}) (hx:x.val∉Interiors w),fC w ⟨x.val,hx⟩=Φ w x) ∧
        (∀w v,v∈Z w→∃x,Φ w x=v) ∧
        (∀v,((Finset.univ.filter (fun w=>v∈Finset.univ.image (Φ w))).card:ℝ)≤
          δglobal*Fintype.card (Fin n)+(Real.sqrt δglobal*Fintype.card (Fin n)+1)) ∧
        (∀w,Disjoint (outsideBufferedPathImage (fun _=>(m+1)*d) (inner w) (fC w))
          (markedIntervalRootSet π (fun _:retainedMarkedIndex π d (fun e=>raw (Sum.inr e)) false t Jret w=>d) Subtype.val)) ∧
        (∀w i (hp:inner w i 0∉Interiors w),fC w ⟨inner w i 0,hp⟩=i.val) ∧
        (∀w i (hp:inner w i (Fin.last ((m+1)*d))∉Interiors w),
          fC w ⟨inner w i (Fin.last ((m+1)*d)),hp⟩=(π^d) i.val) ∧
        (∀w,
          let Y:=markedIntervalRootSet π (fun _:retainedMarkedIndex π d (fun e=>raw (Sum.inr e)) false t Jret w=>d) Subtype.val
          let B:=Finset.univ.image (fun i:retainedMarkedIndex π d (fun e=>raw (Sum.inr e)) false t Jret w=>(π^d) i.val)
          let R:=Finset.univ\(outsideBufferedPathImage (fun _=>(m+1)*d) (inner w) (fC w) ∪ B)
          Y⊆R ∧ R.card=(m+1)*Y.card ∧ Disjoint (R\Y) (Y.image π)) ∧
        (∀w,((Finset.univ\bufferedPathFullDomain (fun _=>(m+1)*d) (inner w))∪
          bufferedFinalEndpoints (fun _=>(m+1)*d) (inner w)).image (factorCycleOrientation (F w) (E w)) =
          (Finset.univ\bufferedPathFullDomain (fun _=>(m+1)*d) (inner w))∪Finset.univ.image (fun i=>inner w i 0)) ∧
        (∀w∈H,A⊆(Finset.univ.filter (fun v=>retainedRawMarkedSpokes π d (fun e=>raw (Sum.inr e)) false t Jret false false false v w)) ∪
          retainedFinalMarkedAt π d (fun e=>raw (Sum.inr e)) t Jret w ∪ absorber w ∪ Finset.univ.image (fC w)) ∧
        (∀w x y,(F w).Adj x.1 y.1→Dsrc w x.1 y.1→Dhost (fC w x) (fC w y)) ∧
        (∀w x y,(F w).Adj x.1 y.1→P.Adj (fC w x) (fC w y)) ∧
        (∀w z,w≠z→Disjoint
          (((F w).induce {x | x∉Interiors w}).edgeFinset.image (Sym2.map (fC w)))
          (((F z).induce {x | x∉Interiors z}).edgeFinset.image (Sym2.map (fC z)))) ∧
        (∀w∈H,∀v∈A,
          let Y:=markedIntervalRootSet π (fun _:retainedMarkedIndex π d (fun e=>raw (Sum.inr e)) false t Jret w=>d) Subtype.val
          let End:=Finset.univ.image (fun i:retainedMarkedIndex π d (fun e=>raw (Sum.inr e)) false t Jret w=>(π^d) i.val)
          let R:=Finset.univ\(outsideBufferedPathImage (fun _=>(m+1)*d) (inner w) (fC w)∪End);
          (v∈R\Y↔retainedRawMarkedSpokes π d (fun e=>raw (Sum.inr e)) false t Jret false false false v w)) ∧
        (∃(assignNew:Sym2 (Fin n)→U) (orient:Sym2 (Fin n)→Fin n×Fin n)
          (BB:∀w,Finset {x // x∈(data w).remaining}) (g:∀w,{x // x∈(data w).remaining}→Fin n),
          (∀w,(prescribedAssignedArcs (Kbad Pack) assignNew orient w).card≤⌈4*((Kbad Pack).edgeFinset.card:ℝ)/(((ρ₀/4)/40000)*Fintype.card (Fin n))⌉₊) ∧
          (∀w,(BB w).image (g w)=(residualSubtypeSet (data w).remaining (data w).prescribed).image (fun x=>ψ w x.1)∪
            prescribedMatchingEndpoints (prescribedAssignedArcs (Kbad Pack) assignNew orient w)∪Z w) ∧
          (∀w v,v∈prescribedMatchingEndpoints (prescribedAssignedArcs (Kbad Pack) assignNew orient w)→
            ∃e∈(Kbad Pack).edgeFinset,v∈e.toFinset ∧ w∈Lbad e) ∧
          (∀w x,x∈BB w→Φ w x=g w x) ∧
          (∀w x,x∉BB w→Φ w x∈Lists w)) ∧
        (∀w,(((Finset.univ.image (Φ w))∩A).card)≤
          (residualSubtypeSet (data w).remaining (data w).prescribed).card+
            2*⌈4*((Kbad Pack).edgeFinset.card:ℝ)/(((ρ₀/4)/40000)*Fintype.card (Fin n))⌉₊+(Z w).card) ∧
        (∃ (hinnerA:∀w i p,inner w i p=ext w (.inl i) ⟨p.val+2,by omega⟩)
          (hdisA:∀w i j,i≠j→Disjoint (Finset.univ.image (fun p=>ext w (.inl i) p))
            (Finset.univ.image (fun p=>ext w (.inl j) p)))
          (hσ:∀w,(complementTailDomain (bufferedPathFullDomain (fun _=>(m+1)*d) (inner w))
            (bufferedFinalEndpoints (fun _=>(m+1)*d) (inner w))).image (factorCycleOrientation (F w) (E w))=
            complementTailDomain (bufferedPathFullDomain (fun _=>(m+1)*d) (inner w))
              (bufferedInitialEndpoints (fun _=>(m+1)*d) (inner w))),
          let tail:=fun w=>bufferedOrientedTailEmbedding (fun _=>(m+1)*d) (fun i=>ext w (.inl i))
            (inner w) (hinnerA w) (hdisA w) (fC w)
          let head:=fun w=>bufferedOrientedHeadEmbedding (fun _=>(m+1)*d) (fun i=>ext w (.inl i))
            (inner w) (hinnerA w) (hdisA w) (factorCycleOrientation (F w) (E w)) (hσ w) (fC w)
          let Q:=orientationMatrixArcs Mhost\Finset.univ.biUnion (fun w=>Finset.univ.image (fun x=>(tail w x,head w x)))
          ∀v,(Q.filter (fun e=>e.1=v)).card=
            (Finset.univ.filter (fun w=>v∉outsideBufferedPathImage (fun _=>(m+1)*d) (inner w) (fC w) ∪
              Finset.univ.image (fun j:retainedMarkedIndex π d (fun e=>raw (Sum.inr e)) false t Jret w=>(π^d) j.val))).card ∧
            (Q.filter (fun e=>e.2=v)).card=
            (Finset.univ.filter (fun w=>v∉outsideBufferedPathImage (fun _=>(m+1)*d) (inner w) (fC w) ∪
              Finset.univ.image (fun j:retainedMarkedIndex π d (fun e=>raw (Sum.inr e)) false t Jret w=>(π^d) j.val))).card) ∧
        let Enew:U→Finset (Sym2 (Fin n)):=fun w=>((prescribedDependentGraph piecesNew w).edgeFinset).image (Sym2.map (Φ w));
        (Kbad Pack).edgeFinset⊆Finset.univ.biUnion Enew ∧
        (∀w,Disjoint (Enew w) Jbad.edgeFinset) ∧ (∀w,Disjoint (Enew w) Pack) ∧
        (prescribedPhysicalUnion Enew).edgeFinset=Finset.univ.biUnion Enew ∧
        (∀v,((prescribedPhysicalUnion Enew).degree v:ℝ)≤5*Real.sqrt δglobal*Fintype.card (Fin n)) ∧
        (∀x y,(SimpleGraph.fromEdgeSet (↑Pack:Set (Sym2 (Fin n)))⊔prescribedPhysicalUnion Enew).Adj x y→¬Reserve.Adj x y))
end Oberwolfach

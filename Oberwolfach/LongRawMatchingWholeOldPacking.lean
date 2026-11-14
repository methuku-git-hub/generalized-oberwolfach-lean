module

public import Oberwolfach.ActualOldSymmetricPhysicalCover
public import Oberwolfach.LongRawMatchingOldSymmetricPacking

@[expose] public section
/-! Assemble the physical old-edge covers at all hubs into the packing
hypotheses of the residual-degree theorem, using the same mixed matching. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance longRawWholeOldPackingDecEqFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem long_raw_matching_whole_old_packing
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    {X A B I:U→Type} [∀w,Fintype (X w)] [∀w,DecidableEq (X w)]
    [∀w,DecidableEq (A w)] [∀w,DecidableEq (B w)] [∀w,Fintype (I w)]
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d m:ℕ) (ℓ:Fin K→ℕ)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (g j:Bool)
    (G:∀w,SimpleGraph (X w))
    (data:∀w,ActualResidualData (K:=A w) (J:=B w) (G w))
    (E:∀w (C:(G w).ConnectedComponent),SimpleGraph.cycleGraph (Fintype.card C) ≃g C.toSimpleGraph)
    (pieces:∀w,List (PrescribedSourcePiece (X w))) (D:∀w,X w→X w→Prop)
    (hpair:∀w,(pieces w).Pairwise (fun p q=>Disjoint p.vertices.toFinset q.vertices.toFinset))
    (hvalid:∀w p,p∈pieces w→p.OriginalValid (D w))
    (hEdges:∀w,sourcePieceEdgesUnion (pieces w)=(G w).edgeFinset)
    (hArcs:∀w x y,D w x y↔(x,y)∈sourcePieceArcsUnion (pieces w))
    (halign:∀w x,D w x (factorCycleOrientation (G w) (E w) x))
    (ψ:∀w,X w→Fin n)
    (b:∀w,I w≃{i // i∈(data w).s₁})
    (ext:∀w (i:I w),Fin ((data w).c*(data w).d+5)↪X w)
    (inner:∀w (i:I w),Fin ((data w).c*(data w).d+1)↪X w)
    (hinner:∀w i k,inner w i k=ext w i ⟨k.val+2,by omega⟩)
    (hsupp:∀w i,((data w).P (b w i).val).support=List.ofFn (ext w i))
    (p:∀w (i:I w),(G w).Walk (inner w i 0) (inner w i (Fin.last ((data w).c*(data w).d))))
    (hp:∀w i,(p w i).support=List.ofFn (inner w i)):
    let state:=longRawHubState P π d raw g j
    let e:{z // z∈bernoulliVertexSet state}↪_:=Function.Embedding.subtype _
    let R:=longRawSeedResources (U:=U) π d m ℓ
    ∀M:Finset (RestrictedResource (mixedCandidateResources R) e),
    (∀c∈M,∀c'∈M,c≠c'→Disjoint (restrictedResourceSet (mixedCandidateResources R) e c)
      (restrictedResourceSet (mixedCandidateResources R) e c'))→
    (∀w,ActualOldArcContainment (data w) (ψ w) (E w)
      (fun x y=>({x,y}:Finset (Fin n))∈longRawPhysicalHubRims P π d m ℓ raw g j M w))→
    let old:=fun w=>((data w).deletedEdges\(Finset.univ.biUnion (fun i:I w=>(p w i).edges.toFinset))).image (Sym2.map (ψ w))
    ∃Pack:Finset (Sym2 (Fin n)),
      (∀w z,w≠z→Disjoint (old w) (old z)) ∧ (∀w,old w⊆Pack):=by
  intro state e R M hmatch hold old
  have hcover:∀w e,e∈old w→e.toFinset∈longRawPhysicalHubRims P π d m ℓ raw g j M w:=by
    intro w
    exact actual_old_symmetric_edges_physically_covered (G w) (data w) (E w) (pieces w) (D w)
      (hpair w) (hvalid w) (hEdges w) (hArcs w) (halign w) (ψ w)
      (longRawPhysicalHubRims P π d m ℓ raw g j M w) (hold w) (b w) (ext w) (inner w)
      (hinner w) (hsupp w) (p w) (hp w)
  exact long_raw_matching_packs_old_symmetric_edges P π d m ℓ raw g j M hmatch old hcover
end Oberwolfach

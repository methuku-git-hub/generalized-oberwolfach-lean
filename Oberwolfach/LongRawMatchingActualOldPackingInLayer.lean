module

public import Oberwolfach.LongRawHubRimsInApproximate
public import Oberwolfach.LongRawMatchingOldSymmetricPacking
public import Oberwolfach.ActualOldArcContainment
public import Oberwolfach.ActualSourceOrientationProperties

@[expose] public section
/-! The matching packs the actual old edges simultaneously, including when
the residual-index types differ from hub to hub. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 24000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance longRawActualOldPackingLayerDecEqFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem long_raw_matching_actual_old_packing_in_approximate_layer
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    {X A B:U→Type} [∀w,Fintype (X w)] [∀w,DecidableEq (X w)]
    [∀w,DecidableEq (A w)] [∀w,DecidableEq (B w)]
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d m:ℕ) (ℓ:Fin K→ℕ)
    (σ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e) (g j:Bool)
    (G:∀w,SimpleGraph (X w)) (data:∀w,ActualResidualData (K:=A w) (J:=B w) (G w))
    (E:∀w (C:(G w).ConnectedComponent),SimpleGraph.cycleGraph (Fintype.card C) ≃g C.toSimpleGraph)
    (pieces:∀w,List (PrescribedSourcePiece (X w))) (D:∀w,X w→X w→Prop)
    (hpair:∀w,(pieces w).Pairwise (fun p q=>Disjoint p.vertices.toFinset q.vertices.toFinset))
    (hvalid:∀w p,p∈pieces w→p.OriginalValid (D w))
    (hEdges:∀w,sourcePieceEdgesUnion (pieces w)=(G w).edgeFinset)
    (hArcs:∀w x y,D w x y↔(x,y)∈sourcePieceArcsUnion (pieces w))
    (halign:∀w x,D w x (factorCycleOrientation (G w) (E w) x))
    (ψ:∀w,X w→Fin n):
    let raw:RawMarkedOutcome (Fin n) U Bool Bool:=fun e=>rawExpandedApproximateCollapse e (σ e)
    let state:=longRawHubState P π d raw g j
    let e:{z // z∈bernoulliVertexSet state}↪_:=Function.Embedding.subtype _
    let R:=longRawSeedResources (U:=U) π d m ℓ
    ∀M:Finset (RestrictedResource (mixedCandidateResources R) e),
    (∀c∈M,∀c'∈M,c≠c'→Disjoint (restrictedResourceSet (mixedCandidateResources R) e c)
      (restrictedResourceSet (mixedCandidateResources R) e c'))→
    (∀w,ActualOldArcContainment (data w) (ψ w) (E w)
      (fun x y=>({x,y}:Finset (Fin n))∈longRawPhysicalHubRims P π d m ℓ raw g j M w))→
    let old:=fun w=>((data w).deletedEdges\(Finset.univ.biUnion
      (fun i:{i // i∈(data w).s₁}=>((data w).path (.inl i)).edges.toFinset))).image (Sym2.map (ψ w))
    ∃Pack:Finset (Sym2 (Fin n)),
      (∀w z,w≠z→Disjoint (old w) (old z)) ∧ (∀w,old w⊆Pack) ∧
        Pack⊆(longApproximatePhysicalGraph P π d σ).edgeFinset:=by
  intro raw state e R M hmatch hold old
  have hcover:∀w e,e∈old w→e.toFinset∈longRawPhysicalHubRims P π d m ℓ raw g j M w:=by
    intro w
    have horient:∀x y,(G w).Adj x y→D w x y ∨ D w y x:=
      (actual_source_orientation_covers_and_has_unique_incoming (G w) (pieces w) (D w)
        (hpair w) (hvalid w) (hEdges w) (hArcs w)).1
    apply physical_cover_gives_symmetric_old_edge_cover (data w) _ (ψ w) (D w) horient
      (longRawPhysicalHubRims P π d m ℓ raw g j M w)
    exact hold w (pieces w) (D w) (hpair w) (hvalid w) (hArcs w) (halign w)
  obtain ⟨_,hdis,_⟩:=long_raw_matching_packs_old_symmetric_edges P π d m ℓ raw g j M hmatch old hcover
  let Pack:=Finset.univ.filter (fun a:Sym2 (Fin n)=>a.toFinset∈
    Finset.univ.biUnion (longRawPhysicalHubRims P π d m ℓ raw g j M))
  refine ⟨Pack,hdis,?_,?_⟩
  · intro w a ha
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,Finset.mem_biUnion.mpr ⟨w,Finset.mem_univ _,hcover w a ha⟩⟩
  · exact long_raw_hub_rim_union_pack_in_approximate_graph P π d m ℓ σ g j M
end Oberwolfach

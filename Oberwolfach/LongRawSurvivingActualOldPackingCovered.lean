module

public import Oberwolfach.LongRawSurvivingMatchingLift
public import Oberwolfach.LongRawActualOldPackingCovered

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 24000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance longRawSurvivingOldPackingCoveredDecEqFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem long_raw_surviving_matching_actual_old_packing_in_covered_graph
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    {X A B:U→Type} [∀w,Fintype (X w)] [∀w,DecidableEq (X w)]
    [∀w,DecidableEq (A w)] [∀w,DecidableEq (B w)]
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d m:ℕ) (ℓ:Fin K→ℕ)
    (σ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e) (g j:Bool) (Del:Finset (Sym2 (Fin n)))
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
    let T:=bernoulliVertexSet (longRawHubState P π d raw g j)
    let S:=longRawSurvivingResources P π d raw g j Del
    let e:{z // z∈T}↪_:=Function.Embedding.subtype _
    let eS:{z // z∈S}↪_:=Function.Embedding.subtype _
    let R:=longRawSeedResources (U:=U) π d m ℓ
    let q:=survivingCandidateEmbedding (mixedCandidateResources R) S T (long_raw_surviving_resources_subset P π d raw g j Del)
    ∀M:Finset (RestrictedResource (mixedCandidateResources R) eS),
    (∀c∈M,∀c'∈M,c≠c'→Disjoint (restrictedResourceSet (mixedCandidateResources R) eS c)
      (restrictedResourceSet (mixedCandidateResources R) eS c'))→
    (∀w,ActualOldArcContainment (data w) (ψ w) (E w)
      (fun x y=>({x,y}:Finset (Fin n))∈longRawPhysicalHubRims P π d m ℓ raw g j (M.map q) w))→
    let old:=fun w=>((data w).deletedEdges\(Finset.univ.biUnion
      (fun i:{i // i∈(data w).s₁}=>((data w).path (.inl i)).edges.toFinset))).image (Sym2.map (ψ w))
    ∃Pack:Finset (Sym2 (Fin n)),
      (∀w z,w≠z→Disjoint (old w) (old z)) ∧ (∀w,old w⊆Pack) ∧
        Pack⊆(longApproximatePhysicalGraph P π d σ).edgeFinset ∧
        Pack⊆(physicalRimCandidateUnion (markedRawSampledPhysicalEmbedding P π d raw g j)
          (restrictedResourceSet (mixedCandidateResources R) e) (M.map q)).edgeFinset:=by
  intro raw T S e eS R q M hmatch hold old
  have hdec : longRawSurvivingOldPackingCoveredDecEqFin n = instDecidableEqFin n := Subsingleton.elim _ _
  have hmatch' := hmatch
  rw [hdec] at hmatch'
  have hlift' := (long_raw_surviving_matching_lift P π d m ℓ raw g j Del M hmatch').1
  rw [← hdec] at hlift'
  have hlift:∀c∈M.map q,∀c'∈M.map q,c≠c'→Disjoint
      (restrictedResourceSet (mixedCandidateResources R) e c)
      (restrictedResourceSet (mixedCandidateResources R) e c'):=
    hlift' 
  exact long_raw_matching_actual_old_packing_in_covered_graph P π d m ℓ σ g j G data E pieces D hpair hvalid hEdges hArcs halign ψ (M.map q) hlift hold
end Oberwolfach

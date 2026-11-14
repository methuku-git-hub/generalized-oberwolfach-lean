module

public import Oberwolfach.ResidualCycleFamilyPieces
public import Oberwolfach.FactorDirectedCyclePieces
public import Oberwolfach.FactorPieceGraphIdentity

@[expose] public section
/-! Construct a directed-cycle source list from an actual two-factor. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V]

theorem two_factor_directed_source_cycles (F:SimpleGraph V) (hF:F.IsRegularOfDegree 2):
    ∃ (D:V→V→Prop) (orig:List (PrescribedSourcePiece V)),
      orig.Pairwise (fun p q=>Disjoint p.vertices.toFinset q.vertices.toFinset) ∧
      (∀p∈orig,∃a xs,p=.cycle a xs ∧ p.OriginalValid D) ∧
      sourcePieceVerticesUnion orig=Finset.univ ∧ sourcePieceEdgesUnion orig=F.edgeFinset ∧
      ∀x y,D x y→F.Adj x y := by
  obtain ⟨root,tail,D,hvalid,hverts,hdisj,hcover,hsub,hedges⟩:=two_factor_components_as_directed_pieces F hF
  letI : Fintype F.ConnectedComponent := Fintype.ofFinite _
  let orig:List (PrescribedSourcePiece V):=Finset.univ.toList.map (fun c=>.cycle (root c) (tail c))
  refine ⟨D,orig,?_,?_,?_,?_,hsub⟩
  · dsimp [orig]
    rw [List.pairwise_map]
    apply List.Pairwise.imp ?_ (Finset.nodup_toList Finset.univ)
    intro c c' hne
    apply Finset.disjoint_left.mpr
    intro x hx hx'
    have hxc:x∈root c::tail c := by simpa [PrescribedSourcePiece.vertices] using hx
    have hxc':x∈root c'::tail c' := by simpa [PrescribedSourcePiece.vertices] using hx'
    exact hne (hdisj c c' x hxc hxc')
  · intro p hp
    obtain ⟨c,_,rfl⟩:=List.mem_map.mp hp
    have hh:=hvalid c
    refine ⟨root c,tail c,rfl,hh.1,hh.2.1,?_⟩
    have hc':= (directed_cycle_through_iff_chain D ⊥ (root c) (tail c)).1 hh.2.2
    simpa using hc'
  · ext x
    simp only [Finset.mem_univ,iff_true]
    obtain ⟨c,hc⟩:=hcover x
    exact Finset.mem_biUnion.mpr ⟨.cycle (root c) (tail c),
      List.mem_toFinset.mpr (List.mem_map.mpr ⟨c,by simp,rfl⟩),by simpa [PrescribedSourcePiece.vertices] using hc⟩
  · ext e
    induction e using Sym2.ind with
    | _ x y =>
      simp only [sourcePieceEdgesUnion,Finset.mem_biUnion,List.mem_toFinset,SimpleGraph.mem_edgeFinset,
        SimpleGraph.mem_edgeSet]
      constructor
      · rintro ⟨p,hp,he⟩
        obtain ⟨c,_,rfl⟩:=List.mem_map.mp hp
        have hx: x∈root c::tail c := (source_piece_physical_edge_endpoints (.cycle (root c) (tail c)) x y he).1
        exact (hedges x y).2 ⟨c,hx,he⟩
      · intro he
        obtain ⟨c,hx,he⟩:=(hedges x y).1 he
        exact ⟨.cycle (root c) (tail c),List.mem_map.mpr ⟨c,by simp,rfl⟩,he⟩
end Oberwolfach

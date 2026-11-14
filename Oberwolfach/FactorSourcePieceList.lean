module

public import Oberwolfach.FactorDirectedCyclePieces
public import Oberwolfach.PrescribedPieceShape

@[expose] public section
/-! Present a two-factor by a finite list of vertex-disjoint source pieces. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V]

theorem two_factor_source_piece_list (F:SimpleGraph V)
    (hF:F.IsRegularOfDegree 2):
    ∃ (pieces:List (PrescribedSourcePiece V)),
      (∀ p∈pieces,p.Shape) ∧
      pieces.Pairwise (fun p q=>Disjoint p.vertices.toFinset q.vertices.toFinset) ∧
      (∀ x,∃ p∈pieces,x∈p.vertices) ∧
      (∀ x y,F.Adj x y ↔ ∃ p∈pieces,x∈p.vertices ∧ s(x,y)∈p.edges) := by
  obtain ⟨root,tail,D,hvalid,hverts,hdisj,hcover,hsub,hedges⟩:=two_factor_components_as_directed_pieces F hF
  letI : Fintype F.ConnectedComponent := Fintype.ofFinite _
  let pieces:List (PrescribedSourcePiece V):=Finset.univ.toList.map (fun c=>.cycle (root c) (tail c))
  refine ⟨pieces,?_,?_,?_,?_⟩
  · intro p hp
    obtain ⟨c,_,rfl⟩:=List.mem_map.mp hp
    have h:=hvalid c
    change (root c::tail c).Nodup ∧ 3≤(root c::tail c).length
    exact ⟨h.1,h.2.1⟩
  · dsimp [pieces]
    rw [List.pairwise_map]
    apply List.Pairwise.imp ?_ (Finset.nodup_toList Finset.univ)
    intro c c' hne
    apply Finset.disjoint_left.mpr
    intro x hx hx'
    have hxc : x∈root c::tail c := by simpa [PrescribedSourcePiece.vertices] using hx
    have hxc' : x∈root c'::tail c' := by simpa [PrescribedSourcePiece.vertices] using hx'
    exact hne (hdisj c c' x hxc hxc')
  · intro x
    obtain ⟨c,hc⟩:=hcover x
    refine ⟨.cycle (root c) (tail c),?_,?_⟩
    · exact List.mem_map.mpr ⟨c,by simp,rfl⟩
    · exact hc
  · intro x y
    rw [hedges x y]
    constructor
    · rintro ⟨c,hx,he⟩
      exact ⟨.cycle (root c) (tail c),List.mem_map.mpr ⟨c,by simp,rfl⟩,hx,he⟩
    · rintro ⟨p,hp,hx,he⟩
      obtain ⟨c,_,rfl⟩:=List.mem_map.mp hp
      exact ⟨c,hx,he⟩
end Oberwolfach

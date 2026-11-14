module

public import Oberwolfach.ResidualPieceSubtypeLift

@[expose] public section
/-! Lifting a source piece preserves its shape and its directed order. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V]

theorem subtype_piece_validity_reflected (R:Finset V)
    (q:PrescribedSourcePiece {x // x∈R}) (D:V→V→Prop)
    (h:(q.map Subtype.val).OriginalValid D):
    q.Shape ∧ q.OriginalValid (fun x y=>D x.1 y.1) := by
  cases q with
  | path xs =>
    have hn:xs.Nodup := List.Nodup.of_map Subtype.val h.1
    have hc:List.IsChain (fun x y=>D x.1 y.1) xs := (List.isChain_map Subtype.val).1 h.2
    exact ⟨hn,hn,hc⟩
  | cycle a xs =>
    have hn:(a::xs).Nodup := by
      apply List.Nodup.of_map Subtype.val
      simpa [PrescribedSourcePiece.map,PrescribedSourcePiece.OriginalValid] using h.1
    have hl:3≤(a::xs).length := by
      simpa [PrescribedSourcePiece.map,PrescribedSourcePiece.OriginalValid] using h.2.1
    have hc:List.IsChain (fun x y=>D x.1 y.1) ((a::xs)++[a]) := by
      apply (List.isChain_map Subtype.val).1
      simpa [PrescribedSourcePiece.map,PrescribedSourcePiece.OriginalValid,List.map_append] using h.2.2
    exact ⟨⟨hn,hl⟩,hn,hl,hc⟩
end Oberwolfach

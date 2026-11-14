module

public import Oberwolfach.ResidualPieceSubtypeValidity

@[expose] public section
/-! Lift every piece simultaneously to the surviving vertex subtype. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V]

theorem source_piece_list_lift_to_vertex_subtype (R:Finset V):
    ∀ ps:List (PrescribedSourcePiece V),
      (∀p∈ps,p.vertices.toFinset⊆R)→
      ∃ qs:List (PrescribedSourcePiece {x // x∈R}),
        qs.map (fun q=>q.map Subtype.val)=ps := by
  intro ps
  induction ps with
  | nil => intro _;exact ⟨[],rfl⟩
  | cons p ps ih =>
    intro hR
    have hp:p.vertices.toFinset⊆R:=hR p (by simp)
    have htail:∀q∈ps,q.vertices.toFinset⊆R:=by
      intro q hq;exact hR q (by simp [hq])
    obtain ⟨q,hq⟩:=source_piece_lift_to_vertex_subtype R p hp
    obtain ⟨qs,hqs⟩:=ih htail
    exact ⟨q::qs,by simp [hq,hqs]⟩
end Oberwolfach

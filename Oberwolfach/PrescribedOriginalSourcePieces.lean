module

public import Oberwolfach.PrescribedSourcePieces
public import Oberwolfach.PrescribedPathScheduleChain

@[expose] public section
/-! Explicit source paths and cycles require only their original directed
order, with no additional forbidden-source graph. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {X:Type} [Fintype X] [DecidableEq X]

def PrescribedSourcePiece.OriginalValid (p:PrescribedSourcePiece X) (D:X→X→Prop):Prop:=
  match p with
  | .path xs=>xs.Nodup ∧ List.IsChain D xs
  | .cycle a xs=>(a::xs).Nodup ∧ 3≤(a::xs).length ∧ List.IsChain D ((a::xs)++[a])

theorem prescribed_original_piece_valid (p:PrescribedSourcePiece X) (D:X→X→Prop)
    (hp:p.OriginalValid D):p.Valid D ⊥ := by
  cases p with
  | path xs =>
    refine ⟨hp.1,?_⟩
    simpa using hp.2
  | cycle a xs =>
    refine ⟨hp.1,hp.2.1,?_⟩
    have hc:List.IsChain (fun x y=>D x y ∧ ¬(⊥:SimpleGraph X).Adj x y) ((a::xs)++[a]):=by
      simpa using hp.2.2
    exact (prescribed_path_through_chain D ⊥ xs a a).mpr hc
end Oberwolfach

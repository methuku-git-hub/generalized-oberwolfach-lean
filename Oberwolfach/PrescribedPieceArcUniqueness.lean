module

public import Oberwolfach.PrescribedSourcePieces
public import Oberwolfach.PrescribedPathArcUniqueness

@[expose] public section
/-! In each ordered path or cycle, every vertex has at most one predecessor
and at most one successor. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {X:Type} [DecidableEq X]

theorem prescribed_piece_unique_successor (p:PrescribedSourcePiece X) (D:X→X→Prop) (F:SimpleGraph X)
    (hp:p.Valid D F) (x y z:X) (hy:(x,y)∈p.arcs) (hz:(x,z)∈p.arcs):y=z := by
  cases p with
  | path xs =>
    apply prescribed_path_unique_successor xs _ x y z hy hz
    exact hp.1.sublist (List.dropLast_sublist xs)
  | cycle a xs =>
    apply prescribed_path_unique_successor ((a::xs)++[a]) _ x y z hy hz
    change ((a::xs)++[a]).dropLast.Nodup
    rw [List.dropLast_concat]
    exact hp.1

theorem prescribed_piece_unique_predecessor (p:PrescribedSourcePiece X) (D:X→X→Prop) (F:SimpleGraph X)
    (hp:p.Valid D F) (x y z:X) (hy:(y,x)∈p.arcs) (hz:(z,x)∈p.arcs):y=z := by
  cases p with
  | path xs =>
    apply prescribed_path_unique_predecessor xs _ x y z hy hz
    exact hp.1.sublist (List.tail_sublist xs)
  | cycle a xs =>
    apply prescribed_path_unique_predecessor ((a::xs)++[a]) _ x y z hy hz
    have hax:a∉xs:=(List.nodup_cons.mp hp.1).1
    have hxs:xs.Nodup:=(List.nodup_cons.mp hp.1).2
    have htail:(xs++[a]).Nodup:=by
      apply List.nodup_append'.mpr
      refine ⟨hxs,by simp,?_⟩
      apply List.disjoint_left.mpr
      intro x hx hy
      simp only [List.mem_singleton] at hy
      subst x;exact hax hx
    simpa [List.cons_append] using htail
end Oberwolfach

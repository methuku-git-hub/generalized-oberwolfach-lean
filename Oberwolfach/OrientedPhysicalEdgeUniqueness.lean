module

public import Oberwolfach.Definitions

@[expose] public section
/-! In an oriented graph an underlying physical edge determines its arc. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem oriented_physical_edge_unique {V:Type} [DecidableEq V] (D:V→V→Prop)
    (horient:∀ a b,D a b→¬D b a) (x y z w:V)
    (hxy:D x y) (hzw:D z w) (hphys:({x,y}:Finset V)={z,w}):
    x=z ∧ y=w := by
  have hx:x=z ∨ x=w:=by
    have hh:x∈({z,w}:Finset V):=by rw [←hphys];simp
    simpa using hh
  have hy:y=z ∨ y=w:=by
    have hh:y∈({z,w}:Finset V):=by rw [←hphys];simp
    simpa using hh
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · subst z;subst y;exact False.elim (horient x x hxy hxy)
  · exact ⟨hx,hy⟩
  · subst w;subst z;exact False.elim (horient x y hxy hzw)
  · subst w;subst y;exact False.elim (horient x x hxy hxy)
end Oberwolfach

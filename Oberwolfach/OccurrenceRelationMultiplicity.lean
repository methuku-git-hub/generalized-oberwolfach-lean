module

public import Oberwolfach.TypedMatrixRealization

@[expose] public section

/-! A simple directed occurrence host is identified with its endpoint
relation, without changing the occurrence identifiers. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem occurrenceMultiplicity_eq_relation {V E:Type} [Fintype E] [DecidableEq V]
    (tail head:E→V) (hinj:Function.Injective (fun e=>(tail e,head e))):
    occurrenceMultiplicity tail head=relationMultiplicity (fun x y=>∃ e,tail e=x∧head e=y):=by
  funext x y
  by_cases h:∃ e,tail e=x∧head e=y
  · obtain ⟨e,rfl,rfl⟩:=h
    rw [occurrenceMultiplicity_at_edge tail head hinj]
    simp only [relationMultiplicity,show ∃ e',tail e'=tail e∧head e'=head e from ⟨e,rfl,rfl⟩,ite_true]
  · rw [occurrenceMultiplicity_zero tail head x y h]
    simp only [relationMultiplicity,h,ite_false]

theorem relationMultiplicity_delete_rectangle_le {V U:Type}
    (H:V→U→Prop) (A:Finset V) (B:Finset U) (v:V) (u:U):
    relationMultiplicity (fun x y=>H x y∧¬(x∈A∧y∈B)) v u≤relationMultiplicity H v u:=by
  by_cases hh:H v u <;> by_cases ha:v∈A <;> by_cases hb:u∈B <;>
    simp [relationMultiplicity,hh,ha,hb]

end Oberwolfach

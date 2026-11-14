module

public import Oberwolfach.ReservedSpokeMatchingListConstruction

@[expose] public section
/-! The physical vertex labels of the actually reserved ordinary spokes. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V I:Type} [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]

def actualReservedOrdinarySpokeLabels (C:Finset (Finset V⊕(V×I)))
    (Hold:Bool→V→I→Prop) (i:I):Finset V:=
  Finset.univ.filter (fun v=>Sum.inr (v,i)∈C ∧ Hold false v i)

theorem actual_reserved_ordinary_spoke_labels_mem
    (C:Finset (Finset V⊕(V×I))) (Hold:Bool→V→I→Prop) (i:I) (v:V):
    v∈actualReservedOrdinarySpokeLabels C Hold i ↔ Sum.inr (v,i)∈C ∧ Hold false v i :=by
  simp [actualReservedOrdinarySpokeLabels]

theorem actual_reserved_ordinary_spoke_labels_incidence
    (C:Finset (Finset V⊕(V×I))) (Hold:Bool→V→I→Prop) (v:V):
    ((Finset.univ:Finset I).filter (fun i=>v∈actualReservedOrdinarySpokeLabels C Hold i)).card≤C.card :=by
  let S:Finset I:=(Finset.univ:Finset I).filter (fun i=>v∈actualReservedOrdinarySpokeLabels C Hold i)
  have hinj:Function.Injective (fun i:I=>Sum.inr (α:=Finset V) (v,i)):=by
    intro i j h
    exact Prod.mk.inj (Sum.inr.inj h) |>.2
  have hsub:S.image (fun i=>Sum.inr (α:=Finset V) (v,i))⊆C:=by
    intro e he
    obtain ⟨i,hi,rfl⟩:=Finset.mem_image.mp he
    have hh:(Sum.inr (v,i))∈C∧Hold false v i:=
      (actual_reserved_ordinary_spoke_labels_mem C Hold i v).mp (Finset.mem_filter.mp hi).2
    exact hh.1
  rw [←Finset.card_image_of_injective S hinj]
  exact Finset.card_le_card hsub
end Oberwolfach

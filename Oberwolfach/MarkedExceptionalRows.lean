module

public import Oberwolfach.MarkedPaddingAssignments

@[expose] public section

/-! The padding indices are exactly the old rows with one incoming edge,
which is marked. The index count is bounded by the original rim count. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V A:Type} [Fintype V] [Fintype A] [DecidableEq V]

def ExceptionalMarkedRow (dst:A→V) (jr:A→Bool) (v:V):Prop:=
  Fintype.card {e:A // dst e=v}=1∧
    (Finset.univ.filter (fun e:{e:A // dst e=v}=>jr e.val=true)).card=1

theorem exceptional_marked_row_has_incoming (dst:A→V) (jr:A→Bool) (v:V)
    (hv:ExceptionalMarkedRow dst jr v):∃ e:A,dst e=v:=by
  obtain ⟨⟨e,he⟩⟩:=Fintype.card_pos_iff.mp (show 0<Fintype.card {e:A // dst e=v} by rw [hv.1];omega)
  exact ⟨e,he⟩

theorem exceptional_marked_rows_subset (dst:A→V) (jr:A→Bool) (R:Finset V)
    (hR:∀ e,dst e∈R):∀ v,ExceptionalMarkedRow dst jr v→v∈R:=by
  intro v hv
  obtain ⟨e,rfl⟩:=exceptional_marked_row_has_incoming dst jr v hv
  exact hR e

theorem exceptional_marked_rows_card (dst:A→V) (jr:A→Bool):
    Fintype.card {v:V // ExceptionalMarkedRow dst jr v}≤Fintype.card A:=by
  let f:{v:V // ExceptionalMarkedRow dst jr v}→A:=
    fun v=>Classical.choose (exceptional_marked_row_has_incoming dst jr v.val v.property)
  have hf:∀ v,dst (f v)=v.val:=fun v=>Classical.choose_spec (exceptional_marked_row_has_incoming dst jr v.val v.property)
  apply Fintype.card_le_of_injective f
  intro v w he
  exact Subtype.ext ((hf v).symm.trans ((congrArg dst he).trans (hf w)))

theorem padding_all_exceptional_rows (dst:A→V) (jr:A→Bool) (m:ℕ)
    (C:{v:V // ExceptionalMarkedRow dst jr v}→Fin (m+1)→V)
    (hC:∀ v,C v 0=v.val):
    ∀ v,¬(Fintype.card {e // paddingRimHead dst C e=v}=1∧
      (Finset.univ.filter (fun e:{e // paddingRimHead dst C e=v}=>paddingRimType jr m e.val=true)).card=1):=by
  apply padding_no_exceptional_row dst jr m C
  · intro v;rw [hC];exact v.property
  · intro v hd hk;exact ⟨⟨v,hd,hk⟩,hC ⟨v,hd,hk⟩⟩

end Oberwolfach

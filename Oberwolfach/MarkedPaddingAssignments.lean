module

public import Oberwolfach.MarkedPaddingDegrees

@[expose] public section

/-! Padding every exceptional row eliminates exactly the obstruction in
the Hall assignment. The statement permits coincident marked heads on the
image side, and does not assert injectivity of a row homomorphism. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V A S I:Type} [Fintype A] [Fintype S] [Fintype I] [DecidableEq V]

theorem padding_root_count_le (m:ℕ) (C:I→Fin (m+1)→V) (v:V):
    Fintype.card {i:I // C i 0=v}≤Fintype.card {z:I×Fin (m+1) // C z.1 z.2=v}:=by
  apply Fintype.card_le_of_injective (fun i=>⟨(i.val,0),i.property⟩)
  intro i j h
  apply Subtype.ext
  exact congrArg (fun z=>z.val.1) h

theorem padding_no_exceptional_row (dst:A→V) (jr:A→Bool) (m:ℕ) (C:I→Fin (m+1)→V)
    (hroots:∀ i,Fintype.card {e:A // dst e=C i 0}=1∧
      (Finset.univ.filter (fun e:{e:A // dst e=C i 0}=>jr e.val=true)).card=1)
    (hcover:∀ v,Fintype.card {e:A // dst e=v}=1→
      (Finset.univ.filter (fun e:{e:A // dst e=v}=>jr e.val=true)).card=1→∃ i,C i 0=v):
    ∀ v,¬(Fintype.card {e // paddingRimHead dst C e=v}=1∧
      (Finset.univ.filter (fun e:{e // paddingRimHead dst C e=v}=>paddingRimType jr m e.val=true)).card=1):=by
  intro v ⟨hd,hk⟩
  rw [finite_card_sum_predicate (fun e=>paddingRimHead dst C e=v)] at hd
  simp only [paddingRimHead,Sum.elim_inl,Sum.elim_inr,padding_cycle_incoming_count] at hd
  rw [finite_card_marked_fiber,
    finite_card_sum_predicate (fun e=>paddingRimHead dst C e=v∧paddingRimType jr m e=true)] at hk
  simp only [paddingRimHead,paddingRimType,Sum.elim_inl,Sum.elim_inr,padding_cycle_marked_incoming_count] at hk
  have hle:=padding_root_count_le m C v
  by_cases hz:Fintype.card {i:I // C i 0=v}=0
  · have hd':Fintype.card {e:A // dst e=v}=1:=by
      have hkm:Fintype.card {e:A // dst e=v∧jr e=true}≤Fintype.card {e:A // dst e=v}:=by
        apply Fintype.card_le_of_injective (fun e=>⟨e.val,e.property.1⟩)
        intro e f h
        exact Subtype.ext (congrArg (fun z:{e:A // dst e=v}=>z.val) h)
      omega
    have hk':(Finset.univ.filter (fun e:{e:A // dst e=v}=>jr e.val=true)).card=1:=by
      rw [finite_card_marked_fiber]
      omega
    obtain ⟨i,hi⟩:=hcover v hd' hk'
    have hp:0<Fintype.card {i:I // C i 0=v}:=Fintype.card_pos_iff.mpr ⟨⟨i,hi⟩⟩
    omega
  · have hp:0<Fintype.card {i:I // C i 0=v}:=Nat.pos_of_ne_zero hz
    obtain ⟨⟨i,hi⟩⟩:=Fintype.card_pos_iff.mp hp
    have hb:Fintype.card {e:A // dst e=v}=1:=by simpa only [hi] using (hroots i).1
    omega

theorem padding_constructed_row_assignments (src dst:A→V) (row:S→V) (jr:A→Bool) (js:S→Bool)
    (m:ℕ) (C:I→Fin (m+1)→V)
    (hbal:∀ v,Fintype.card {e:A // dst e=v}=Fintype.card {e:A // src e=v}∧
      Fintype.card {e:A // dst e=v}=Fintype.card {s:S // row s=v})
    (hmark:∀ v,(Finset.univ.filter (fun e:{e:A // dst e=v}=>jr e.val=true)).card=
      (Finset.univ.filter (fun s:{s:S // row s=v}=>js s.val=true)).card)
    (hroots:∀ i,Fintype.card {e:A // dst e=C i 0}=1∧
      (Finset.univ.filter (fun e:{e:A // dst e=C i 0}=>jr e.val=true)).card=1)
    (hcover:∀ v,Fintype.card {e:A // dst e=v}=1→
      (Finset.univ.filter (fun e:{e:A // dst e=v}=>jr e.val=true)).card=1→∃ i,C i 0=v):
    let s:=paddingRimTail src C
    let t:=paddingRimHead dst C
    let r:=paddingSpokeRow row C
    ∃ τ:∀ v,Equiv.Perm (DirectedIncidence s t v),
    ∃ a:∀ v,{e // t e=v}≃{e // r e=v},∃ d:∀ v,{e // s e=v}≃{e // r e=v},
      (∀ v i,τ v i≠i)∧
      (∀ v,∀ e:{e // t e=v},paddingSpokeType js m (a v e).val=
        markedIncidenceSpokeType (paddingRimType jr m) (τ v (Sum.inl e)))∧
      ∀ v,∀ e:{e // s e=v},markedIncidenceSpokeType (paddingRimType jr m) (τ v (Sum.inr e))=false:=by
  dsimp only
  obtain ⟨hb,hm⟩:=padding_row_balance src dst row jr js m C hbal hmark
  exact marked_row_assignment_types _ _ _ _ _ hb hm
    (padding_no_exceptional_row dst jr m C hroots hcover)

end Oberwolfach

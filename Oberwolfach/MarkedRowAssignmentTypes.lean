module

public import Oberwolfach.MarkedAttachmentAssignedTypes
public import Oberwolfach.MarkedRimIncidenceSpokes

@[expose] public section

/-! Apply the Hall assignment at every row with the exact rim/spoke degree
and marked-degree equalities. The permutation is in the attachment-to-hub
direction used by the actual vertex-wheel construction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 13000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V A S:Type} [Fintype A] [Fintype S] [DecidableEq V]

 theorem marked_row_assignment_types (src dst:A→V) (row:S→V) (jr:A→Bool) (js:S→Bool)
    (hbal:∀ v,Fintype.card {e:A // dst e=v}=Fintype.card {e:A // src e=v}∧
      Fintype.card {e:A // dst e=v}=Fintype.card {s:S // row s=v})
    (hmark:∀ v,(Finset.univ.filter (fun e:{e:A // dst e=v}=>jr e.val=true)).card=
      (Finset.univ.filter (fun s:{s:S // row s=v}=>js s.val=true)).card)
    (hpad:∀ v,¬(Fintype.card {e:A // dst e=v}=1∧
      (Finset.univ.filter (fun e:{e:A // dst e=v}=>jr e.val=true)).card=1)):
    ∃ τ:∀ v,Equiv.Perm (DirectedIncidence src dst v),
    ∃ a:∀ v,{e:A // dst e=v}≃{s:S // row s=v},
    ∃ d:∀ v,{e:A // src e=v}≃{s:S // row s=v},
      (∀ v i,τ v i≠i)∧
      (∀ v,∀ e:{e:A // dst e=v},js (a v e).val=markedIncidenceSpokeType jr (τ v (Sum.inl e)))∧
      ∀ v,∀ e:{e:A // src e=v},markedIncidenceSpokeType jr (τ v (Sum.inr e))=false:=by
  have hex:∀ v,∃ τ:Equiv.Perm (DirectedIncidence src dst v),
      ∃ a:{e:A // dst e=v}≃{s:S // row s=v},∃ d:{e:A // src e=v}≃{s:S // row s=v},
      (∀ i,τ i≠i)∧
      (∀ e:{e:A // dst e=v},js (a e).val=markedIncidenceSpokeType jr (τ (Sum.inl e)))∧
      ∀ e:{e:A // src e=v},markedIncidenceSpokeType jr (τ (Sum.inr e))=false:=by
    intro v
    let K:=Finset.univ.filter (fun e:{e:A // dst e=v}=>jr e.val=true)
    let SK:=Finset.univ.filter (fun s:{s:S // row s=v}=>js s.val=true)
    obtain ⟨τ,a,d,hτ,ha,hd⟩:=marked_attachment_assigned_types K SK (hbal v).1 (hbal v).2 (hmark v) (hpad v)
    have htype (z:DirectedIncidence src dst v):z∈K.image (Sum.inl (β:={e:A // src e=v}))↔
        markedIncidenceSpokeType jr z=true:=by
      cases z with
      | inl e=>simp [K,markedIncidenceSpokeType]
      | inr e=>simp [markedIncidenceSpokeType]
    refine ⟨τ,a,d,hτ,?_,?_⟩
    · intro e
      have hh:(js (a e).val=true)↔markedIncidenceSpokeType jr (τ (Sum.inl e))=true:=by
        have hh':js (a e).val=true↔τ (Sum.inl e)∈K.image (Sum.inl (β:={e:A // src e=v})):=by
          convert ha e using 1 <;> try simp only [SK,Finset.mem_filter,Finset.mem_univ,true_and]
          all_goals congr!
        exact hh'.trans (htype _)
      cases h₁:js (a e).val <;> cases h₂:markedIncidenceSpokeType jr (τ (Sum.inl e)) <;> simp_all
    · intro e
      have hh:markedIncidenceSpokeType jr (τ (Sum.inr e))≠true:=by
        intro h
        apply hd e
        convert (htype (τ (Sum.inr e))).mpr h using 1 <;> congr!
      exact Bool.eq_false_iff.mpr hh
  choose τ a d h using hex
  exact ⟨τ,a,d,fun v=>(h v).1,fun v=>(h v).2.1,fun v=>(h v).2.2⟩

end Oberwolfach

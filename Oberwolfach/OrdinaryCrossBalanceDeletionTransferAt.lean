module

public import Oberwolfach.OrdinaryDeletedHostBalanceRefinedAt
public import Oberwolfach.OrdinaryCrossBalanceFromChanges

@[expose] public section
/-! Cross-balance of the actual remainder can be charged to cross-balance of
the deleted pair, rather than to its total number of edits. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_cross_balance_deletion_transfer_at
    (Q R:SimpleGraph V) (H E:V→U→Prop) (I:Finset V) (J:Finset U) (v:V) (b c:ℝ)
    (hRQ:R≤Q) (hEH:∀v u,E v u→H v u)
    (hparent:|((Q.neighborFinset v∩I).card:ℝ)-2*(J.filter (H v)).card|≤b)
    (hdel:|((R.neighborFinset v∩I).card:ℝ)-2*(J.filter (E v)).card|≤c):
    |(((Q\R).neighborFinset v∩I).card:ℝ)-
      2*(J.filter (fun u=>H v u∧¬E v u)).card|≤b+c :=by
  let Qrow:=Q.neighborFinset v∩I
  let Rrow:=R.neighborFinset v∩I
  let Hrow:=J.filter (H v)
  let Erow:=J.filter (E v)
  have hRsub:Rrow⊆Qrow:=by
    intro x hx
    have h: x∈R.neighborFinset v∧x∈I:=Finset.mem_inter.mp hx
    exact Finset.mem_inter.mpr ⟨(Q.mem_neighborFinset v x).mpr (hRQ ((R.mem_neighborFinset v x).mp h.1)),h.2⟩
  have hEsub:Erow⊆Hrow:=by
    intro u hu
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hu).1,hEH v u (Finset.mem_filter.mp hu).2⟩
  have hRrow:((Q\R).neighborFinset v∩I)=Qrow\Rrow:=by
    ext x
    simp only [Qrow,Rrow,Finset.mem_sdiff,Finset.mem_inter,SimpleGraph.mem_neighborFinset,SimpleGraph.sdiff_adj]
    tauto
  have hErow:J.filter (fun u=>H v u∧¬E v u)=Hrow\Erow:=by
    ext u
    simp only [Hrow,Erow,Finset.mem_sdiff,Finset.mem_filter]
    tauto
  have hRq:Rrow.card≤Qrow.card:=Finset.card_le_card hRsub
  have hEq:Erow.card≤Hrow.card:=Finset.card_le_card hEsub
  have hr:(((Q\R).neighborFinset v∩I).card:ℝ)=(Qrow.card:ℝ)-Rrow.card:=by
    rw [hRrow,Finset.card_sdiff_of_subset hRsub,Nat.cast_sub hRq]
  have he:((J.filter (fun u=>H v u∧¬E v u)).card:ℝ)=(Hrow.card:ℝ)-Erow.card:=by
    rw [hErow,Finset.card_sdiff_of_subset hEsub,Nat.cast_sub hEq]
  rw [hr,he]
  have hp:=abs_le.mp hparent
  have hd:=abs_le.mp hdel
  apply abs_le.mpr
  constructor <;> linarith only [hp.1,hp.2,hd.1,hd.2]
end Oberwolfach

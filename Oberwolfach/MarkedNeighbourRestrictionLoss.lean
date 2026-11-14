module

public import Oberwolfach.MarkedHostNeighbourEmbeddings
public import Oberwolfach.BipartiteBlockMatching
public import Oberwolfach.MarkedPhysicalRimDeletionDegrees

@[expose] public section

/-! Exact losses in actual endpoint neighbourhoods after deleting typed
occurrences. The loss is the realised number of deleted root occurrences;
it is not multiplied by a sampling probability. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V E:Type} [Fintype V] [Fintype E] [DecidableEq V]

theorem occurrenceRootNeighbours_restriction_subset (f g:E→V) (P:E→Prop) (v:V):
    occurrenceRootNeighbours (fun e:{e // P e}=>f e.val) (fun e=>g e.val) v⊆
      occurrenceRootNeighbours f g v:=by
  intro x hx
  obtain ⟨e,he,hg⟩:=(Finset.mem_filter.mp hx).2
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,e.val,he,hg⟩

theorem occurrenceRootNeighbours_restriction_loss (f g:E→V)
    (hinj:Function.Injective (fun e=>(f e,g e))) (P:E→Prop) (v:V):
    (occurrenceRootNeighbours f g v\
      occurrenceRootNeighbours (fun e:{e // P e}=>f e.val) (fun e=>g e.val) v).card=
      (Finset.univ.filter (fun e=>¬P e∧g e=v)).card:=by
  have hi:Function.Injective (fun e:{e // P e}=>(f e.val,g e.val)):=hinj.comp Subtype.val_injective
  have hs:=occurrenceRootNeighbours_restriction_subset f g P v
  rw [Finset.card_sdiff_of_subset hs,occurrenceRootNeighbours_card f g hinj,
    occurrenceRootNeighbours_card (fun e:{e // P e}=>f e.val) (fun e=>g e.val) hi]
  have hc:(Finset.univ.filter (fun e:{e // P e}=>g e.val=v)).card=
      (Finset.univ.filter (fun e=>P e∧g e=v)).card:=by
    convert subtype_filter_predicate_card P (fun e=>g e=v) using 1 <;> congr!
  rw [hc]
  have hsplit:(Finset.univ.filter (fun e=>P e∧g e=v)).card+
      (Finset.univ.filter (fun e=>¬P e∧g e=v)).card=
        (Finset.univ.filter (fun e=>g e=v)).card:=by
    simp only [Finset.card_filter,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro e _
    by_cases hp:P e <;> by_cases hg:g e=v <;> simp [hp,hg]
  omega

theorem marked_neighbour_physical_deletion_loss
    (f g:E→V) (π:Equiv.Perm V)
    (hp:Function.Injective (fun e=>({f e,π (g e)}:Finset V))) (D:SimpleGraph V) (v:V):
    ((occurrenceRootNeighbours f g v\
      occurrenceRootNeighbours (fun e:{e // ¬D.Adj (f e) (π (g e))}=>f e.val) (fun e=>g e.val) v).card:ℝ)
      ≤D.degree (π v):=by
  have hi:Function.Injective (fun e=>(f e,g e)):=by
    intro e z he
    apply hp
    have hf:f e=f z:=congrArg Prod.fst he
    have hg:g e=g z:=congrArg Prod.snd he
    change ({f e,π (g e)}:Finset V)={f z,π (g z)}
    rw [hf,hg]
  have he:(occurrenceRootNeighbours f g v\
      occurrenceRootNeighbours (fun e:{e // ¬D.Adj (f e) (π (g e))}=>f e.val) (fun e=>g e.val) v).card=
      (Finset.univ.filter (fun e=>¬¬D.Adj (f e) (π (g e))∧g e=v)).card:=by
    convert occurrenceRootNeighbours_restriction_loss f g hi (fun e=>¬D.Adj (f e) (π (g e))) v using 1 <;> congr!
  rw [he]
  have hc:((Finset.univ.filter (fun e=>¬¬D.Adj (f e) (π (g e))∧g e=v)).card:ℝ)=
      ∑ e,if D.Adj (f e) (π (g e))∧π (g e)=π v then (1:ℝ) else 0:=by
    simp only [not_not,Equiv.apply_eq_iff_eq,Finset.card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  rw [hc]
  exact deleted_pair_indegree f (fun e=>π (g e)) hp D (π v)


theorem marked_outgoing_neighbour_physical_deletion_loss
    (f g:E→V) (π:Equiv.Perm V)
    (hp:Function.Injective (fun e=>({f e,π (g e)}:Finset V))) (D:SimpleGraph V) (v:V):
    ((occurrenceRootNeighbours g f v\
      occurrenceRootNeighbours (fun e:{e // ¬D.Adj (f e) (π (g e))}=>g e.val) (fun e=>f e.val) v).card:ℝ)
      ≤D.degree v:=by
  have hi:Function.Injective (fun e=>(g e,f e)):=by
    intro e z he
    apply hp
    have hf:f e=f z:=congrArg Prod.snd he
    have hg:g e=g z:=congrArg Prod.fst he
    change ({f e,π (g e)}:Finset V)={f z,π (g z)}
    rw [hf,hg]
  have he:(occurrenceRootNeighbours g f v\
      occurrenceRootNeighbours (fun e:{e // ¬D.Adj (f e) (π (g e))}=>g e.val) (fun e=>f e.val) v).card=
      (Finset.univ.filter (fun e=>¬¬D.Adj (f e) (π (g e))∧f e=v)).card:=by
    convert occurrenceRootNeighbours_restriction_loss g f hi (fun e=>¬D.Adj (f e) (π (g e))) v using 1 <;> congr!
  rw [he]
  have hc:((Finset.univ.filter (fun e=>¬¬D.Adj (f e) (π (g e))∧f e=v)).card:ℝ)=
      ∑ e,if D.Adj (f e) (π (g e))∧f e=v then (1:ℝ) else 0:=by
    simp only [not_not,Finset.card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  rw [hc]
  exact deleted_pair_outdegree f (fun e=>π (g e)) hp D v

end Oberwolfach

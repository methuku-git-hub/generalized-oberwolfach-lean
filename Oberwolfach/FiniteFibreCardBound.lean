module

public import Oberwolfach.TwoPathPacking

@[expose] public section

/-! Cardinality bounds from the actual fibre counts of a finite set. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem finite_card_le_uniform_fibre {A V:Type} [Fintype V] [DecidableEq V]
    (S:Finset A) (f:A→V) (b:ℝ)
    (h:∀ v,((S.filter (fun a=>f a=v)).card:ℝ)≤b):
    (S.card:ℝ)≤b*Fintype.card V:=by
  have he:∑ v,(S.filter (fun a=>f a=v)).card=S.card:=by
    simpa using Finset.sum_card_fiberwise_eq_card_filter S Finset.univ f
  have hh:=Finset.sum_le_sum (fun v (_:v∈(Finset.univ:Finset V))=>h v)
  rw [←Nat.cast_sum,he] at hh
  simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_comm] using hh

theorem finite_arc_card_le_uniform_incidence {A V:Type} [Fintype V] [DecidableEq V]
    (S:Finset A) (tail head:A→V) (b:ℝ)
    (h:∀ v,((S.filter (fun a=>v=tail a∨v=head a)).card:ℝ)≤b):
    (S.card:ℝ)≤b*Fintype.card V:=by
  apply finite_card_le_uniform_fibre S tail b
  intro v
  apply le_trans _ (h v)
  exact_mod_cast Finset.card_le_card (show S.filter (fun a=>tail a=v)⊆
    S.filter (fun a=>v=tail a∨v=head a) from fun a ha=>
      Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp ha).1,Or.inl (Finset.mem_filter.mp ha).2.symm⟩)

end Oberwolfach

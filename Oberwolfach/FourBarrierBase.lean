module

public import Oberwolfach.GraphJoinDegrees
public import Oberwolfach.FourCycleParity

@[expose] public section

/-! The three-part host for the ordinary four-cycle threshold obstruction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def fourBarrierBase (t : ℕ) : SimpleGraph (Fin ((t + t) + (t - 1))) :=
  joinOnFin (disjointSumOnFin (⊤ : SimpleGraph (Fin t)) ⊤) ⊥

def fourBarrierA (t : ℕ) : Fin t ↪ Fin ((t + t) + (t - 1)) :=
  (sumLeftEmbedding t t).trans (sumLeftEmbedding (t + t) (t - 1))

def fourBarrierC (t : ℕ) : Fin t ↪ Fin ((t + t) + (t - 1)) :=
  (Function.Embedding.inr.trans
    (finSumFinEquiv : Fin t ⊕ Fin t ≃ Fin (t + t)).toEmbedding).trans
      (sumLeftEmbedding (t + t) (t - 1))

def fourBarrierColour (t : ℕ) (v : Fin ((t + t) + (t - 1))) : Fin 3 :=
  Sum.elim
    (fun x => Sum.elim (fun _ => 0) (fun _ => 2)
      ((finSumFinEquiv : Fin t ⊕ Fin t ≃ Fin (t + t)).symm x))
    (fun _ => 1)
    ((finSumFinEquiv : Fin (t + t) ⊕ Fin (t - 1) ≃ Fin ((t + t) + (t - 1))).symm v)

theorem fourBarrierColour_A (t : ℕ) (v : Fin t) :
    fourBarrierColour t (fourBarrierA t v) = 0 := by
  simp only [fourBarrierColour, fourBarrierA, sumLeftEmbedding,
    Function.Embedding.trans_apply, Function.Embedding.inl_apply, Equiv.toEmbedding_apply,
    Equiv.symm_apply_apply, Sum.elim_inl]

theorem fourBarrierColour_C (t : ℕ) (v : Fin t) :
    fourBarrierColour t (fourBarrierC t v) = 2 := by
  simp only [fourBarrierColour, fourBarrierC, sumLeftEmbedding,
    Function.Embedding.trans_apply, Function.Embedding.inl_apply, Function.Embedding.inr_apply,
    Equiv.toEmbedding_apply, Equiv.symm_apply_apply, Sum.elim_inl, Sum.elim_inr]

theorem fourBarrierColour_zero_iff (t : ℕ) (v : Fin ((t + t) + (t - 1))) :
    fourBarrierColour t v = 0 ↔ ∃ a, fourBarrierA t a = v := by
  constructor
  · intro hv
    obtain ⟨z, rfl⟩ := (finSumFinEquiv :
      Fin (t + t) ⊕ Fin (t - 1) ≃ Fin ((t + t) + (t - 1))).surjective v
    cases z with
    | inr b =>
      simp only [fourBarrierColour, Equiv.symm_apply_apply, Sum.elim_inr] at hv
      norm_num at hv
    | inl z =>
      obtain ⟨z, rfl⟩ := (finSumFinEquiv : Fin t ⊕ Fin t ≃ Fin (t + t)).surjective z
      cases z with
      | inr c =>
        simp only [fourBarrierColour, Equiv.symm_apply_apply, Sum.elim_inl, Sum.elim_inr] at hv
        norm_num at hv
      | inl a => exact ⟨a, rfl⟩
  · rintro ⟨a, rfl⟩
    exact fourBarrierColour_A t a

theorem fourBarrierBase_adj_A (t : ℕ) (u v : Fin t) :
    (fourBarrierBase t).Adj (fourBarrierA t u) (fourBarrierA t v) ↔ u ≠ v := by
  change (fourBarrierBase t).Adj
    (finSumFinEquiv (Sum.inl (finSumFinEquiv (Sum.inl u))))
    (finSumFinEquiv (Sum.inl (finSumFinEquiv (Sum.inl v)))) ↔ _
  rw [fourBarrierBase, joinOnFin_adj_left, disjointSumOnFin_adj]
  rfl

theorem fourBarrierBase_adj_C (t : ℕ) (u v : Fin t) :
    (fourBarrierBase t).Adj (fourBarrierC t u) (fourBarrierC t v) ↔ u ≠ v := by
  change (fourBarrierBase t).Adj
    (finSumFinEquiv (Sum.inl (finSumFinEquiv (Sum.inr u))))
    (finSumFinEquiv (Sum.inl (finSumFinEquiv (Sum.inr v)))) ↔ _
  rw [fourBarrierBase, joinOnFin_adj_left, disjointSumOnFin_adj]
  rfl

theorem fourBarrierBase_allowed (t : ℕ) (u v : Fin ((t + t) + (t - 1)))
    (huv : (fourBarrierBase t).Adj u v) :
    fourBarrierAllowed (fourBarrierColour t u) (fourBarrierColour t v) := by
  obtain ⟨u, rfl⟩ := (finSumFinEquiv :
    Fin (t + t) ⊕ Fin (t - 1) ≃ Fin ((t + t) + (t - 1))).surjective u
  obtain ⟨v, rfl⟩ := (finSumFinEquiv :
    Fin (t + t) ⊕ Fin (t - 1) ≃ Fin ((t + t) + (t - 1))).surjective v
  cases u with
  | inl u =>
    cases v with
    | inl v =>
      rw [fourBarrierBase, joinOnFin_adj_left] at huv
      obtain ⟨u, rfl⟩ := (finSumFinEquiv : Fin t ⊕ Fin t ≃ Fin (t + t)).surjective u
      obtain ⟨v, rfl⟩ := (finSumFinEquiv : Fin t ⊕ Fin t ≃ Fin (t + t)).surjective v
      rw [disjointSumOnFin_adj] at huv
      cases u <;> cases v <;>
        simp only [SimpleGraph.sum_adj, fourBarrierColour, Equiv.symm_apply_apply,
          Sum.elim_inl, Sum.elim_inr] at huv ⊢ <;> norm_num [fourBarrierAllowed] at *
    | inr v =>
      obtain ⟨u, rfl⟩ := (finSumFinEquiv : Fin t ⊕ Fin t ≃ Fin (t + t)).surjective u
      cases u <;> simp only [fourBarrierColour, Equiv.symm_apply_apply,
        Sum.elim_inl, Sum.elim_inr] <;> norm_num [fourBarrierAllowed]
  | inr u =>
    cases v with
    | inl v =>
      obtain ⟨v, rfl⟩ := (finSumFinEquiv : Fin t ⊕ Fin t ≃ Fin (t + t)).surjective v
      cases v <;> simp only [fourBarrierColour, Equiv.symm_apply_apply,
        Sum.elim_inl, Sum.elim_inr] <;> norm_num [fourBarrierAllowed]
    | inr v =>
      rw [fourBarrierBase, joinOnFin_adj_right] at huv
      cases huv

theorem fourBarrierBase_internal_edges (t : ℕ) :
    (fourBarrierBase t).edgeFinset.filter (colourInternalEdge (fourBarrierColour t)) =
      ((⊤ : SimpleGraph (Fin t)).map (fourBarrierA t)).edgeFinset := by
  ext e
  induction e using Sym2.ind with
  | _ u v =>
    simp only [Finset.mem_filter, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
      colourInternalEdge_pair]
    constructor
    · rintro ⟨huv, hu, hv⟩
      obtain ⟨a, rfl⟩ := (fourBarrierColour_zero_iff t u).mp hu
      obtain ⟨b, rfl⟩ := (fourBarrierColour_zero_iff t v).mp hv
      apply SimpleGraph.map_adj_apply.mpr
      exact (fourBarrierBase_adj_A t a b).mp huv
    · intro huv
      rw [SimpleGraph.map_adj] at huv
      obtain ⟨a, b, hab, rfl, rfl⟩ := huv
      exact ⟨(fourBarrierBase_adj_A t a b).mpr hab, fourBarrierColour_A t a,
        fourBarrierColour_A t b⟩

theorem fourBarrierBase_internal_card (t : ℕ) :
    ((fourBarrierBase t).edgeFinset.filter (colourInternalEdge (fourBarrierColour t))).card =
      t.choose 2 := by
  rw [fourBarrierBase_internal_edges]
  have hh := SimpleGraph.card_edgeFinset_map (fourBarrierA t) (⊤ : SimpleGraph (Fin t))
  have hc := SimpleGraph.card_edgeFinset_top_eq_card_choose_two (V := Fin t)
  simp only [← Set.ncard_coe_finset, SimpleGraph.coe_edgeFinset, Fintype.card_fin] at hh hc ⊢
  exact hh.trans hc

theorem fourBarrierBase_degree_core (t : ℕ) (x : Fin (t + t)) :
    (fourBarrierBase t).degree (finSumFinEquiv (Sum.inl x)) = (t - 1) + (t - 1) := by
  rw [fourBarrierBase, joinOnFin_degree_left]
  have htop : (⊤ : SimpleGraph (Fin t)).IsRegularOfDegree (t - 1) := by
    intro v
    simpa only [SimpleGraph.completeGraph_eq_top, Fintype.card_fin, ← SimpleGraph.ncard_neighborSet]
      using SimpleGraph.complete_graph_degree v
  have hh := disjointSumOnFin_regular (⊤ : SimpleGraph (Fin t)) ⊤
    (d := t - 1)
    (by intro v; simpa only [← SimpleGraph.ncard_neighborSet] using htop v)
    (by intro v; simpa only [← SimpleGraph.ncard_neighborSet] using htop v) x
  simpa only [← SimpleGraph.ncard_neighborSet] using congrArg (fun z => (t - 1) + z) hh

theorem fourBarrierBase_degree_middle (t : ℕ) (x : Fin (t - 1)) :
    (fourBarrierBase t).degree (finSumFinEquiv (Sum.inr x)) = t + t := by
  rw [fourBarrierBase, joinOnFin_degree_right]
  simpa only [← SimpleGraph.ncard_neighborSet, Nat.add_zero]
    using congrArg (fun z => t + t + z) (SimpleGraph.bot_degree x)

theorem fourBarrierBase_degrees (t : ℕ) (x : Fin ((t + t) + (t - 1))) :
    Even ((fourBarrierBase t).degree x) ∧
      (t - 1) + (t - 1) ≤ (fourBarrierBase t).degree x := by
  obtain ⟨x, rfl⟩ := (finSumFinEquiv :
    Fin (t + t) ⊕ Fin (t - 1) ≃ Fin ((t + t) + (t - 1))).surjective x
  cases x with
  | inl x =>
    rw [fourBarrierBase_degree_core]
    exact ⟨⟨t - 1, rfl⟩, le_refl _⟩
  | inr x =>
    rw [fourBarrierBase_degree_middle]
    exact ⟨⟨t, rfl⟩, by omega⟩

theorem fourBarrierBase_edge_card (t : ℕ) :
    (fourBarrierBase t).edgeFinset.card = 3 * t * (t - 1) := by
  have hh := (fourBarrierBase t).sum_degrees_eq_twice_card_edges
  rw [← (finSumFinEquiv : Fin (t + t) ⊕ Fin (t - 1) ≃
    Fin ((t + t) + (t - 1))).sum_comp] at hh
  simp only [Fintype.sum_sum_type, fourBarrierBase_degree_core,
    fourBarrierBase_degree_middle, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul] at hh
  nlinarith

end Oberwolfach

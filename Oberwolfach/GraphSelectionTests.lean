module

public import Oberwolfach.SelectionCounters
public import Mathlib.Combinatorics.SimpleGraph.Finite

@[expose] public section

/-! The fixed tests for sequential graph selection are vertices inside
prescribed supports. Edge-disjoint candidates give the required bound
on how many candidates can affect one such test. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V A : Type*} [Fintype V] [DecidableEq V] [Fintype A] {N : ℕ}

def GraphSupportedOn (S : Finset V) (F : SimpleGraph V) : Prop :=
  ∀ v w,F.Adj v w → v∈S ∧ w∈S

abbrev SelectionVertexTest (S : Fin N→Finset V) := {iv : Fin N×V // iv.2∈S iv.1}

def graphSelectionActive (S : Fin N→Finset V) (j : Fin N) (x : SelectionVertexTest S) : Prop :=
  j.val < x.val.1.val ∧ x.val.2∈S j

def graphSelectionHit (S : Fin N→Finset V) (x : SelectionVertexTest S) (F : SimpleGraph V) : Prop :=
  ∃ w∈S x.val.1,F.Adj x.val.2 w

theorem graphSelectionHit_bot (S : Fin N→Finset V) (x : SelectionVertexTest S) :
    ¬graphSelectionHit S x (⊥ : SimpleGraph V) := by simp [graphSelectionHit]

theorem selectionVertexTest_card (S : Fin N→Finset V) :
    Fintype.card (SelectionVertexTest S)=∑ v,(Finset.univ.filter (fun i=>v∈S i)).card := by
  simp only [SelectionVertexTest,Fintype.card_subtype,Finset.card_filter,Fintype.sum_prod_type]
  exact Finset.sum_comm

theorem selectionVertexTest_card_le (S : Fin N→Finset V) (M : ℝ)
    (hM : ∀ v,((Finset.univ.filter (fun i=>v∈S i)).card:ℝ) ≤ M) :
    (Fintype.card (SelectionVertexTest S):ℝ) ≤ M*Fintype.card V := by
  rw [selectionVertexTest_card,Nat.cast_sum]
  have hh := Finset.sum_le_sum (fun v (_ : v∈Finset.univ)=>hM v)
  simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_comm] using hh

theorem graphSelection_remaining_le (S : Fin N→Finset V) (k : ℕ) (x : SelectionVertexTest S) :
    selectionRemaining (graphSelectionActive S) k x ≤
      (Finset.univ.filter (fun i=>x.val.2∈S i)).card := by
  apply Finset.card_le_card
  intro i hi
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hi).2.2.2⟩

theorem disjoint_graphs_no_common_edge (F G : SimpleGraph V) (h : Disjoint F G)
    (v w : V) (hF : F.Adj v w) (hG : G.Adj v w) : False := by
  have hh : F⊓G ≤ ⊥ := disjoint_iff_inf_le.mp h
  exact hh ⟨hF,hG⟩

theorem graph_candidates_hit_bound (S T : Finset V) (v : V) (F : A→SimpleGraph V)
    (hsup : ∀ a,GraphSupportedOn S (F a))
    (hdisj : ∀ a b,a≠b → Disjoint (F a) (F b)) :
    (Finset.univ.filter (fun a=>∃ w∈T,(F a).Adj v w)).card ≤ (S∩T).card := by
  let Hit := {a : A // ∃ w∈T,(F a).Adj v w}
  let f : Hit→{w : V // w∈S∩T} := fun a=>⟨Classical.choose a.property,
    Finset.mem_inter.mpr ⟨(hsup a.val v _ (Classical.choose_spec a.property).2).2,
      (Classical.choose_spec a.property).1⟩⟩
  have hf : Function.Injective f := by
    intro a b he
    apply Subtype.ext
    by_contra hn
    have hv : Classical.choose a.property=Classical.choose b.property := congrArg Subtype.val he
    have ha := (Classical.choose_spec a.property).2
    have hb := (Classical.choose_spec b.property).2
    rw [← hv] at hb
    exact disjoint_graphs_no_common_edge (F a.val) (F b.val) (hdisj a.val b.val hn) v _ ha hb
  have hh := Fintype.card_le_of_injective f hf
  simpa only [Hit,Fintype.card_subtype,Fintype.card_coe,Finset.filter_mem_eq_inter,Finset.univ_inter] using hh

end Oberwolfach

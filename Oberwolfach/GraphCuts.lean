module

public import Oberwolfach.NormalizedDemands
public import Mathlib.Combinatorics.SimpleGraph.Finite

@[expose] public section

/-! Concrete ordered-edge counts and the large-cut consequence of minimum degree. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def graphCut {V : Type*} [Fintype V] (G : SimpleGraph V) (S T : Finset V) : ℕ :=
  ∑ x ∈ S, (G.neighborFinset x ∩ T).card

theorem graphCut_eq_sum
    {V : Type*} [Fintype V] (G : SimpleGraph V) (S T : Finset V) :
    graphCut G S T = ∑ x ∈ S, ∑ y ∈ T, if G.Adj x y then 1 else 0 := by
  unfold graphCut
  apply Finset.sum_congr rfl
  intro x _
  have hh : G.neighborFinset x ∩ T = T.filter (G.Adj x) := by
    ext y
    simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset, Finset.mem_filter]
    tauto
  rw [hh, Finset.card_filter]

theorem graphCut_symm
    {V : Type*} [Fintype V] (G : SimpleGraph V) (S T : Finset V) :
    graphCut G S T = graphCut G T S := by
  rw [graphCut_eq_sum, graphCut_eq_sum, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro x _
  rw [G.adj_comm]

theorem graphCut_lower_of_degrees
    {V : Type*} [Fintype V] (G : SimpleGraph V) (S T : Finset V) {d : ℝ}
    (hdegree : ∀ x ∈ S, d ≤ (G.degree x : ℝ)) :
    (S.card : ℝ) * (d + T.card - Fintype.card V) ≤ (graphCut G S T : ℝ) := by
  have hx (x : V) (hx : x ∈ S) : d + T.card - Fintype.card V ≤
      ((G.neighborFinset x ∩ T).card : ℝ) := by
    have hc := Finset.card_inter_add_card_union (G.neighborFinset x) T
    have hu := Finset.card_le_univ (G.neighborFinset x ∪ T)
    have hcr : ((G.neighborFinset x ∩ T).card : ℝ) +
        ((G.neighborFinset x ∪ T).card : ℝ) = (G.degree x : ℝ) + T.card := by
      exact_mod_cast (by simpa only [SimpleGraph.card_neighborFinset_eq_degree] using hc)
    have hur : ((G.neighborFinset x ∪ T).card : ℝ) ≤ Fintype.card V := by exact_mod_cast hu
    linarith [hdegree x hx]
  have hh := Finset.sum_le_sum hx
  simpa only [graphCut, Nat.cast_sum, Finset.sum_const, nsmul_eq_mul] using hh

theorem graphCut_large_of_minDegree
    {V : Type*} [Fintype V] (G : SimpleGraph V) {α δ : ℝ}
    (hdegree : ∀ x, (1 / 2 + α) * Fintype.card V ≤ (G.degree x : ℝ))
    (S T : Finset V)
    (hlarge : (1 - 2 * δ) * Fintype.card V < (S.card : ℝ) + T.card) :
    (α - δ) * Fintype.card V * min (S.card : ℝ) T.card ≤ (graphCut G S T : ℝ) := by
  have hsmallLarge (A B : Finset V)
      (hab : A.card ≤ B.card)
      (hlarge : (1 - 2 * δ) * Fintype.card V < (A.card : ℝ) + B.card) :
      (α - δ) * Fintype.card V * A.card ≤ (graphCut G A B : ℝ) := by
    have hr : (A.card : ℝ) ≤ B.card := by exact_mod_cast hab
    have hb : (1 / 2 - δ) * Fintype.card V ≤ (B.card : ℝ) := by linarith
    have hh := graphCut_lower_of_degrees G A B (fun x _ => hdegree x)
    have hm := mul_le_mul_of_nonneg_left hb (show (0 : ℝ) ≤ A.card by positivity)
    nlinarith
  rcases le_total S.card T.card with hST | hTS
  · have hr : (S.card : ℝ) ≤ T.card := by exact_mod_cast hST
    rw [min_eq_left hr]
    exact hsmallLarge S T hST hlarge
  · have hr : (T.card : ℝ) ≤ S.card := by exact_mod_cast hTS
    rw [min_eq_right hr, graphCut_symm]
    exact hsmallLarge T S hTS (by linarith)

end Oberwolfach

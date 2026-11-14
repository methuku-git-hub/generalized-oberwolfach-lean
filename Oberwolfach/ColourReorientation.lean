module

public import Oberwolfach.ColourRestriction

@[expose] public section

/-! Cut losses after an orientation change and exclusion of protected
physical edges. The excluded edge count is a realised count. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def excludeGraph {V : Type*} (F : SimpleGraph V) (M : V → V → ℕ) (x y : V) : ℕ :=
  if F.Adj x y then 0 else M x y

theorem sampledColourDegree_eq_sum {V : Type*} [Fintype V] {k : ℕ}
    (F : SimpleGraph V) (c : Sym2 V → Fin k) (a : Fin k) (x : V) :
    sampledColourDegree F c a x = ∑ y, if F.Adj x y ∧ c s(x,y) = a then 1 else 0 := by
  rw [sampledColourDegree, Finset.card_filter]
  have hh : F.neighborFinset x = Finset.univ.filter (F.Adj x) := by ext y; simp
  rw [hh, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro y _
  by_cases hf : F.Adj x y <;> by_cases hc : c s(x,y) = a <;> simp [hf, hc]

theorem edgeColourGraph_degree {V : Type*} [Fintype V] {k : ℕ}
    (F : SimpleGraph V) (c : Sym2 V → Fin k) (a : Fin k) (x : V) :
    (edgeColourGraph F c a).degree x = sampledColourDegree F c a x := by
  unfold SimpleGraph.degree sampledColourDegree
  congr 1
  ext y
  simp [edgeColourGraph]

theorem sampledColourDegree_sup_le {V : Type*} [Fintype V] {k : ℕ}
    (Z A : SimpleGraph V) (c : Sym2 V → Fin k) (a : Fin k) (x : V) :
    sampledColourDegree (Z ⊔ A) c a x ≤ sampledColourDegree Z c a x + A.degree x := by
  rw [sampledColourDegree_eq_sum, sampledColourDegree_eq_sum]
  have hdeg : (∑ y, if A.Adj x y then 1 else 0 : ℕ) = A.degree x := by
    rw [← Finset.card_filter, SimpleGraph.degree]
    congr 1
    ext y
    simp
  rw [← hdeg, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro y _
  by_cases hz : Z.Adj x y <;> by_cases ha : A.Adj x y <;>
    by_cases hc : c s(x,y) = a <;> simp [SimpleGraph.sup_adj, hz, ha, hc]

theorem graph_sup_degree_le {V : Type*} [Fintype V] (Z A : SimpleGraph V) (x : V) :
    (Z ⊔ A).degree x ≤ Z.degree x + A.degree x := by
  rw [SimpleGraph.degree, SimpleGraph.neighborFinset_sup]
  exact Finset.card_union_le _ _

theorem colourReorientation_cut_loss
    {V : Type*} [Fintype V] {k : ℕ}
    (c : Sym2 V → Fin k) (M N : V → V → ℕ) (F : SimpleGraph V)
    (hM : ∀ x y, M x y ≤ 1)
    {b : ℝ} {f : Fin k → ℝ}
    (hchange : ∀ x, ((Finset.univ.filter (fun y => M x y ≠ N x y ∨ M y x ≠ N y x)).card : ℝ) ≤ b)
    (hforbid : ∀ a x, (sampledColourDegree F c a x : ℝ) ≤ f a)
    (a : Fin k) (S T : Finset V) :
    (matrixCut (colourRestriction c M a) S T : ℝ) -
      (f a + b) * min (S.card : ℝ) T.card ≤
      (matrixCut (excludeGraph F (colourRestriction c N a)) S T : ℝ) := by
  let W (x y : V) :=
    (if F.Adj x y ∧ c s(x,y) = a then 1 else 0 : ℕ) +
    (if M x y ≠ N x y ∨ M y x ≠ N y x then 1 else 0 : ℕ)
  have hpoint (x y : V) : colourRestriction c M a x y ≤
      excludeGraph F (colourRestriction c N a) x y + W x y := by
    have hm := hM x y
    by_cases hc : c s(x,y) = a
    · by_cases hf : F.Adj x y
      · simp [colourRestriction, excludeGraph, W, hc, hf]; omega
      · by_cases he : M x y = N x y
        · simp [colourRestriction, excludeGraph, W, hc, hf, he]
        · simp [colourRestriction, excludeGraph, W, hc, hf, he]; omega
    · simp [colourRestriction, W, hc]
  have hrow (x : V) : ((∑ y, W x y : ℕ) : ℝ) ≤ f a + b := by
    dsimp [W]
    rw [Finset.sum_add_distrib, Nat.cast_add, ← sampledColourDegree_eq_sum,
      ← Finset.card_filter]
    exact add_le_add (hforbid a x) (hchange x)
  have hsym (x y : V) : W x y = W y x := by
    simp only [W, F.adj_comm, Sym2.eq_swap, or_comm]
  apply matrixCut_loss_bound _ _ W hpoint hrow
  intro y
  simpa only [hsym] using hrow y

end Oberwolfach

module

public import Oberwolfach.ConditionalPartitionDegrees
public import Oberwolfach.ConditionalPartitionEvents
public import Mathlib.Combinatorics.SimpleGraph.Finite

@[expose] public section

/-! Conditional degree estimates for the actual ordinary and successor
interfaces. For the latter, the summation variable is mapped by π, so the
test set is the inverse image of a graph neighbourhood. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def graphCellDegree {V : Type*} [Fintype V] {k : ℕ} {d : Fin k → ℕ}
    (G : SimpleGraph V) (σ : Equiv.Perm V) (P : FixedPartition V k d)
    (v : V) (a : Fin k) : ℕ :=
  (Finset.univ.filter (fun x => G.Adj v (σ x) ∧ P.1 x = a)).card

theorem permutation_neighbour_count {V : Type*} [Fintype V]
    (G : SimpleGraph V) (σ : Equiv.Perm V) (v : V) :
    (Finset.univ.filter (fun x => G.Adj v (σ x))).card = G.degree v := by
  rw [Finset.card_filter, ← G.card_neighborFinset_eq_degree]
  have he : (Finset.univ.filter (G.Adj v)) = G.neighborFinset v := by
    ext x
    simp
  rw [← he, Finset.card_filter]
  exact Fintype.sum_equiv σ _ _ (fun _ => rfl)

theorem split_neighbour_count {X Y : Type*} [Fintype X] [Fintype Y]
    (G : SimpleGraph (X ⊕ Y)) (σ : Equiv.Perm (X ⊕ Y)) (v : X ⊕ Y) :
    (Finset.univ.filter (fun x => G.Adj v (σ (Sum.inl x)))).card +
      (Finset.univ.filter (fun y => G.Adj v (σ (Sum.inr y)))).card = G.degree v := by
  rw [← permutation_neighbour_count G σ v]
  simp only [Finset.card_filter, Fintype.sum_sum_type]

theorem rooted_graphCellDegree {X Y : Type*} [Fintype X] [Fintype Y]
    {k : ℕ} {r : X → Fin k} {d : Fin k → ℕ}
    (G : SimpleGraph (X ⊕ Y)) (σ : Equiv.Perm (X ⊕ Y))
    (P : RootedPartition X Y k r d) (v : X ⊕ Y) (a : Fin k) :
    graphCellDegree G σ P.1 v a = rootedCellTest P
      (Finset.univ.filter (fun x => G.Adj v (σ (Sum.inl x))))
      (Finset.univ.filter (fun y => G.Adj v (σ (Sum.inr y)))) a := by
  unfold graphCellDegree rootedCellTest
  congr 1
  ext x
  cases x <;> simp

theorem rooted_graph_degree_tail {X Y : Type*} [Fintype X] [Fintype Y] [Nonempty Y]
    {k : ℕ} (r : X → Fin k) (d : Fin k → ℕ)
    [Nonempty (RootedPartition X Y k r d)] [Nonempty (FixedPartition Y k d)]
    (G : SimpleGraph (X ⊕ Y)) (σ : Equiv.Perm (X ⊕ Y))
    (v : X ⊕ Y) (a : Fin k) (D ε η t : ℝ) (ht : 0 ≤ t)
    (hdeg : |(G.degree v : ℝ) - D| ≤ ε * ((Fintype.card X : ℝ) + Fintype.card Y))
    (hmargin : t + 2 * Fintype.card X + ε * (rootCellSize r a + d a) ≤
      η * (rootCellSize r a + d a)) :
    (FiniteLaw.uniform (RootedPartition X Y k r d)).probability
      (fun P => η * (rootCellSize r a + d a) ≤
        |(graphCellDegree G σ P.1 v a : ℝ) -
          D * (((rootCellSize r a : ℝ) + d a) /
            ((Fintype.card X : ℝ) + Fintype.card Y))|) ≤
      2 * Real.exp (-2 * t ^ 2 / (d a : ℝ)) := by
  simp_rw [rooted_graphCellDegree]
  apply rootedPartition_degree_tail r d _ _ a D ε η t ht _ hmargin
  simpa only [← Nat.cast_add, split_neighbour_count] using hdeg

/-- A single event controls every vertex and every prescribed interface
class for each of the fixed permutations. It also controls external
vertices, since the test variable ranges over the whole vertex set. -/
theorem rooted_graph_degrees_common_event {X Y J : Type*}
    [Fintype X] [Fintype Y] [Nonempty Y] [Fintype J]
    {k : ℕ} (r : X → Fin k) (d : Fin k → ℕ)
    [Nonempty (RootedPartition X Y k r d)] [Nonempty (FixedPartition Y k d)]
    (G : SimpleGraph (X ⊕ Y)) (σ : J → Equiv.Perm (X ⊕ Y))
    (classes : Finset (Fin k)) (D ε η t : ℝ) (ht : 0 ≤ t)
    (hdeg : ∀ v, |(G.degree v : ℝ) - D| ≤
      ε * ((Fintype.card X : ℝ) + Fintype.card Y))
    (hmargin : ∀ a ∈ classes, t + 2 * Fintype.card X + ε * (rootCellSize r a + d a) ≤
      η * (rootCellSize r a + d a)) :
    1 - ∑ a ∈ classes, (Fintype.card J : ℝ) *
        (Fintype.card X + Fintype.card Y) *
          (2 * Real.exp (-2 * t ^ 2 / (d a : ℝ))) ≤
    (FiniteLaw.uniform (RootedPartition X Y k r d)).probability
      (fun P => ∀ a ∈ classes, ∀ j v,
        |(graphCellDegree G (σ j) P.1 v a : ℝ) -
          D * (((rootCellSize r a : ℝ) + d a) /
            ((Fintype.card X : ℝ) + Fintype.card Y))| <
          η * (rootCellSize r a + d a)) := by
  let tests := classes ×ˢ (Finset.univ : Finset (J × (X ⊕ Y)))
  have h := finiteLaw_common_event_lower
    (FiniteLaw.uniform (RootedPartition X Y k r d)) tests
    (fun z P => η * (rootCellSize r z.1 + d z.1) ≤
      |(graphCellDegree G (σ z.2.1) P.1 z.2.2 z.1 : ℝ) -
        D * (((rootCellSize r z.1 : ℝ) + d z.1) /
          ((Fintype.card X : ℝ) + Fintype.card Y))|)
    (fun z => 2 * Real.exp (-2 * t ^ 2 / (d z.1 : ℝ)))
    (by
      intro z hz
      exact rooted_graph_degree_tail r d G (σ z.2.1) z.2.2 z.1 D ε η t ht
        (hdeg _) (hmargin _ (Finset.mem_product.mp hz).1))
  simp only [tests, Finset.sum_product, Finset.sum_const, Finset.card_univ,
    Fintype.card_prod, Fintype.card_sum, Nat.cast_mul, Nat.cast_add, nsmul_eq_mul,
    Finset.mem_product, Finset.mem_univ, and_true, Prod.forall,
    forall_const, not_le, mul_assoc] at h
  simp only [mul_assoc]
  apply h.trans_eq
  congr 1
  ext P
  constructor
  · intro hp a ha j v; exact hp a j v ha
  · intro hp a j v ha; exact hp a ha j v

end Oberwolfach

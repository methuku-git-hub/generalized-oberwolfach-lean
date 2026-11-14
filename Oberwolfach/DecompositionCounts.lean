module

public import Oberwolfach.CycleCopies

@[expose] public section

/-! Exact restricted edge counts in an edge decomposition. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem EdgePartition.piece_le {n q : ℕ} {G : SimpleGraph (Fin n)}
    {H : Fin q → SimpleGraph (Fin n)} (h : EdgePartition G H) (i : Fin q) : H i ≤ G := by
  intro x y hxy
  exact (h x y).1.mpr ⟨i, hxy⟩

theorem EdgePartition.filtered_edge_count {n q : ℕ} {G : SimpleGraph (Fin n)}
    {H : Fin q → SimpleGraph (Fin n)} (h : EdgePartition G H)
    (P : Sym2 (Fin n) → Prop) [DecidablePred P] :
    (G.edgeFinset.filter P).card = ∑ i, ((H i).edgeFinset.filter P).card := by
  classical
  have heq : G.edgeFinset.filter P =
      Finset.univ.biUnion (fun i : Fin q => (H i).edgeFinset.filter P) := by
    ext e
    induction e using Sym2.ind with
    | _ u v =>
      simp only [Finset.mem_filter, SimpleGraph.mem_edgeFinset, Finset.mem_biUnion,
        Finset.mem_univ, true_and]
      exact ⟨fun ⟨he, hp⟩ => by
        obtain ⟨i, hi⟩ := (h u v).1.mp he
        exact ⟨i, hi, hp⟩,
        fun ⟨i, hi, hp⟩ => ⟨(h u v).1.mpr ⟨i, hi⟩, hp⟩⟩
  rw [heq, Finset.card_biUnion]
  intro i hi j hj hij
  apply Finset.disjoint_left.mpr
  intro e hei hej
  have hei' := (Finset.mem_filter.mp hei).1
  have hej' := (Finset.mem_filter.mp hej).1
  induction e using Sym2.ind with
  | _ u v =>
    exact hij ((h u v).2 i j (SimpleGraph.mem_edgeFinset.mp hei')
      (SimpleGraph.mem_edgeFinset.mp hej'))

theorem EdgePartition.edge_count {n q : ℕ} {G : SimpleGraph (Fin n)}
    {H : Fin q → SimpleGraph (Fin n)} (h : EdgePartition G H) :
    G.edgeFinset.card = ∑ i, (H i).edgeFinset.card := by
  simpa only [Finset.filter_true] using h.filtered_edge_count (fun _ => True)

theorem HasCycleDecomposition.edge_divisible {n r : ℕ} {G : SimpleGraph (Fin n)}
    (hG : HasCycleDecomposition G r) : r ∣ G.edgeFinset.card := by
  obtain ⟨q, H, hpart, hH⟩ := hG
  rw [hpart.edge_count]
  apply Finset.dvd_sum
  intro i hi
  rw [(hH i).edge_card]

end Oberwolfach

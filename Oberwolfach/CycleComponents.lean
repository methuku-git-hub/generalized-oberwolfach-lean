module

public import Oberwolfach.DecompositionCounts

@[expose] public section

/-! Every component of a cycle-decomposable graph has divisible edge count. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def internalEdges {V : Type*} [Fintype V] (G : SimpleGraph V) (A : Finset V) :
    Finset (Sym2 V) :=
  G.edgeFinset.filter (fun e => ∀ x ∈ e, x ∈ A)

theorem mem_internalEdges {V : Type*} [Fintype V] (G : SimpleGraph V) (A : Finset V)
    (u v : V) : s(u, v) ∈ internalEdges G A ↔ G.Adj u v ∧ u ∈ A ∧ v ∈ A := by
  simp only [internalEdges, Finset.mem_filter, SimpleGraph.mem_edgeFinset,
    SimpleGraph.mem_edgeSet, Sym2.forall_mem_pair]

theorem IsCycleCopy.internal_edge_count {n r : ℕ} {H : SimpleGraph (Fin n)}
    (hH : IsCycleCopy H r) (A : Finset (Fin n))
    (hclosed : ∀ u v, H.Adj u v → (u ∈ A ↔ v ∈ A)) :
    (internalEdges H A).card = r ∨ (internalEdges H A).card = 0 := by
  classical
  obtain ⟨hr, f, hf⟩ := hH
  let i₀ : Fin r := ⟨0, by omega⟩
  have hfc : ∀ i j : Fin r, f i ∈ A ↔ f j ∈ A := by
    intro i j
    obtain ⟨p⟩ := (SimpleGraph.cycleGraph_preconnected (n := r)) i j
    induction p with
    | nil => rfl
    | @cons u v w huv p ih =>
      apply Iff.trans ?_ ih
      apply hclosed
      apply (hf (f u) (f v)).mpr
      exact ⟨u, v, rfl, rfl, (cycleGraph_modular_adj (by omega : 2 ≤ r) u v).mp huv⟩
  by_cases hzero : f i₀ ∈ A
  · left
    have hall : internalEdges H A = H.edgeFinset := by
      ext e
      induction e using Sym2.ind with
      | _ u v =>
        rw [mem_internalEdges, SimpleGraph.mem_edgeFinset]
        refine ⟨fun he => he.1, fun he => ⟨he, ?_⟩⟩
        obtain ⟨i, j, rfl, rfl, hij⟩ := (hf u v).mp he
        exact ⟨(hfc i i₀).mpr hzero, (hfc j i₀).mpr hzero⟩
    rw [hall]
    exact IsCycleCopy.edge_card ⟨hr, f, hf⟩
  · right
    have hempty : internalEdges H A = ∅ := by
      ext e
      induction e using Sym2.ind with
      | _ u v =>
        rw [mem_internalEdges]
        simp only [Finset.notMem_empty, iff_false]
        rintro ⟨he, hu, hv⟩
        obtain ⟨i, j, rfl, rfl, hij⟩ := (hf u v).mp he
        exact hzero ((hfc i i₀).mp hu)
    rw [hempty, Finset.card_empty]

theorem HasCycleDecomposition.closed_set_edge_divisible {n r : ℕ}
    {G : SimpleGraph (Fin n)} (hG : HasCycleDecomposition G r)
    (A : Finset (Fin n)) (hclosed : ∀ u v, G.Adj u v → (u ∈ A ↔ v ∈ A)) :
    r ∣ (internalEdges G A).card := by
  classical
  obtain ⟨q, H, hpart, hH⟩ := hG
  rw [internalEdges, hpart.filtered_edge_count]
  apply Finset.dvd_sum
  intro i hi
  have hci := (hH i).internal_edge_count A
    (fun u v huv => hclosed u v (hpart.piece_le i huv))
  rcases hci with he | he
  · change r ∣ (internalEdges (H i) A).card
    rw [he]
  · change r ∣ (internalEdges (H i) A).card
    rw [he]
    exact dvd_zero r

end Oberwolfach

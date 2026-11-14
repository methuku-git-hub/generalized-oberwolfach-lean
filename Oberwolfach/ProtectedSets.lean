module

public import Oberwolfach.ColourReorientation

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def protectedInducedUnion {V : Type*} {k : ℕ} (G : SimpleGraph V)
    (I : Fin k → Finset V) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ ∃ a, x ∈ I a ∧ y ∈ I a
  symm := by constructor; intro x y h; obtain ⟨a, hx, hy⟩ := h.2; exact ⟨h.1.symm, a, hy, hx⟩
  loopless := by constructor; intro x h; exact (G.ne_of_adj h.1) rfl

theorem protectedInducedUnion_degree {V : Type*} [Fintype V] {k : ℕ}
    (G : SimpleGraph V) (I : Fin k → Finset V) (x : V) :
    (protectedInducedUnion G I).degree x ≤ ∑ a, (I a).card := by
  have hs : (protectedInducedUnion G I).neighborFinset x ⊆ Finset.univ.biUnion I := by
    intro y hy
    have hh : (protectedInducedUnion G I).Adj x y := by simpa using hy
    obtain ⟨_, a, _, ha⟩ := hh
    exact Finset.mem_biUnion.mpr ⟨a, Finset.mem_univ a, ha⟩
  exact (Finset.card_le_card hs).trans (Finset.card_biUnion_le)

theorem graphFromFiniteEdges_degree {V : Type*} [Fintype V]
    (A : Finset (Sym2 V)) (x : V) :
    (SimpleGraph.fromEdgeSet (A : Set (Sym2 V))).degree x ≤ A.card := by
  let H := SimpleGraph.fromEdgeSet (A : Set (Sym2 V))
  have hs : H.edgeFinset ⊆ A := by
    intro e he
    have hh := (SimpleGraph.mem_edgeFinset.mp he)
    rw [SimpleGraph.edgeSet_fromEdgeSet] at hh
    exact hh.1
  exact (H.degree_le_card_edgeFinset x).trans (Finset.card_le_card hs)

theorem positive_common_lower_bound {k : ℕ} (hk : 0 < k) (ρ : Fin k → ℝ)
    (hρ : ∀ a, 0 < ρ a) : ∃ r : ℝ, 0 < r ∧ ∀ a, r ≤ ρ a := by
  have hu : (Finset.univ : Finset (Fin k)).Nonempty := ⟨⟨0, hk⟩, Finset.mem_univ _⟩
  refine ⟨Finset.univ.inf' hu ρ, ?_, ?_⟩
  · exact (Finset.lt_inf'_iff hu).mpr (fun a _ => hρ a)
  · intro a; exact Finset.inf'_le ρ (Finset.mem_univ a)

end Oberwolfach

module

public import Oberwolfach.CycleEdgeEnumeration
public import Oberwolfach.DecompositionCounts

@[expose] public section

/-! The parity obstruction for four-cycles in the three-part lower-bound graph. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def fourBarrierAllowed (a b : Fin 3) : Prop :=
  ¬ (a = 0 ∧ b = 2) ∧ ¬ (a = 2 ∧ b = 0) ∧ ¬ (a = 1 ∧ b = 1)

theorem four_cycle_colour_parity :
    ∀ c : Fin 4 → Fin 3, (∀ i, fourBarrierAllowed (c i) (c (cycleNext i))) →
      Even (∑ i : Fin 4, if c i = 0 ∧ c (cycleNext i) = 0 then (1 : ℕ) else 0) := by
  unfold fourBarrierAllowed
  decide

def colourInternalEdge {V : Type*} (c : V → Fin 3) (e : Sym2 V) : Prop :=
  ∀ x ∈ e, c x = 0

theorem colourInternalEdge_pair {V : Type*} (c : V → Fin 3) (u v : V) :
    colourInternalEdge c s(u, v) ↔ c u = 0 ∧ c v = 0 := by
  simp [colourInternalEdge, Sym2.mem_iff]

theorem IsCycleCopy.four_internal_even {n : ℕ} {H : SimpleGraph (Fin n)}
    (hH : IsCycleCopy H 4) (c : Fin n → Fin 3)
    (hallowed : ∀ u v, H.Adj u v → fourBarrierAllowed (c u) (c v)) :
    Even ((H.edgeFinset.filter (colourInternalEdge c)).card) := by
  obtain ⟨hr, f, hf⟩ := hH
  rw [cycle_copy_filtered_edge_count hr f hf]
  simp only [colourInternalEdge_pair]
  apply four_cycle_colour_parity (fun i => c (f i))
  intro i
  exact hallowed _ _ ((hf _ _).mpr ⟨i, cycleNext i, rfl, rfl, Or.inl rfl⟩)

theorem HasCycleDecomposition.four_internal_even {n : ℕ} {G : SimpleGraph (Fin n)}
    (hG : HasCycleDecomposition G 4) (c : Fin n → Fin 3)
    (hallowed : ∀ u v, G.Adj u v → fourBarrierAllowed (c u) (c v)) :
    Even ((G.edgeFinset.filter (colourInternalEdge c)).card) := by
  obtain ⟨q, H, hpart, hH⟩ := hG
  rw [hpart.filtered_edge_count]
  apply Finset.even_sum
  intro i hi
  exact (hH i).four_internal_even c (fun u v huv => hallowed u v (hpart.piece_le i huv))

end Oberwolfach

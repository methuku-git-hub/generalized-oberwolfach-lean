module

public import Oberwolfach.CyclicFractionalGraphs
public import Oberwolfach.FractionalDecompositions

@[expose] public section

/-! The even cyclic-partite fractional-decomposition theorem, for a graph
whose consecutive interfaces are specified by their adjacency relations. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem cyclicInterfaceGraph_has_fractional_cycles {k : ℕ} {X Y : Type*}
    [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y] [Nonempty X]
    (L : Fin (k + 2) → X → Y → Prop) (R : Fin (k + 2) → Y → X → Prop)
    (δ : ℝ) (hn : 0 < Fintype.card Y)
    (hthreshold : (k + 2 : ℝ) * Fintype.card Y ≤ (2 * (k + 2) - 1) * δ)
    (hdL : ∀ i x, δ ≤ (Finset.univ.filter (L i x)).card)
    (hY : ∀ i y, (Finset.univ.filter (fun x => L i x y)).card =
      (Finset.univ.filter (R i y)).card)
    (hX : ∀ i z, (Finset.univ.filter (fun y => R i y z)).card =
      (Finset.univ.filter (L (finRotate (k + 2) i) z)).card) :
    HasFractionalDecomposition (cyclicInterfaceGraph L R)
      (fun H => IsEmbeddedCycle H ((k + 2) * 2) ∧
        ∃ p : Fin (k + 2) → X × Y × X, H = alternatingTupleGraph p) := by
  obtain ⟨ω, hω, _, hl, hr, hc⟩ :=
    cyclic_interfaces_fractional_weighting L R δ hn hthreshold hdL hY hX
  obtain ⟨hs, he⟩ := cyclic_weighting_graph_equations L R ω hω hl hr hc
  apply fractionalDecomposition_of_indexed _ _ alternatingTupleGraph ω hω _ he
  intro p hp
  exact ⟨hs p hp, ⟨⟨by omega, alternatingCycleEmbedding p, rfl⟩, p, rfl⟩⟩

end Oberwolfach

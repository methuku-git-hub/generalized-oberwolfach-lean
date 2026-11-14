module

public import Oberwolfach.CyclicInterfaceSpread
public import Oberwolfach.CanonicalCycleSupport
public import Oberwolfach.FractionalDecompositions

@[expose] public section

/-! Uniform positive weights on actual part-respecting cycle subgraphs,
with no multiplicity loss from their tuple descriptions. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem cyclicInterfaceGraph_fractional_cycles_bounded {k : ℕ} {X Y : Type*}
    [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y] [Nonempty X]
    (L : Fin (k + 2) → X → Y → Prop) (R : Fin (k + 2) → Y → X → Prop)
    (δ α : ℝ) (hn : 0 < Fintype.card Y) (hα : 0 < α)
    (hcard : Fintype.card X = Fintype.card Y)
    (hthreshold : ((k + 2) + (2 * (k + 2) - 1) * α) * Fintype.card Y ≤
      (2 * (k + 2) - 1) * δ)
    (hdL : ∀ i x, δ ≤ (Finset.univ.filter (L i x)).card)
    (hdY : ∀ i y, δ ≤ (Finset.univ.filter (fun x => L i x y)).card)
    (hY : ∀ i y, (Finset.univ.filter (fun x => L i x y)).card =
      (Finset.univ.filter (R i y)).card)
    (hX : ∀ i z, (Finset.univ.filter (fun y => R i y z)).card =
      (Finset.univ.filter (L (finRotate (k + 2) i) z)).card) :
    ∃ w : SimpleGraph ((Fin (k + 2) × X) ⊕ (Fin (k + 2) × Y)) → ℝ,
      (∀ H, 0 ≤ w H) ∧
      (∀ H, 0 < w H → H ≤ cyclicInterfaceGraph L R ∧
        IsEmbeddedCycle H ((k + 2) * 2) ∧
          ∃ p : Fin (k + 2) → X × Y × X, H = alternatingTupleGraph p) ∧
      (∀ u v, (∑ H, if H.Adj u v then w H else 0) =
        if (cyclicInterfaceGraph L R).Adj u v then 1 else 0) ∧
      (∀ H, H ≤ cyclicInterfaceGraph L R →
        (∃ p : Fin (k + 2) → X × Y × X, H = alternatingTupleGraph p) →
        ((k + 2 : ℝ) * cyclicSectorLower k α) / (Fintype.card Y : ℝ) ^ (2 * k + 2) ≤ w H ∧
        w H ≤ ((k + 2 : ℝ) * cyclicSectorUpper k α) /
          (Fintype.card Y : ℝ) ^ (2 * k + 2)) := by
  obtain ⟨ω, hω, _, hl, hr, hc, hb⟩ := cyclic_interfaces_fractional_weighting_bounded
    L R δ α hn hα hcard hthreshold hdL hdY hY hX
  obtain ⟨hs, he⟩ := cyclic_weighting_graph_equations L R ω hω hl hr hc
  have hprops := indexed_fractional_weight_properties (cyclicInterfaceGraph L R)
    (fun H => IsEmbeddedCycle H ((k + 2) * 2) ∧
      ∃ p : Fin (k + 2) → X × Y × X, H = alternatingTupleGraph p)
    alternatingTupleGraph ω hω
    (fun p hp => ⟨hs p hp, ⟨⟨by omega, alternatingCycleEmbedding p, rfl⟩, p, rfl⟩⟩) he
  refine ⟨indexedFractionalWeight alternatingTupleGraph ω, hprops.1, hprops.2.1,
    hprops.2.2, ?_⟩
  intro H hsub hpart
  obtain ⟨p, rfl⟩ := hpart
  let v := cyclicTupleVertices p
  have hcanon : alternatingTupleGraph (cyclicTupleOfVertices v) = alternatingTupleGraph p := rfl
  have hactual := (canonicalCycleGraph_le_iff L R v).mp (hcanon ▸ hsub)
  have hweight : indexedFractionalWeight alternatingTupleGraph ω (alternatingTupleGraph p) =
      ω (cyclicTupleOfVertices v) := by
    rw [← hcanon]
    exact cyclic_weight_of_canonical_graph ω hω hc v
  rw [hweight]
  exact hb (cyclicTupleOfVertices v) (fun _ => rfl) hactual

end Oberwolfach

module

public import Oberwolfach.CyclicInterfaceSpread
public import Oberwolfach.CanonicalCycleSupport

@[expose] public section

/-! Fractional weights on the unique vertex-choice description of a
transversal cycle. The edge equations and pointwise positive bounds use
one and the same weighting. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem sum_canonical_cyclic_tuples {k : ℕ} {X Y : Type*}
    [Fintype X] [Fintype Y]
    (g : (Fin (k + 2) → X × Y × X) → ℝ)
    (hc : ∀ p, g p ≠ 0 → ∀ i, (p i).2.2 = (p (finRotate (k + 2) i)).1) :
    (∑ v : Fin (k + 2) → X × Y, g (cyclicTupleOfVertices v)) = ∑ p, g p := by
  apply Fintype.sum_of_injective cyclicTupleOfVertices
    (Function.LeftInverse.injective cyclicTupleVertices_inverse)
  · intro p hp
    by_contra hg
    exact hp ⟨cyclicTupleVertices p, cyclicTupleOfVertices_inverse p (hc p hg)⟩
  · intro v; rfl

theorem canonical_cyclic_tuple_weights {k : ℕ} {X : Type*}
    [Fintype X] [Nonempty X]
    (L R : Fin (k + 2) → X → X → Prop)
    (δ α : ℝ) (hn : 0 < Fintype.card X) (hα : 0 < α)
    (hthreshold : ((k + 2) + (2 * (k + 2) - 1) * α) * Fintype.card X ≤
      (2 * (k + 2) - 1) * δ)
    (hdL : ∀ i x, δ ≤ (Finset.univ.filter (L i x)).card)
    (hdY : ∀ i y, δ ≤ (Finset.univ.filter (fun x => L i x y)).card)
    (hY : ∀ i y, (Finset.univ.filter (fun x => L i x y)).card =
      (Finset.univ.filter (R i y)).card)
    (hX : ∀ i z, (Finset.univ.filter (fun y => R i y z)).card =
      (Finset.univ.filter (L (finRotate (k + 2) i) z)).card) :
    ∃ w : (Fin (k + 2) → X × X) → ℝ,
      (∀ v, 0 ≤ w v) ∧
      (∀ v, 0 < w v → ∀ i,
        L i (v i).1 (v i).2 ∧ R i (v i).2 (v (finRotate (k + 2) i)).1) ∧
      (∀ i x y, (∑ v, if v i = (x, y) then w v else 0) = interfaceCapacity (L i) x y) ∧
      (∀ i y z, (∑ v, if ((v i).2, (v (finRotate (k + 2) i)).1) = (y, z)
        then w v else 0) = interfaceCapacity (R i) y z) ∧
      (∀ v, w v ≤ ((k + 2 : ℝ) * cyclicSectorUpper k α) /
        (Fintype.card X : ℝ) ^ (2 * k + 2)) ∧
      (∀ v, (∀ i, L i (v i).1 (v i).2 ∧ R i (v i).2 (v (finRotate (k + 2) i)).1) →
        ((k + 2 : ℝ) * cyclicSectorLower k α) /
          (Fintype.card X : ℝ) ^ (2 * k + 2) ≤ w v) := by
  obtain ⟨ω, hω, _, hl, hr, hc, hb⟩ := cyclic_interfaces_fractional_weighting_bounded
    L R δ α hn hα rfl hthreshold hdL hdY hY hX
  have hs := (cyclic_weighting_graph_equations L R ω hω hl hr hc).1
  let w (v : Fin (k + 2) → X × X) := ω (cyclicTupleOfVertices v)
  have hs' (v) (hv : 0 < w v) : ∀ i,
      L i (v i).1 (v i).2 ∧ R i (v i).2 (v (finRotate (k + 2) i)).1 :=
    (canonicalCycleGraph_le_iff L R v).mp (hs _ hv)
  refine ⟨w, fun v => hω _, hs', ?_, ?_, ?_, ?_⟩
  · intro i x y
    have he := sum_canonical_cyclic_tuples
      (fun p => if ((p i).1, (p i).2.1) = (x,y) then ω p else 0)
      (by intro p hp; apply hc p; have hnz : ω p ≠ 0 := by
            intro hz; simp [hz] at hp
          exact lt_of_le_of_ne (hω p) (Ne.symm hnz))
    simpa only [cyclicTupleOfVertices, Prod.eta, w, hl] using he
  · intro i y z
    have he := sum_canonical_cyclic_tuples
      (fun p => if ((p i).2.1, (p i).2.2) = (y,z) then ω p else 0)
      (by intro p hp; apply hc p; have hnz : ω p ≠ 0 := by
            intro hz; simp [hz] at hp
          exact lt_of_le_of_ne (hω p) (Ne.symm hnz))
    simpa only [cyclicTupleOfVertices, w, hr] using he
  · intro v
    by_cases hz : w v = 0
    · rw [hz]
      exact div_nonneg (mul_nonneg (by positivity) (cyclicSectorConstants_pos k α hα).2.le)
        (by positivity)
    · exact (hb _ (fun _ => rfl) (hs' v (lt_of_le_of_ne (hω _) (Ne.symm hz)))).2
  · intro v hv
    exact (hb _ (fun _ => rfl) hv).1

end Oberwolfach

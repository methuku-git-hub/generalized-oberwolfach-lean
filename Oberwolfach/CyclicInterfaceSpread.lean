module

public import Oberwolfach.CyclicInterfaceFractional
public import Oberwolfach.CyclicSectorEstimates

@[expose] public section

/-! One and the same cyclic weighting satisfies all edge equations and
uniform positive bounds on every actual compatible tuple. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem cyclic_interfaces_fractional_weighting_bounded {k : ℕ} {X Y : Type*}
    [Fintype X] [Fintype Y] [Nonempty X]
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
    ∃ ω : (Fin (k + 2) → X × Y × X) → ℝ,
      (∀ p, 0 ≤ ω p) ∧
      (∑ p, ω p) = (∑ x, cyclicInterfaceDegree L 0 x) ∧
      (∀ i x y, (∑ p, if ((p i).1, (p i).2.1) = (x, y) then ω p else 0) =
        interfaceCapacity (L i) x y) ∧
      (∀ i y z, (∑ p, if ((p i).2.1, (p i).2.2) = (y, z) then ω p else 0) =
        interfaceCapacity (R i) y z) ∧
      (∀ p, 0 < ω p → ∀ i, (p i).2.2 = (p (finRotate (k + 2) i)).1) ∧
      (∀ p, (∀ i, (p i).2.2 = (p (finRotate (k + 2) i)).1) →
        (∀ i, L i (p i).1 (p i).2.1 ∧ R i (p i).2.1 (p i).2.2) →
        ((k + 2 : ℝ) * cyclicSectorLower k α) / (Fintype.card Y : ℝ) ^ (2 * k + 2) ≤ ω p ∧
        ω p ≤ ((k + 2 : ℝ) * cyclicSectorUpper k α) /
          (Fintype.card Y : ℝ) ^ (2 * k + 2)) := by
  have hk : (2 : ℝ) ≤ k + 2 := by linarith [Nat.cast_nonneg (α := ℝ) k]
  have hn' : (0 : ℝ) < Fintype.card Y := by exact_mod_cast hn
  obtain ⟨_, hbase⟩ := positive_margin_base hk hn' hα hthreshold
  obtain ⟨Q, ω, hω, ht, hl, hr, hc, hf, hformula⟩ :=
    cyclic_interfaces_fractional_weighting_with_formula L R δ hn hbase hdL hY hX
  refine ⟨ω, hω, ht, hl, hr, hc, ?_⟩
  intro p hp hpath
  rw [hformula p hp]
  have hb (c : Fin (k + 2)) := cyclicSectorWeight_bounds L R δ α hn hα hcard
    hthreshold hdL hdY hY hX Q hf p hp hpath c
  have hlo := Finset.sum_le_sum (s := Finset.univ) (fun c _ => (hb c).1)
  have hhi := Finset.sum_le_sum (s := Finset.univ) (fun c _ => (hb c).2)
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_add, Nat.cast_ofNat, ← mul_div_assoc] using And.intro hlo hhi

end Oberwolfach

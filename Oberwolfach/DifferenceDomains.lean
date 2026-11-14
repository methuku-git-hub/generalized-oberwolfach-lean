module

public import Oberwolfach.Vortex

@[expose] public section

/-! Degree estimates on the actual differences of nested vertex/index sets. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem real_card_sdiff {V : Type*} [DecidableEq V] {A B : Finset V}
    (hBA : B ⊆ A) : ((A \ B).card : ℝ) = (A.card : ℝ) - B.card := by
  rw [Finset.card_sdiff_of_subset hBA, Nat.cast_sub (Finset.card_le_card hBA)]

theorem real_inter_sdiff_card {V : Type*} [DecidableEq V] (N : Finset V)
    {A B : Finset V} (hBA : B ⊆ A) :
    ((N ∩ (A \ B)).card : ℝ) = ((N ∩ A).card : ℝ) - (N ∩ B).card := by
  have heq : N ∩ (A \ B) = (N ∩ A) \ (N ∩ B) := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_sdiff]
    tauto
  rw [heq]
  exact real_card_sdiff (Finset.inter_subset_inter_left hBA)

theorem subtract_two_degree_errors {a b x y c d β : ℝ}
    (hb : 0 ≤ β) (hsmall : b ≤ a / 4)
    (hx : |x - c| ≤ β * a) (hy : |y - d| ≤ β * b) :
    |(x - y) - (c - d)| ≤ (5 / 3 : ℝ) * β * (a - b) := by
  have ht : |(x - y) - (c - d)| ≤ |x - c| + |y - d| := by
    rw [show (x - y) - (c - d) = (x - c) - (y - d) by ring]
    exact abs_sub (x - c) (y - d)
  have hm := mul_nonneg hb (show 0 ≤ a - 4 * b by linarith)
  nlinarith

theorem nested_domains_degree_subtraction {V U : Type*} [Fintype V]
    [DecidableEq V] [DecidableEq U] (G : SimpleGraph V)
    {A B : Finset V} {I J : Finset U} (hBA : B ⊆ A) (hJI : J ⊆ I)
    (β ρ d : ℝ) (hb : 0 ≤ β) (hsmall : (B.card : ℝ) ≤ A.card / 4)
    (hA : |2 * (I.card : ℝ) / ρ - d * A.card| ≤ β * A.card)
    (hB : |2 * (J.card : ℝ) / ρ - d * B.card| ≤ β * B.card)
    (x : V)
    (hxA : |((G.neighborFinset x ∩ A).card : ℝ) - 2 * I.card / ρ| ≤ β * A.card)
    (hxB : |((G.neighborFinset x ∩ B).card : ℝ) - 2 * J.card / ρ| ≤ β * B.card) :
    |2 * ((I \ J).card : ℝ) / ρ - d * (A \ B).card| ≤
        (5 / 3 : ℝ) * β * (A \ B).card ∧
    |((G.neighborFinset x ∩ (A \ B)).card : ℝ) - 2 * (I \ J).card / ρ| ≤
        (5 / 3 : ℝ) * β * (A \ B).card := by
  have hc := subtract_two_degree_errors hb hsmall hA hB
  have hx := subtract_two_degree_errors hb hsmall hxA hxB
  rw [real_card_sdiff hJI, real_card_sdiff hBA, real_inter_sdiff_card _ hBA]
  have hi : 2 * ((I.card : ℝ) - J.card) / ρ =
      2 * (I.card : ℝ) / ρ - 2 * J.card / ρ := by ring
  rw [hi, mul_sub]
  constructor
  · exact hc
  · exact hx

end Oberwolfach

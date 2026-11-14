module

public import Oberwolfach.IntervalResidualMap

@[expose] public section

/-! Full triple spaces, with zero weight assigned to triples missing an edge.
These identities connect endpoint matrices to actual interface edge loads. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem triple_endpoint_sum {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (w : X → Y → Z → ℝ) (x : X) (z : Z) :
    (∑ p : X × Y × Z, if (p.1, p.2.2) = (x, z) then w p.1 p.2.1 p.2.2 else 0) =
      ∑ y, w x y z := by
  classical
  simp only [Fintype.sum_prod_type, Prod.mk.injEq]
  simp_rw [ite_and]
  simp

theorem triple_left_sum {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (w : X → Y → Z → ℝ) (x : X) (y : Y) :
    (∑ p : X × Y × Z, if (p.1, p.2.1) = (x, y) then w p.1 p.2.1 p.2.2 else 0) =
      ∑ z, w x y z := by
  classical
  simp only [Fintype.sum_prod_type, Prod.mk.injEq]
  simp_rw [ite_and]
  simp

theorem triple_right_sum {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (w : X → Y → Z → ℝ) (y : Y) (z : Z) :
    (∑ p : X × Y × Z, if (p.2.1, p.2.2) = (y, z) then w p.1 p.2.1 p.2.2 else 0) =
      ∑ x, w x y z := by
  classical
  simp only [Fintype.sum_prod_type, Prod.mk.injEq]
  simp_rw [ite_and]
  simp

theorem triple_total_of_endpoints {X Y Z : Type*}
    [Fintype X] [Fintype Y] [Fintype Z]
    (w : X → Y → Z → ℝ) (K : X → Z → ℝ) (m : X → ℝ)
    (hw : ∀ x z, ∑ y, w x y z = K x z) (hK : ∀ x, ∑ z, K x z = m x) :
    (∑ p : X × Y × Z, w p.1 p.2.1 p.2.2) = ∑ x, m x := by
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_comm]
  simp_rw [hw]
  exact hK x

theorem interval_scaled_path_nonneg {X Y Z : Type*}
    [Fintype X] [Fintype Y] [Fintype Z]
    (L : X → Y → Prop) (R : Y → Z → Prop) (k δ : ℝ)
    (hk : 2 ≤ k) (hn : 0 < Fintype.card Y) (hδ : 0 ≤ δ)
    (hthreshold : k * Fintype.card Y ≤ (2 * k - 1) * δ)
    (hdL : ∀ x, δ ≤ (Finset.univ.filter (L x)).card)
    (hdR : ∀ z, δ ≤ (Finset.univ.filter (fun y => R y z)).card)
    (hbal : ∀ y, (Finset.univ.filter (fun x => L x y)).card =
      (Finset.univ.filter (R y)).card)
    {Q : X → Z → ℝ} (hQ : Q ∈ transportMatrices
      (fun x => (Finset.univ.filter (L x)).card / k)
      (fun z => (Finset.univ.filter (fun y => R y z)).card / k))
    (x : X) (y : Y) (z : Z) :
    0 ≤ scaledResidualPath (interfaceCapacity L) (interfaceCapacity R)
      (endpointReserve L R Q) k x y z := by
  obtain ⟨hL, hR⟩ := endpointReserve_capacities L R Q k δ hk hn hδ hthreshold hdL hdR hQ
  have hb : ∀ y, (∑ x, interfaceCapacity L x y) = ∑ z, interfaceCapacity R y z := by
    intro y
    rw [interfaceCapacity_column, interfaceCapacity_row, hbal y]
  unfold scaledResidualPath
  apply div_nonneg _ (by linarith)
  exact (residualPath_bounds _ _
    (fun x y => sub_nonneg.mpr (hL x y))
    (fun y z => sub_nonneg.mpr (hR y z))
    (residual_interfaces_balanced _ _ _ hb) x y z).1

theorem finite_marginal_test {Ω P : Type*} [Fintype Ω] [Fintype P]
    (w : Ω → ℝ) (f : Ω → P) (v : P → ℝ)
    (h : ∀ p, (∑ a, if f a = p then w a else 0) = v p)
    (g : P → ℝ) :
    (∑ a, w a * g (f a)) = ∑ p, v p * g p := by
  classical
  simp_rw [← h, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp only [ite_mul, zero_mul]
  simp

end Oberwolfach

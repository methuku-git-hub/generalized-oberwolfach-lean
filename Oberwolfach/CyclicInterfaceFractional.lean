module

public import Oberwolfach.CyclicWeightData

@[expose] public section

/-! Fractional weights on compatible tuples of paths in actual interfaces.
All transportation data are derived from the given adjacency relations. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

set_option maxHeartbeats 800000 in
theorem cyclic_interfaces_fractional_weighting_with_formula {k : ℕ} {X Y : Type*}
    [Fintype X] [Fintype Y] [Nonempty X]
    (L : Fin (k + 2) → X → Y → Prop) (R : Fin (k + 2) → Y → X → Prop)
    (δ : ℝ) (hn : 0 < Fintype.card Y)
    (hthreshold : (k + 2 : ℝ) * Fintype.card Y ≤ (2 * (k + 2) - 1) * δ)
    (hdL : ∀ i x, δ ≤ (Finset.univ.filter (L i x)).card)
    (hY : ∀ i y, (Finset.univ.filter (fun x => L i x y)).card =
      (Finset.univ.filter (R i y)).card)
    (hX : ∀ i z, (Finset.univ.filter (fun y => R i y z)).card =
      (Finset.univ.filter (L (finRotate (k + 2) i) z)).card) :
    ∃ Q : transportProduct (cyclicInterfaceMarginal L) (finRotate (k + 2)),
    ∃ ω : (Fin (k + 2) → X × Y × X) → ℝ,
      (∀ p, 0 ≤ ω p) ∧
      (∑ p, ω p) = (∑ x, cyclicInterfaceDegree L 0 x) ∧
      (∀ i x y, (∑ p, if ((p i).1, (p i).2.1) = (x, y) then ω p else 0) =
        interfaceCapacity (L i) x y) ∧
      (∀ i y z, (∑ p, if ((p i).2.1, (p i).2.2) = (y, z) then ω p else 0) =
        interfaceCapacity (R i) y z) ∧
      (∀ p, 0 < ω p → ∀ i, (p i).2.2 = (p (finRotate (k + 2) i)).1) ∧
      (∀ i x z, Q.val i x z = walkTransport (cyclicInterfaceMarginal L)
        (cyclicResidualSystem L R Q) (finRotate (k + 2))
        (finRotate (k + 2) i) (k + 1) z x) ∧
      (∀ p, (∀ i, (p i).2.2 = (p (finRotate (k + 2) i)).1) →
        ω p = ∑ c, cyclicSectorWeight L R Q c p) := by
  let m (i : Fin (k + 2)) (x : X) := cyclicInterfaceDegree L i x / (k + 2 : ℝ)
  let B := ∑ x, m 0 x
  obtain ⟨hB, hm, hms⟩ := cyclic_interface_marginals L R δ hn hthreshold hdL hY hX
  have hk : (2 : ℝ) ≤ k + 2 := by linarith [Nat.cast_nonneg (α := ℝ) k]
  have hk0 : (0 : ℝ) < k + 2 := by positivity
  have hδ : 0 ≤ δ := by
    have hn' : (0 : ℝ) < Fintype.card Y := by exact_mod_cast hn
    have hp : 0 < (2 * (k + 2 : ℝ) - 1) * δ :=
      lt_of_lt_of_le (mul_pos hk0 hn') hthreshold
    exact (pos_of_mul_pos_right hp (by linarith [Nat.cast_nonneg (α := ℝ) k])).le
  have hdR (i : Fin (k + 2)) (z : X) :
      δ ≤ (Finset.univ.filter (fun y => R i y z)).card := by
    rw [hX i z]
    exact hdL _ z
  let T := transportProduct m (finRotate (k + 2))
  have hQmat (Q : T) (i : Fin (k + 2)) :
      Q.val i ∈ transportMatrices
        (fun x => (Finset.univ.filter (L i x)).card / (k + 2 : ℝ))
        (fun z => (Finset.univ.filter (fun y => R i y z)).card / (k + 2 : ℝ)) := by
    simpa only [hX, m, cyclicInterfaceDegree] using Q.property i (Set.mem_univ i)
  let H (Q : T) (i : Fin (k + 2)) :=
    intervalResidualMap (L i) (R i) (k + 2 : ℝ) (Q.val i)
  have hHm (Q : T) (i : Fin (k + 2)) :
      H Q i ∈ transportMatrices (m i) (m (finRotate (k + 2) i)) := by
    simpa only [H, hX, m, cyclicInterfaceDegree] using
      intervalResidualMap_mem (L i) (R i) (k + 2) δ hk hn hδ hthreshold
        (hdL i) (hdR i) (hY i) (hQmat Q i)
  have hH : Continuous H := by
    apply continuous_pi
    intro i
    let ev : T → transportMatrices
        (fun x => (Finset.univ.filter (L i x)).card / (k + 2 : ℝ))
        (fun z => (Finset.univ.filter (fun y => R i y z)).card / (k + 2 : ℝ)) :=
      fun Q => ⟨Q.val i, hQmat Q i⟩
    have he : Continuous ev := Continuous.subtype_mk
      ((continuous_apply i).comp continuous_subtype_val) _
    change Continuous (fun Q : T => intervalResidualMap (L i) (R i)
      (k + 2 : ℝ) (ev Q).val)
    exact (intervalResidualMap_continuous (L i) (R i) (k + 2) δ hk hn hδ
      hthreshold (hdL i) (hdR i) (hY i)).comp he
  let ρ (Q : T) (i : Fin (k + 2)) (p : X × Y × X) :=
    endpointReserve (L i) (R i) (Q.val i) p.1 p.2.1 p.2.2
  let S (Q : T) (i : Fin (k + 2)) (p : X × Y × X) :=
    scaledResidualPath (interfaceCapacity (L i)) (interfaceCapacity (R i))
      (endpointReserve (L i) (R i) (Q.val i)) (k + 2 : ℝ) p.1 p.2.1 p.2.2
  have hρ (Q : T) (i : Fin (k + 2)) (p : X × Y × X) : 0 ≤ ρ Q i p :=
    endpointReserve_nonneg _ _ _ (hQmat Q i).1 _ _ _
  have hS (Q : T) (i : Fin (k + 2)) (p : X × Y × X) : 0 ≤ S Q i p :=
    interval_scaled_path_nonneg (L i) (R i) (k + 2) δ hk hn hδ hthreshold
      (hdL i) (hdR i) (hY i) (hQmat Q i) _ _ _
  have hendρ (Q : T) (i : Fin (k + 2)) (x z : X) :
      (∑ y, endpointReserve (L i) (R i) (Q.val i) x y z) = Q.val i x z :=
    endpointReserve_endpoints _ _ _
      (intervalCommon_pos _ _ (k + 2) δ hk hn hδ hthreshold (hdL i) (hdR i)) x z
  have hρtotal (Q : T) (i : Fin (k + 2)) : ∑ p, ρ Q i p = B := by
    rw [triple_total_of_endpoints _ (Q.val i) (m i) (hendρ Q i)
      (Q.property i (Set.mem_univ i)).2.1]
    exact hms i
  have hStotal (Q : T) (i : Fin (k + 2)) : ∑ p, S Q i p = B := by
    rw [triple_total_of_endpoints _ (H Q i) (m i) (fun _ _ => rfl) (hHm Q i).2.1]
    exact hms i
  obtain ⟨Q, ω, hω, htotal, hmarg, hclosed, hfixed, hformula⟩ :=
    fractional_cycle_path_assembly_with_formula m B hB hm hms
      (fun _ (p : X × Y × X) => (p.1, p.2.2)) H hH hHm ρ S hρ hS hρtotal hStotal
      (by intro Q i x z; dsimp only [ρ]; rw [triple_endpoint_sum]; exact hendρ Q i x z)
      (by intro Q i x z; dsimp only [S]; rw [triple_endpoint_sum]; rfl)
  refine ⟨Q, ω, hω, ?_, ?_, ?_, hclosed, hfixed, hformula⟩
  · rw [htotal]
    dsimp only [B, m]
    rw [← Finset.sum_div]
    exact mul_div_cancel₀ _ hk0.ne'
  · intro i x y
    have hh := finite_marginal_test ω (fun p => p i)
      (fun p => ρ Q i p + (k + 1 : ℝ) * S Q i p) (hmarg i)
      (fun p => if (p.1, p.2.1) = (x, y) then (1 : ℝ) else 0)
    simp only [mul_ite, mul_one, mul_zero] at hh
    rw [hh, triple_left_sum (fun a b c => ρ Q i (a, b, c) + (k + 1 : ℝ) * S Q i (a, b, c))]
    have hb (y : Y) : (∑ x, interfaceCapacity (L i) x y) =
        ∑ z, interfaceCapacity (R i) y z := by
      rw [interfaceCapacity_column, interfaceCapacity_row, hY i y]
    have hc := (endpointReserve_capacities (L i) (R i) (Q.val i) (k + 2) δ
      hk hn hδ hthreshold (hdL i) (hdR i) (hQmat Q i)).1
    convert reserve_residual_reconstructs_left (interfaceCapacity (L i))
      (interfaceCapacity (R i)) (endpointReserve (L i) (R i) (Q.val i))
      (k + 2) (by linarith) hc hb x y using 1 <;> dsimp only [ρ, S]
    congr 1
    funext z
    congr 2 <;> ring
  · intro i y z
    have hh := finite_marginal_test ω (fun p => p i)
      (fun p => ρ Q i p + (k + 1 : ℝ) * S Q i p) (hmarg i)
      (fun p => if (p.2.1, p.2.2) = (y, z) then (1 : ℝ) else 0)
    simp only [mul_ite, mul_one, mul_zero] at hh
    rw [hh, triple_right_sum (fun a b c => ρ Q i (a, b, c) + (k + 1 : ℝ) * S Q i (a, b, c))]
    have hb (y : Y) : (∑ x, interfaceCapacity (L i) x y) =
        ∑ z, interfaceCapacity (R i) y z := by
      rw [interfaceCapacity_column, interfaceCapacity_row, hY i y]
    have hc := (endpointReserve_capacities (L i) (R i) (Q.val i) (k + 2) δ
      hk hn hδ hthreshold (hdL i) (hdR i) (hQmat Q i)).2
    convert reserve_residual_reconstructs_right (interfaceCapacity (L i))
      (interfaceCapacity (R i)) (endpointReserve (L i) (R i) (Q.val i))
      (k + 2) (by linarith) hc hb y z using 1 <;> dsimp only [ρ, S]
    congr 1
    funext x
    congr 2 <;> ring

set_option maxHeartbeats 800000 in
theorem cyclic_interfaces_fractional_weighting {k : ℕ} {X Y : Type*}
    [Fintype X] [Fintype Y] [Nonempty X]
    (L : Fin (k + 2) → X → Y → Prop) (R : Fin (k + 2) → Y → X → Prop)
    (δ : ℝ) (hn : 0 < Fintype.card Y)
    (hthreshold : (k + 2 : ℝ) * Fintype.card Y ≤ (2 * (k + 2) - 1) * δ)
    (hdL : ∀ i x, δ ≤ (Finset.univ.filter (L i x)).card)
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
      (∀ p, 0 < ω p → ∀ i, (p i).2.2 = (p (finRotate (k + 2) i)).1) := by
  obtain ⟨_, ω, hω, ht, hL, hR, hc, _, _⟩ :=
    cyclic_interfaces_fractional_weighting_with_formula L R δ hn hthreshold hdL hY hX
  exact ⟨ω, hω, ht, hL, hR, hc⟩

end Oberwolfach

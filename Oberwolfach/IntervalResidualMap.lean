module

public import Oberwolfach.EndpointReserve
public import Oberwolfach.ResidualEndpoint

@[expose] public section

/-! The continuous residual endpoint map for actual unweighted interfaces. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def interfaceCapacity {X Y : Type*} (L : X → Y → Prop) : X → Y → ℝ :=
  fun x y => if L x y then 1 else 0

theorem interfaceCapacity_row {X Y : Type*} [Fintype Y]
    (L : X → Y → Prop) (x : X) :
    (∑ y, interfaceCapacity L x y) = (Finset.univ.filter (L x)).card := by
  simp [interfaceCapacity]

theorem interfaceCapacity_column {X Y : Type*} [Fintype X]
    (L : X → Y → Prop) (y : Y) :
    (∑ x, interfaceCapacity L x y) = (Finset.univ.filter (fun x => L x y)).card := by
  simp [interfaceCapacity]

theorem intervalCommon_pos {X Y Z : Type*} [Fintype Y]
    (L : X → Y → Prop) (R : Y → Z → Prop) (k δ : ℝ)
    (hk : 2 ≤ k) (hn : 0 < Fintype.card Y) (hδ : 0 ≤ δ)
    (hthreshold : k * Fintype.card Y ≤ (2 * k - 1) * δ)
    (hdL : ∀ x, δ ≤ (Finset.univ.filter (L x)).card)
    (hdR : ∀ z, δ ≤ (Finset.univ.filter (fun y => R y z)).card)
    (x : X) (z : Z) :
    0 < intervalCommon L R x z := by
  have hden := (reserve_capacity_inequality hk (by exact_mod_cast hn) hδ hthreshold (hdL x)).1
  have hc : ((Finset.univ.filter (L x)).card : ℝ) +
      (Finset.univ.filter (fun y => R y z)).card ≤
      (intervalCommon L R x z : ℝ) + Fintype.card Y := by
    exact_mod_cast intervalCommon_lower L R x z
  have hp : (0 : ℝ) < intervalCommon L R x z := by linarith [hdR z]
  exact_mod_cast hp

theorem endpointReserve_capacities {X Y Z : Type*}
    [Fintype X] [Fintype Y] [Fintype Z]
    (L : X → Y → Prop) (R : Y → Z → Prop) (Q : X → Z → ℝ) (k δ : ℝ)
    (hk : 2 ≤ k) (hn : 0 < Fintype.card Y) (hδ : 0 ≤ δ)
    (hthreshold : k * Fintype.card Y ≤ (2 * k - 1) * δ)
    (hdL : ∀ x, δ ≤ (Finset.univ.filter (L x)).card)
    (hdR : ∀ z, δ ≤ (Finset.univ.filter (fun y => R y z)).card)
    (hQ : Q ∈ transportMatrices
      (fun x => (Finset.univ.filter (L x)).card / k)
      (fun z => (Finset.univ.filter (fun y => R y z)).card / k)) :
    (∀ x y, (∑ z, endpointReserve L R Q x y z) ≤ interfaceCapacity L x y) ∧
    (∀ y z, (∑ x, endpointReserve L R Q x y z) ≤ interfaceCapacity R y z) := by
  constructor
  · intro x y
    by_cases hxy : L x y
    · simp only [interfaceCapacity, hxy, ite_true]
      exact endpointReserve_left_le L R Q _ k δ hk hn hδ hthreshold hQ.1 hQ.2.1
        (fun _ => rfl) hdL hdR x y
    · simp [interfaceCapacity, endpointReserve, hxy]
  · intro y z
    by_cases hyz : R y z
    · simp only [interfaceCapacity, hyz, ite_true]
      exact endpointReserve_right_le L R Q _ k δ hk hn hδ hthreshold hQ.1 hQ.2.2
        (fun _ => rfl) hdR hdL y z
    · simp [interfaceCapacity, endpointReserve, hyz]

def intervalResidualMap {X Y Z : Type*}
    [Fintype X] [Fintype Y] [Fintype Z]
    (L : X → Y → Prop) (R : Y → Z → Prop) (k : ℝ)
    (Q : X → Z → ℝ) : X → Z → ℝ :=
  scaledResidualEndpoint (interfaceCapacity L) (interfaceCapacity R)
    (endpointReserve L R Q) k

theorem intervalResidualMap_mem {X Y Z : Type*}
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
      (fun z => (Finset.univ.filter (fun y => R y z)).card / k)) :
    intervalResidualMap L R k Q ∈ transportMatrices
      (fun x => (Finset.univ.filter (L x)).card / k)
      (fun z => (Finset.univ.filter (fun y => R y z)).card / k) := by
  obtain ⟨hleft, hright⟩ := endpointReserve_capacities L R Q k δ hk hn hδ hthreshold hdL hdR hQ
  have hc := intervalCommon_pos L R k δ hk hn hδ hthreshold hdL hdR
  apply scaledResidualEndpoint_mem (interfaceCapacity L) (interfaceCapacity R)
    (endpointReserve L R Q) _ _ k (by linarith) hleft hright
  · intro y
    rw [interfaceCapacity_column, interfaceCapacity_row, hbal y]
  · exact interfaceCapacity_row L
  · exact interfaceCapacity_column R
  · intro x
    rw [Finset.sum_comm]
    simp_rw [endpointReserve_endpoints L R Q hc]
    exact hQ.2.1 x
  · intro z
    rw [Finset.sum_comm]
    simp_rw [endpointReserve_endpoints L R Q hc]
    exact hQ.2.2 z

set_option maxHeartbeats 800000 in
theorem intervalResidualMap_continuous {X Y Z : Type*}
    [Fintype X] [Fintype Y] [Fintype Z]
    (L : X → Y → Prop) (R : Y → Z → Prop) (k δ : ℝ)
    (hk : 2 ≤ k) (hn : 0 < Fintype.card Y) (hδ : 0 ≤ δ)
    (hthreshold : k * Fintype.card Y ≤ (2 * k - 1) * δ)
    (hdL : ∀ x, δ ≤ (Finset.univ.filter (L x)).card)
    (hdR : ∀ z, δ ≤ (Finset.univ.filter (fun y => R y z)).card)
    (hbal : ∀ y, (Finset.univ.filter (fun x => L x y)).card =
      (Finset.univ.filter (R y)).card) :
    Continuous (fun Q : transportMatrices
      (fun x => (Finset.univ.filter (L x)).card / k)
      (fun z => (Finset.univ.filter (fun y => R y z)).card / k) =>
      intervalResidualMap L R k Q.val) := by
  let T := transportMatrices
    (fun x => (Finset.univ.filter (L x)).card / k)
    (fun z => (Finset.univ.filter (fun y => R y z)).card / k)
  change Continuous (fun Q : T => scaledResidualEndpoint
    (interfaceCapacity L) (interfaceCapacity R) (endpointReserve L R Q.val) k)
  refine scaledResidualEndpoint_continuous (T := T)
    (interfaceCapacity L) (interfaceCapacity R)
    (fun Q : T => endpointReserve L R Q.val) k ?_ ?_ ?_ ?_
  · exact (endpointReserve_continuous L R).comp continuous_subtype_val
  · intro Q
    exact (endpointReserve_capacities L R Q.val k δ hk hn hδ hthreshold hdL hdR Q.property).1
  · intro Q
    exact (endpointReserve_capacities L R Q.val k δ hk hn hδ hthreshold hdL hdR Q.property).2
  · intro y
    rw [interfaceCapacity_column, interfaceCapacity_row, hbal y]

end Oberwolfach

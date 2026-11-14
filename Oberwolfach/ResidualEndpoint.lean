module

public import Oberwolfach.TransportMatrices
public import Oberwolfach.ResidualPaths

@[expose] public section

/-! Residual endpoint matrices after a capacity-respecting reserve. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach

def residualLeft {X Y Z : Type*} [Fintype Z]
    (A : X → Y → ℝ) (ρ : X → Y → Z → ℝ) : X → Y → ℝ :=
  fun x y => A x y - ∑ z, ρ x y z

def residualRight {X Y Z : Type*} [Fintype X]
    (B : Y → Z → ℝ) (ρ : X → Y → Z → ℝ) : Y → Z → ℝ :=
  fun y z => B y z - ∑ x, ρ x y z

theorem residual_interfaces_balanced {X Y Z : Type*}
    [Fintype X] [Fintype Z]
    (A : X → Y → ℝ) (B : Y → Z → ℝ) (ρ : X → Y → Z → ℝ)
    (hbal : ∀ y, ∑ x, A x y = ∑ z, B y z) (y : Y) :
    (∑ x, residualLeft A ρ x y) = ∑ z, residualRight B ρ y z := by
  unfold residualLeft residualRight
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, hbal y, Finset.sum_comm]

def scaledResidualPath {X Y Z : Type*} [Fintype X] [Fintype Z]
    (A : X → Y → ℝ) (B : Y → Z → ℝ) (ρ : X → Y → Z → ℝ)
    (k : ℝ) (x : X) (y : Y) (z : Z) : ℝ :=
  residualPath (residualLeft A ρ) (residualRight B ρ) x y z / (k - 1)

def scaledResidualEndpoint {X Y Z : Type*}
    [Fintype X] [Fintype Y] [Fintype Z]
    (A : X → Y → ℝ) (B : Y → Z → ℝ) (ρ : X → Y → Z → ℝ)
    (k : ℝ) : X → Z → ℝ :=
  fun x z => ∑ y, scaledResidualPath A B ρ k x y z

theorem scaledResidualEndpoint_mem {X Y Z : Type*}
    [Fintype X] [Fintype Y] [Fintype Z]
    (A : X → Y → ℝ) (B : Y → Z → ℝ) (ρ : X → Y → Z → ℝ)
    (dX : X → ℝ) (dZ : Z → ℝ) (k : ℝ) (hk : 1 < k)
    (hleft : ∀ x y, (∑ z, ρ x y z) ≤ A x y)
    (hright : ∀ y z, (∑ x, ρ x y z) ≤ B y z)
    (hbal : ∀ y, ∑ x, A x y = ∑ z, B y z)
    (hA : ∀ x, ∑ y, A x y = dX x)
    (hB : ∀ z, ∑ y, B y z = dZ z)
    (hρX : ∀ x, (∑ y, ∑ z, ρ x y z) = dX x / k)
    (hρZ : ∀ z, (∑ y, ∑ x, ρ x y z) = dZ z / k) :
    scaledResidualEndpoint A B ρ k ∈
      transportMatrices (fun x => dX x / k) (fun z => dZ z / k) := by
  have hL : ∀ x y, 0 ≤ residualLeft A ρ x y := fun x y => sub_nonneg.mpr (hleft x y)
  have hR : ∀ y z, 0 ≤ residualRight B ρ y z := fun y z => sub_nonneg.mpr (hright y z)
  have hbal' := residual_interfaces_balanced A B ρ hbal
  have hk1 : 0 < k - 1 := by linarith
  have hk0 : k ≠ 0 := by linarith
  have hid (d : ℝ) : (d - d / k) / (k - 1) = d / k := by
    apply (div_eq_iff hk1.ne').mpr
    field_simp
  refine ⟨?_, ?_, ?_⟩
  · intro x z
    exact Finset.sum_nonneg fun y _ =>
      div_nonneg (residualPath_bounds _ _ hL hR hbal' x y z).1 hk1.le
  · intro x
    unfold scaledResidualEndpoint scaledResidualPath
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_div, residualPath_left_load _ _ hL hbal']
    unfold residualLeft
    rw [Finset.sum_sub_distrib, hA x, hρX x, hid]
  · intro z
    unfold scaledResidualEndpoint scaledResidualPath
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_div, residualPath_right_load _ _ hR hbal']
    unfold residualRight
    rw [Finset.sum_sub_distrib, hB z, hρZ z, hid]

theorem scaledResidualEndpoint_continuous {T X Y Z : Type*} [TopologicalSpace T]
    [Fintype X] [Fintype Y] [Fintype Z]
    (A : X → Y → ℝ) (B : Y → Z → ℝ) (ρ : T → X → Y → Z → ℝ) (k : ℝ)
    (hρ : Continuous ρ)
    (hleft : ∀ t x y, (∑ z, ρ t x y z) ≤ A x y)
    (hright : ∀ t y z, (∑ x, ρ t x y z) ≤ B y z)
    (hbal : ∀ y, ∑ x, A x y = ∑ z, B y z) :
    Continuous (fun t => scaledResidualEndpoint A B (ρ t) k) := by
  have hcont := residualPath_continuous
    (fun t => residualLeft A (ρ t)) (fun t => residualRight B (ρ t))
    (by intro x y; unfold residualLeft; fun_prop)
    (by intro y z; unfold residualRight; fun_prop)
    (fun t x y => sub_nonneg.mpr (hleft t x y))
    (fun t y z => sub_nonneg.mpr (hright t y z))
    (fun t => residual_interfaces_balanced A B (ρ t) hbal)
  unfold scaledResidualEndpoint scaledResidualPath
  fun_prop

theorem reserve_residual_reconstructs_left {X Y Z : Type*}
    [Fintype X] [Fintype Z]
    (A : X → Y → ℝ) (B : Y → Z → ℝ) (ρ : X → Y → Z → ℝ)
    (k : ℝ) (hk : 1 < k)
    (hleft : ∀ x y, (∑ z, ρ x y z) ≤ A x y)
    (hbal : ∀ y, ∑ x, A x y = ∑ z, B y z)
    (x : X) (y : Y) :
    (∑ z, (ρ x y z + (k - 1) * scaledResidualPath A B ρ k x y z)) = A x y := by
  have hk' : k - 1 ≠ 0 := by linarith
  unfold scaledResidualPath
  simp_rw [mul_div_cancel₀ _ hk']
  have hL : ∀ x y, 0 ≤ residualLeft A ρ x y := fun x y => sub_nonneg.mpr (hleft x y)
  have hload := residualPath_left_load (residualLeft A ρ) (residualRight B ρ) hL
    (residual_interfaces_balanced A B ρ hbal) x y
  rw [Finset.sum_add_distrib, hload]
  unfold residualLeft
  ring

theorem reserve_residual_reconstructs_right {X Y Z : Type*}
    [Fintype X] [Fintype Z]
    (A : X → Y → ℝ) (B : Y → Z → ℝ) (ρ : X → Y → Z → ℝ)
    (k : ℝ) (hk : 1 < k)
    (hright : ∀ y z, (∑ x, ρ x y z) ≤ B y z)
    (hbal : ∀ y, ∑ x, A x y = ∑ z, B y z)
    (y : Y) (z : Z) :
    (∑ x, (ρ x y z + (k - 1) * scaledResidualPath A B ρ k x y z)) = B y z := by
  have hk' : k - 1 ≠ 0 := by linarith
  unfold scaledResidualPath
  simp_rw [mul_div_cancel₀ _ hk']
  have hR : ∀ y z, 0 ≤ residualRight B ρ y z := fun y z => sub_nonneg.mpr (hright y z)
  have hload := residualPath_right_load (residualLeft A ρ) (residualRight B ρ) hR
    (residual_interfaces_balanced A B ρ hbal) y z
  rw [Finset.sum_add_distrib, hload]
  unfold residualRight
  ring

end Oberwolfach

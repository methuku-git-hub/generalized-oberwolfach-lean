module

public import Oberwolfach.LongAlignedResidualError

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem long_three_residual_error_alignment
    (epsOrd epsParent ζOrd ξParent ξSeed:ℝ)
    (heps:0<epsOrd) (hParent:epsParent≤epsOrd)
    (hζ:0≤ζOrd) (hζeps:ζOrd≤epsOrd/8)
    (hξParent:0≤ξParent) (hParentRate:4*ξParent≤epsParent/2)
    (hξSeed:0≤ξSeed) (hSeedRate:4*ξSeed≤epsOrd/2):
    ∃ξ:ℝ,0≤ξ ∧ 4*ξ≤epsOrd/2 ∧ ζOrd≤ξ ∧ ξParent≤ξ ∧ ξSeed≤ξ ∧
      ∀n:ℕ,ζOrd*n≤ξ*n ∧ ξParent*n≤ξ*n ∧ ξSeed*n≤ξ*n := by
  let ξ:=max ζOrd (max ξParent ξSeed)
  have hζb:4*ζOrd≤epsOrd/2:=by linarith
  have hParentBound:4*ξParent≤epsOrd/2:=by linarith
  have hbound0:ξ≤epsOrd/8:=by
    dsimp [ξ]
    apply max_le hζeps
    apply max_le <;> linarith
  have hbound:4*ξ≤epsOrd/2:=by linarith
  have hζξ:ζOrd≤ξ:=by dsimp [ξ];exact le_max_left _ _
  have hpξ:ξParent≤ξ:=by dsimp [ξ];exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hsξ:ξSeed≤ξ:=by dsimp [ξ];exact le_trans (le_max_right _ _) (le_max_right _ _)
  refine ⟨ξ,hζ.trans hζξ,hbound,hζξ,hpξ,hsξ,?_⟩
  intro n
  exact ⟨mul_le_mul_of_nonneg_right hζξ (Nat.cast_nonneg n),mul_le_mul_of_nonneg_right hpξ (Nat.cast_nonneg n),mul_le_mul_of_nonneg_right hsξ (Nat.cast_nonneg n)⟩
end Oberwolfach

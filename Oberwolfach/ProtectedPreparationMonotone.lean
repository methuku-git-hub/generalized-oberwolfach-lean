module

public import Oberwolfach.ProtectedFactorPreparation
public import Oberwolfach.CommonEvents

@[expose] public section
/-! Shrinking the permitted perturbation, enlarging the fixed vertex set, or
raising the edge budget preserves protected preparation on the same sample. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem protected_factor_preparation_mono {n m:ℕ}
    (P S₀:SimpleGraph (Fin n)) (F:Fin m→SimpleGraph (Fin n))
    (I J:Finset (Fin n)) (ξ ζ:ℝ) (B C:ℕ)
    (hIJ:I⊆J) (hξ:ζ≤ξ) (hBC:B≤C)
    (h:ProtectedFactorPreparation P S₀ I ξ B F):
    ProtectedFactorPreparation P S₀ J ζ C F :=by
  obtain ⟨A,hA,hsize,hprep⟩:=h
  refine ⟨A,hA,hsize.trans hBC,?_⟩
  intro S hS hregular hAS hagree hchange
  apply hprep S hS hregular hAS
  · intro x hx y hy
    exact hagree x (hIJ hx) y (hIJ hy)
  · intro x
    exact (hchange x).trans (mul_le_mul_of_nonneg_right hξ (Nat.cast_nonneg n))

theorem protected_factor_preparation_probability_mono {n m:ℕ} {Ω:Type} [Fintype Ω]
    (μ:FiniteLaw Ω) (P:SimpleGraph (Fin n)) (sample:Ω→SimpleGraph (Fin n))
    (F:Fin m→SimpleGraph (Fin n)) (I J:Finset (Fin n)) (ξ ζ:ℝ) (B C:ℕ)
    (hIJ:I⊆J) (hξ:ζ≤ξ) (hBC:B≤C):
    μ.probability (fun ω=>ProtectedFactorPreparation P (sample ω) I ξ B F)≤
      μ.probability (fun ω=>ProtectedFactorPreparation P (sample ω) J ζ C F) :=by
  apply finiteLaw_probability_mono
  intro ω h
  exact protected_factor_preparation_mono P (sample ω) F I J ξ ζ B C hIJ hξ hBC h
end Oberwolfach

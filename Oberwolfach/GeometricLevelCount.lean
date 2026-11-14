module

public import Oberwolfach.VortexUniformEvents

@[expose] public section

/-! Polynomial-size bounds for the actual fixed family of vortex levels.
These discharge the family-size input of global retention from a positive
geometrically decreasing integer scale. -/
set_option autoImplicit false
namespace Oberwolfach

theorem geometric_level_count_le (M : ℕ→ℕ) (L : ℕ) (η : ℝ) (hη : η<1)
    (hpos : ∀ i≤L,1≤M i) (hstep : ∀ i<L,(M (i+1):ℝ)≤η*M i) :
    L+1≤M 0 := by
  have hdec (i : ℕ) (hi : i<L) : M (i+1)+1≤M i := by
    have hposR : (0:ℝ)<M i := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (hpos i (by omega)))
    have hh := (hstep i hi).trans_lt (by simpa only [one_mul] using mul_lt_mul_of_pos_right hη hposR)
    have hh' : M (i+1)<M i := by exact_mod_cast hh
    omega
  have hsum : ∀ i≤L,M i+i≤M 0 := by
    intro i
    induction i with
    | zero=>intro hi;omega
    | succ i ih=>
      intro hi
      have hp := ih (by omega)
      have hs := hdec i (by omega)
      omega
  have hh := hsum L le_rfl
  have hp := hpos L le_rfl
  omega

theorem geometric_restriction_family_quadratic (M : ℕ→ℕ) (L n k : ℕ) (η : ℝ)
    (hη : η<1) (hpos : ∀ i≤L,1≤M i) (hstep : ∀ i<L,(M (i+1):ℝ)≤η*M i)
    (hM : M 0≤n) (hk : k≤n) :
    ((Fintype.card (Fin k×Fin (L+1))):ℝ)≤(n:ℝ)^(2:ℝ) := by
  have hL := (geometric_level_count_le M L η hη hpos hstep).trans hM
  have hh := Nat.mul_le_mul hk hL
  simp only [Fintype.card_prod,Fintype.card_fin,Nat.cast_mul,Real.rpow_two]
  have hhR : (k:ℝ)*(L+1:ℕ)≤(n:ℝ)*n := by exact_mod_cast hh
  simpa only [pow_two] using hhR

end Oberwolfach

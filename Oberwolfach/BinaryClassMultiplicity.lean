module

public import Mathlib.Tactic

@[expose] public section
/-! The chosen class and its complement have the exact integral half-degrees
required by the protected binary partition. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach

def binaryClassMultiplicity (D N:ℕ):Fin 2→ℕ:=![N,D/2-N]

theorem binary_class_multiplicity_exact
    (D N:ℕ) (ρ:ℝ) (heven:Even D) (hρhi:ρ≤1) (hsize:ρ*D=2*N):
    (∑i,binaryClassMultiplicity D N i)=D/2 ∧
      ρ/2*D=(binaryClassMultiplicity D N 0:ℝ) ∧
      (1-ρ)/2*D=(binaryClassMultiplicity D N 1:ℝ):=by
  have hleR:(2:ℝ)*N≤D:=by
    have hh:=mul_le_mul_of_nonneg_right hρhi (Nat.cast_nonneg D)
    nlinarith
  have hle:2*N≤D:=by exact_mod_cast hleR
  have hDN:2*(D/2)=D:=by obtain ⟨k,hk⟩:=heven;omega
  have hN:N≤D/2:=by omega
  have hDNr:(2:ℝ)*(D/2:ℕ)=D:=by exact_mod_cast hDN
  have hsub:((D/2-N:ℕ):ℝ)=(D/2:ℕ)-N:=Nat.cast_sub hN
  constructor
  · simp [binaryClassMultiplicity,Fin.sum_univ_succ,hN]
  · constructor
    · simp [binaryClassMultiplicity];nlinarith
    · simp only [binaryClassMultiplicity,Matrix.cons_val_one,Matrix.cons_val_zero,hsub]
      nlinarith
end Oberwolfach

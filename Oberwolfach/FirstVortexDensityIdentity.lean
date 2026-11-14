module

public import Oberwolfach.FirstVortexDensityCardBounds

@[expose] public section
/-! The matching density is the actual initial index density, with its
mass identity and hub-cardinality consequences. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_density_identity
    {U:Type} [Fintype U] (n D:ℕ) (ρ₀:ℝ)
    (hD:0<D) (hρ₀:0<ρ₀) (hlo:ρ₀≤ initialIndexDensity U D)
    (hhi:initialIndexDensity U D≤1) (hDhi:(D:ℝ)≤2*n):
    0< initialIndexDensity U D ∧
    initialIndexDensity U D*(D:ℝ)=2*Fintype.card U ∧
    0<Fintype.card U ∧ Fintype.card U≤n :=by
  have hDpos:(D:ℝ)≠0:=by exact_mod_cast (Nat.ne_of_gt hD)
  refine ⟨lt_of_lt_of_le hρ₀ hlo,?_,first_vortex_density_card_bounds n D ρ₀ hD hρ₀ hlo hhi hDhi⟩
  simp [initialIndexDensity,hDpos]
end Oberwolfach

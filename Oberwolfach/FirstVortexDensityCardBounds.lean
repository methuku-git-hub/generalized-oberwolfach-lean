module

public import Oberwolfach.Vortex

@[expose] public section
/-! The index-density assumptions already imply a nonempty hub class and
that the number of hubs does not exceed the ambient order. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_density_card_bounds
    {U:Type} [Fintype U] (n D:ℕ) (ρ₀:ℝ)
    (hD:0<D) (hρ₀:0<ρ₀) (hlo:ρ₀≤ initialIndexDensity U D)
    (hhi:initialIndexDensity U D≤1) (hDhi:(D:ℝ)≤2*n):
    0<Fintype.card U ∧ Fintype.card U≤n :=by
  have hDpos:(0:ℝ)<D:=by exact_mod_cast hD
  have hρpos:0< initialIndexDensity U D:=lt_of_lt_of_le hρ₀ hlo
  have hupos:(0:ℝ)<Fintype.card U:=by
    have h:= (div_pos_iff_of_pos_right hDpos).mp hρpos
    linarith
  have hupper:(2:ℝ)*Fintype.card U≤D:=by
    have h:2*(Fintype.card U:ℝ)/(D:ℝ)≤1:=by simpa [initialIndexDensity] using hhi
    have hh:2*(Fintype.card U:ℝ)≤1*(D:ℝ):=(div_le_iff₀ hDpos).mp h
    linarith
  constructor
  · exact_mod_cast hupos
  · have h:(Fintype.card U:ℝ)≤n:=by linarith
    exact_mod_cast h
end Oberwolfach

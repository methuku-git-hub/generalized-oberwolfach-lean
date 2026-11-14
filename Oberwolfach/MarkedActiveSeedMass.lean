module

public import Oberwolfach.Vortex

@[expose] public section
/-! The prescribed seed density supplies enough total mass for retention. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem marked_active_seed_mass_bound
    {V U:Type} [Fintype V] [Fintype U] (D:ℕ)
    (ρ₀ tstar t pret:ℝ) (hρ:0<ρ₀) (ht:0<tstar) (hn:0<Fintype.card V)
    (hD:(Fintype.card V:ℝ)/2≤D) (hρlo:ρ₀≤ initialIndexDensity U D)
    (htlo:tstar≤t) (hpret:pret≤ρ₀*tstar/4):
    pret*Fintype.card V≤t*Fintype.card U:=by
  have hn':(0:ℝ)<Fintype.card V:=by exact_mod_cast hn
  have hD':(0:ℝ)<D:=lt_of_lt_of_le (by linarith:(0:ℝ)<(Fintype.card V:ℝ)/2) hD
  have hρD:ρ₀*D≤2*(Fintype.card U:ℝ):=by
    have hh:=(le_div_iff₀ hD').mp hρlo
    simpa [initialIndexDensity] using hh
  have hcard:(ρ₀/4)*(Fintype.card V:ℝ)≤Fintype.card U:=by
    have hh:=mul_le_mul_of_nonneg_left hD hρ.le
    nlinarith
  have hU:(0:ℝ)≤Fintype.card U:=Nat.cast_nonneg _
  have hmass:=mul_le_mul_of_nonneg_right htlo hU
  have hh:=mul_le_mul_of_nonneg_left hcard ht.le
  have hp:=mul_le_mul_of_nonneg_right hpret hn'.le
  nlinarith
end Oberwolfach

module

public import Oberwolfach.VortexSizeBounds

@[expose] public section
/-! The paired-vortex density lower bound supplies the absolute hub mass
needed by the retained marked event, uniformly in the supplied marginals. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_vortex_hub_mass_lower
    {V U:Type} [Fintype V] [Fintype U] {G:SimpleGraph V} {D:ℕ}
    (hreg:G.IsRegularOfDegree D) (hn:0<Fintype.card V)
    (hD:(Fintype.card V:ℝ)/2≤D) (ρ₀:ℝ) (hρ:0<ρ₀)
    (hrlo:ρ₀ ≤ initialIndexDensity U D):
    ρ₀*(Fintype.card V:ℝ)/4≤Fintype.card U:=by
  have hnR:(0:ℝ)<Fintype.card V:=by exact_mod_cast hn
  have hDpos:(0:ℝ)<D:=by linarith
  have hscale:ρ₀*(D:ℝ)≤2*Fintype.card U:=by
    have hh:=(le_div_iff₀ hDpos).mp hrlo
    simpa [initialIndexDensity] using hh
  have hh:=mul_le_mul_of_nonneg_left hD (le_of_lt hρ)
  nlinarith

theorem marked_vortex_retention_mass
    {V U:Type} [Fintype V] [Fintype U] {G:SimpleGraph V} {D:ℕ}
    (hreg:G.IsRegularOfDegree D) (hn:0<Fintype.card V)
    (hD:(Fintype.card V:ℝ)/2≤D) (ρ₀ tstar pstar t₀:ℝ)
    (hρ:0<ρ₀) (ht:0<tstar) (hp:0≤pstar)
    (hrlo:ρ₀ ≤ initialIndexDensity U D) (hbound:pstar≤ρ₀*tstar/4) (htlo:tstar≤t₀):
    pstar*Fintype.card V≤t₀*Fintype.card U:=by
  have hu:=marked_vortex_hub_mass_lower hreg hn hD ρ₀ hρ hrlo
  have hn0:(0:ℝ)≤Fintype.card V:=Nat.cast_nonneg _
  have hu0:(0:ℝ)≤Fintype.card U:=Nat.cast_nonneg _
  have h1:=mul_le_mul_of_nonneg_right hbound hn0
  have h2:=mul_le_mul_of_nonneg_left hu (le_of_lt ht)
  have h3:=mul_le_mul_of_nonneg_right htlo hu0
  nlinarith
end Oberwolfach

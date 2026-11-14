module

public import Oberwolfach.LongFirstPrescribedAsymptotic
public import Oberwolfach.FirstVortexPrescribedHubDensity

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_first_prescribed_numerical_hypotheses
    (ρ₀ α b ε:ℝ) (m:ℕ) (hρ₀:0<ρ₀) (hb:0<b) (hαb:α/16≤b)
    (hbd:b≤((ρ₀/4)/40000)/16) (hm:0<m) (hmarg:4/(m:ℝ)≤b/2)
    (hε:ε≤(ρ₀/4)/80000):
    ∃N:ℕ,∀n≥N,∀{U:Type} [Fintype U] {G:SimpleGraph (Fin n)} {D:ℕ},
      G.IsRegularOfDegree D→0<n→(n:ℝ)/2≤D→ρ₀ ≤ initialIndexDensity U D→
      0<ρ₀/4 ∧ α/16≤b ∧ b≤((ρ₀/4)/40000)/16 ∧
      (ρ₀/4)*n≤Fintype.card U ∧ ε≤(ρ₀/4)/80000 ∧
      (n:ℝ)^(3/4:ℝ)≤(ρ₀/4)*n/80000 ∧
      (0:ℝ)<m ∧ 0≤b ∧ 4/(m:ℝ)≤b/2 ∧ 4*(n:ℝ)^(3/4:ℝ)≤b*n/2:=by
  obtain ⟨N,hN⟩:=long_first_prescribed_matching_asymptotic b (ρ₀/4) hb (by positivity)
  refine ⟨N,?_⟩
  intro n hn U _ G D hreg hnpos hD hrlo
  obtain ⟨hρ,hcard⟩:=first_vortex_prescribed_hub_density hreg hnpos hD ρ₀ hρ₀ hrlo
  obtain ⟨hpow,hpowρ⟩:=hN n hn
  refine ⟨hρ,hαb,hbd,hcard,hε,hpowρ,?_,hb.le,hmarg,hpow⟩
  exact_mod_cast hm
end Oberwolfach

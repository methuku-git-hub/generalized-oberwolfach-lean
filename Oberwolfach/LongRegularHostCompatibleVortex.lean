module

public import Oberwolfach.LongRegularHostVortex
public import Oberwolfach.MarkedVortexAbsorberCompatibleScales

@[expose] public section
/-! Choose the vortex tolerances after the absorber tolerance, then choose
its size before the allowed set and the regular host. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_regular_host_absorber_compatible_vortex
    (αHost αRef βmax εBal εRef εAbs ρ₀:ℝ)
    (hαHost:0<αHost) (hαRef:0<αRef) (hβmax:0<βmax)
    (hBal:0<εBal) (hRef:0<εRef) (hAbs:0<εAbs) (hρ₀:0<ρ₀) (d:ℕ):
    ∃εQ βQ:ℝ,0<εQ ∧ εQ<1/4 ∧ εQ≤εAbs ∧
      0<βQ ∧ βQ≤1/4 ∧ βQ≤αRef/4 ∧ βQ≤βmax ∧ βQ≤εBal/4 ∧ βQ≤εRef/4 ∧
    ∃m₀:ℕ,1≤m₀ ∧ ∀ (Allowed:Set ℕ),Allowed.Nonempty→(∀r∈Allowed,3≤r)→
    ∀n:ℕ,0<n→∀(U:Type) [Fintype U] (G:SimpleGraph (Fin n)) (D m:ℕ),
      G.IsRegularOfDegree D→(allowedThreshold Allowed+αHost)*n≤(D:ℝ)→
      ρ₀ ≤ initialIndexDensity U D→initialIndexDensity U D≤1→m₀≤m→m≤n→
      ∃Q:Vortex U G D βQ εQ m,∃π:Equiv.Perm (Fin n),
        (∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i) ∧
        (∀x l,0<l→l<2*d+1→(π^l) x≠x) := by
  obtain ⟨εQ,βQ,he,he1,heAbs,hb,hb1,hbα,hbmax,hbbal,hbref⟩:=
    marked_vortex_absorber_compatible_scales αRef βmax εBal εRef εAbs hαRef hβmax hBal hRef hAbs
  obtain ⟨m₀,hm₀,hvortex⟩:=long_regular_host_vortex_with_permutation αHost βQ εQ ρ₀ hαHost hb he he1 hρ₀ d
  exact ⟨εQ,βQ,he,he1,heAbs,hb,hb1,hbα,hbmax,hbbal,hbref,m₀,hm₀,hvortex⟩
end Oberwolfach

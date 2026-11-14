module

public import Oberwolfach.LongRegularHostNumericInputs
public import Oberwolfach.VortexPermutation

@[expose] public section
/-! A regular host at the original threshold has a vortex and a shared
short-cycle-free permutation, uniformly in the allowed length set. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_regular_host_vortex_with_permutation
    (α β ε ρ₀:ℝ) (hα:0<α) (hb:0<β) (he:0<ε) (he1:ε<1/4) (hρ₀:0<ρ₀) (d:ℕ):
    ∃m₀:ℕ,1≤m₀ ∧ ∀ (Allowed:Set ℕ),Allowed.Nonempty→(∀r∈Allowed,3≤r)→
    ∀n:ℕ,0<n→∀(U:Type) [Fintype U] (G:SimpleGraph (Fin n)) (D m:ℕ),
      G.IsRegularOfDegree D→(allowedThreshold Allowed+α)*n≤(D:ℝ)→
      ρ₀ ≤ initialIndexDensity U D→initialIndexDensity U D≤1→m₀≤m→m≤n→
      ∃Q:Vortex U G D β ε m,∃π:Equiv.Perm (Fin n),
        (∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i) ∧
        (∀x l,0<l→l<2*d+1→(π^l) x≠x) := by
  obtain ⟨m₀,hm₀,hvortex⟩:=vortex_with_permutation_exists (β:=β) (ε:=ε) (ρ₀:=ρ₀) hb he he1 hρ₀ (2*d+1)
  refine ⟨m₀,hm₀,?_⟩
  intro Allowed hAllowed hvalid n hn U _ G D m hreg hmin hρlo hρhi hm hmn
  have hnum:=long_regular_host_numeric_inputs n D hn U Allowed hAllowed hvalid α hα G hreg hmin
  obtain ⟨Q,π,hpres,_,hshort⟩:=hvortex (Fin n) U G D m hreg (by simpa using hnum.2.1) hρlo hρhi hm (by simpa using hmn)
  exact ⟨Q,π,hpres,hshort⟩
end Oberwolfach

module

public import Oberwolfach.LongFirstVortexProtectedGraph

@[expose] public section
/-! The existing reserved-list error cap also gives the protected partition
its required first-vortex graph degree bound. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_first_vortex_reserved_protected_graph
    {n:ℕ} {U:Type} [Fintype U] {P:SimpleGraph (Fin n)}
    {D m:ℕ} {β ε:ℝ} (Q:Vortex U P D β ε m)
    (α ρ:ℝ) (hα:0≤α) (hρ:0≤ρ) (hρ1:ρ≤1) (hε:0≤ε)
    (hεcap:ε≤((min α (1/4:ℝ))*(ρ/200)^2*(1/100)/16)/32):
    let I:=Q.extendedVertices 1
    let Z:=spanningRestriction (⊤:SimpleGraph (Fin n)) I;
    (∀x y,Z.Adj x y→x∈I ∧ y∈I) ∧
    (∀v,(Z.degree v:ℝ)≤(α/100000)*n) := by
  have hr0:0≤ρ/200:=by positivity
  have hr1:ρ/200≤1/2:=by linarith
  have hs:(ρ/200)^2≤1/4:=by nlinarith [sq_nonneg (ρ/200-1/2)]
  have hm0:0≤min α (1/4:ℝ):=le_min hα (by norm_num)
  have hm:min α (1/4:ℝ)≤α:=min_le_left _ _
  have hmprod:min α (1/4:ℝ)*(ρ/200)^2≤α/4:=by
    have h1:=mul_le_mul_of_nonneg_left hs hm0
    nlinarith
  have hsmall:ε≤α/100000:=by nlinarith
  exact long_first_vortex_protected_graph Q hε (α/100000) hsmall
end Oberwolfach

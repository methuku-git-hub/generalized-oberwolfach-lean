module

public import Oberwolfach.LongFirstVortexProtectedGraph
public import Oberwolfach.MarkedReferenceLevelThresholdMono
public import Oberwolfach.GraphSelectionDegrees

@[expose] public section
/-! The first vortex set and any later bounded protected graph jointly fit
the degree allowance for the balanced orientation. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_first_vortex_protected_union_budget
    (α ρ₀:ℝ) (B:ℕ) (hα:0<α) (hρ₀:0<ρ₀):
    ∃N:ℕ,1≤N ∧ ∀n:ℕ,N≤n→∀(U:Type) [Fintype U]
      (P:SimpleGraph (Fin n)) (D m:ℕ) (β ε:ℝ) (Q:Vortex U P D β ε m)
      (hε:0≤ε)
      (hcap:ε≤((min α (1/4:ℝ))*(ρ₀/200)^2*(1/100)/16)/32),
      let Z:=spanningRestriction (⊤:SimpleGraph (Fin n)) (Q.extendedVertices 1);
      ∀A:SimpleGraph (Fin n),(∀v,A.degree v≤B)→
        ∀v,((Z⊔A).degree v:ℝ)≤(α*(ρ₀/200)^2/16)*n := by
  let c:ℝ:=α*(ρ₀/200)^2/32
  have hc:0<c:=by dsimp [c];positivity
  obtain ⟨N,hN,hSize⟩:=bounded_card_fits_two_linear_reserves B c c hc hc
  refine ⟨N,hN,?_⟩
  intro n hn U _ P D m β ε Q hε hcap Z A hA v
  have hB:(B:ℝ)≤c*n:=by simpa only [min_self] using hSize n hn
  have hmin:min α (1/4:ℝ)≤α:=min_le_left _ _
  have hs:0≤(ρ₀/200)^2:=sq_nonneg _
  have hprod:min α (1/4:ℝ)*(ρ₀/200)^2≤α*(ρ₀/200)^2:=mul_le_mul_of_nonneg_right hmin hs
  have hεc:ε≤c:=by dsimp [c] at *; nlinarith
  have hZ:= (long_first_vortex_protected_graph Q hε c hεc).2 v
  have hA':(A.degree v:ℝ)≤c*n:=(by exact_mod_cast hA v : (A.degree v:ℝ)≤B).trans hB
  have hUnion:=graph_degree_sup_le Z A v
  have hUnion':((Z⊔A).degree v:ℝ)≤(Z.degree v:ℝ)+(A.degree v:ℝ):=by exact_mod_cast hUnion
  dsimp only [c] at *
  linarith
end Oberwolfach

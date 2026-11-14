module

public import Oberwolfach.ApproximateSublinearMargin
public import Oberwolfach.ClassRequiredPreciseDegreeFromEdits
public import Oberwolfach.MarkedInitialInnerVertexBound
public import Oberwolfach.FirstVortexResidualTargetSize

@[expose] public section
/-! The actual required-graph degree fits the residual capacity budget from
its θ|I| term and the later matching and edit errors. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem first_vortex_precise_required_degree_budget
    (ε θ lam ξ a:ℝ) (d:ℕ) (hε:0≤ε) (hθ:0<θ) (ha:0<a)
    (hεsmall:ε≤a/8192) (hsmall:lam+ξ≤a*θ/4096):
    ∃N:ℕ,∀n:ℕ,N≤n→∀{U:Type} [Fintype U] {G Bad:SimpleGraph (Fin n)}
      {D m:ℕ} {β:ℝ} (Q:Vortex U G D β ε m),
      (∀v,(Bad.degree v:ℝ)≤2*θ*(Q.extendedVertices 1).card+(n:ℝ)^(3/4:ℝ)+(lam+ξ)*n+(6*d+2:ℕ))→
      ∀v,(Bad.degree v:ℝ)≤(a*θ/1024)*n :=by
  obtain ⟨N,hN⟩:=eventually_three_quarters_and_constant_le_linear (a*θ/4096) ((6*d+2:ℕ):ℝ) (by positivity)
  refine ⟨N,?_⟩
  intro n hn U _ G Bad D m β Q hdegree v
  have hI:((Q.extendedVertices 1).card:ℝ)≤ε*n:=by
    simpa only [Fintype.card_fin] using marked_initial_inner_vertex_bound Q hε
  have hI':=mul_le_mul_of_nonneg_left hI (by positivity:0≤2*θ)
  have hε':=mul_le_mul_of_nonneg_right hεsmall (by positivity:0≤θ*(n:ℝ))
  have hsmall':=mul_le_mul_of_nonneg_right hsmall (Nat.cast_nonneg n)
  have herr:=hN n hn
  have hh:=hdegree v
  nlinarith only [hI',hε',hsmall',herr,hh]
end Oberwolfach

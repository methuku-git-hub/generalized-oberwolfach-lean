module

public import Oberwolfach.FirstVortexMatchingScalePositive
public import Oberwolfach.VortexSizeBounds
public import Oberwolfach.ApproximateSublinearMargin

@[expose] public section
/-! An all-roots boundary test at ambient concentration scale becomes a
small multiple of the first-inner vertex set for sufficiently large hosts. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem first_vortex_all_roots_boundary_relative
    (ε c:ℝ) (hε:0<ε) (hc:0<c):
    ∃N:ℕ,1≤N ∧ ∀(V U:Type) [Fintype V] [Fintype U] [LinearOrder V]
      (G:SimpleGraph V) (D m:ℕ) (β:ℝ) (Q:Vortex U G D β ε m),
      N≤Fintype.card V→G.IsRegularOfDegree D→0<D→0<m→initialIndexDensity U D≤1→
      ∀d:ℕ,0<d→4/(d:ℝ)≤c→
      4*((Q.extendedIndices 1).card:ℝ)/d+4*(Fintype.card V:ℝ)^(3/4:ℝ)≤
        c*((Q.extendedVertices 1).card:ℝ) :=by
  obtain ⟨N,hN⟩:=eventually_three_quarters_and_constant_le_linear (c*ε/16) 0 (by positivity)
  refine ⟨max N 1,by omega,?_⟩
  intro V U _ _ _ G D m β Q hn hreg hD hm hρ d hd hdsmall
  have hn0:0<Fintype.card V:=by omega
  have hIndexNat:=Q.extended_index_size_upper hreg hn0 hD hε.le hρ 1
  have hIndex:(2:ℝ)*(Q.extendedIndices 1).card≤(Q.extendedVertices 1).card:=by exact_mod_cast hIndexNat
  have hInner:=Q.first_inner_vertex_size_lower_of_positive_terminal_size hε hm
  have hA:(0:ℝ)≤(Q.extendedVertices 1).card:=by positivity
  have hdpos:(0:ℝ)<d:=by exact_mod_cast hd
  have h2d:2/(d:ℝ)≤c/2:=by
    have heq:2/(d:ℝ)=(4/(d:ℝ))/2:=by ring
    linarith
  have hfirst:4*((Q.extendedIndices 1).card:ℝ)/d≤(c/2)*(Q.extendedVertices 1).card:=by
    have h1:=mul_le_mul_of_nonneg_left hIndex (show 0≤2/(d:ℝ) by positivity)
    have h2:=mul_le_mul_of_nonneg_right h2d hA
    calc
      4*((Q.extendedIndices 1).card:ℝ)/d = (2/(d:ℝ))*(2*(Q.extendedIndices 1).card) := by ring
      _ ≤ (2/(d:ℝ))*(Q.extendedVertices 1).card := h1
      _ ≤ _ := h2
  have hasym:=hN (Fintype.card V) (by omega)
  have hsecond:4*(Fintype.card V:ℝ)^(3/4:ℝ)≤(c/2)*(Q.extendedVertices 1).card:=by
    have hh:=mul_le_mul_of_nonneg_left hInner (show 0≤c/2 by positivity)
    nlinarith
  linarith
end Oberwolfach

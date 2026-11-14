module

public import Oberwolfach.FirstVortexAllRootsBoundaryRelative

@[expose] public section
/-! The selector's original all-hub boundary test also has first-inner
scale once spacing is chosen in terms of the earlier vortex scale. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem first_vortex_ambient_boundary_relative
    (ε c:ℝ) (hε:0<ε) (hc:0<c):
    ∃N:ℕ,1≤N ∧ ∀(V U:Type) [Fintype V] [Fintype U] [LinearOrder V]
      (G:SimpleGraph V) (D m:ℕ) (β:ℝ) (Q:Vortex U G D β ε m),
      N≤Fintype.card V→Fintype.card U≤Fintype.card V→0<m→
      ∀d:ℕ,0<d→4/(d:ℝ)≤c*ε/4→
      4*(Fintype.card U:ℝ)/d+4*(Fintype.card V:ℝ)^(3/4:ℝ)≤
        c*((Q.extendedVertices 1).card:ℝ) :=by
  obtain ⟨N,hN⟩:=eventually_three_quarters_and_constant_le_linear (c*ε/16) 0 (by positivity)
  refine ⟨max N 1,by omega,?_⟩
  intro V U _ _ _ G D m β Q hn hU hm d hd hspacing
  have hn0:(0:ℝ)≤Fintype.card V:=by positivity
  have hU':(Fintype.card U:ℝ)≤Fintype.card V:=by exact_mod_cast hU
  have hfirst:4*(Fintype.card U:ℝ)/d≤(c*ε/4)*Fintype.card V:=by
    have h1:=mul_le_mul_of_nonneg_left hU' (show 0≤4/(d:ℝ) by positivity)
    have h2:=mul_le_mul_of_nonneg_right hspacing hn0
    calc
      _ = (4/(d:ℝ))*Fintype.card U :=by ring
      _ ≤ (4/(d:ℝ))*Fintype.card V :=h1
      _ ≤ _ :=h2
  have hsub:=hN (Fintype.card V) (by omega)
  have hInner:=Q.first_inner_vertex_size_lower_of_positive_terminal_size hε hm
  have hcpos:0≤c:=hc.le
  nlinarith
end Oberwolfach

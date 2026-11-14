module

public import Oberwolfach.OrdinaryDeepCubicTolerance
public import Oberwolfach.VortexExtendedPowerBounds

@[expose] public section
/-! A third-level reserve is small enough for the explicit packing tolerance.
This is a size estimate; it does not replace the missing cover-down step. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_third_vortex_reserve_below_packing_tolerance
    (r:ℕ) (p a b c cap₀ cLinear:ℝ)
    (hp:0<p) (ha:0<a) (hb:0<b) (hc:0<c) (hcap:0<cap₀) (hLinear:0<cLinear):
    ∃εcap:ℝ,0<εcap ∧ εcap≤1 ∧ ∀ε:ℝ,0<ε→ε≤εcap→∀η:ℝ,
      cLinear*ordinarySafeCleanupScale r p (a*ε) (b*ε) (c*ε) (cap₀*ε^2)≤η→
    ∀(V U:Type) [Fintype V] [Fintype U],Fintype.card U≤Fintype.card V→
    ∀(G:SimpleGraph V) (D m:ℕ) (β:ℝ) (Q:Vortex U G D β ε m),
      (((Q.extendedVertices 3).card+(Q.extendedIndices 3).card:ℕ):ℝ)≤η*Fintype.card V :=by
  obtain ⟨εcap,hcap0,hcap1,hsmall⟩:=ordinary_deep_cubic_error_below_packing_tolerance r p a b c cap₀ cLinear 2 hp ha hb hc hcap hLinear (by norm_num)
  refine ⟨εcap,hcap0,hcap1,?_⟩
  intro ε hε hεcap η hη V U _ _ hUV G D m β Q
  have heps:2*ε^3≤η/2:=hsmall ε hε hεcap η hη
  obtain ⟨hV,hU⟩:=Q.extended_pair_power_size_bounds hε.le 3
  have hUV':(Fintype.card U:ℝ)≤Fintype.card V:=by exact_mod_cast hUV
  have hU':((Q.extendedIndices 3).card:ℝ)≤ε^3*Fintype.card V:=
    hU.trans (mul_le_mul_of_nonneg_left hUV' (by positivity))
  have hn:0≤(Fintype.card V:ℝ):=by positivity
  have hh:=mul_le_mul_of_nonneg_right heps hn
  have hη0:0≤η:=by nlinarith [hε]
  have hh':(η/2)*(Fintype.card V:ℝ)≤η*Fintype.card V:=by nlinarith only [mul_nonneg hη0 hn]
  push_cast
  nlinarith only [hV,hU',hh,hh']
end Oberwolfach

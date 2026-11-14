module

public import Oberwolfach.OrdinaryDeepCubicTolerance
public import Oberwolfach.OrdinaryVortexBufferedDomains
public import Oberwolfach.VortexProtectedGeometry

@[expose] public section
/-! The cubic reserve bound holds at every actual vortex parent, not only at
the initial host, under the original regularity and density assumptions. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_third_local_vortex_reserve_below_packing_tolerance
    (r:ℕ) (p a b c cap₀ cLinear:ℝ)
    (hp:0<p) (ha:0<a) (hb:0<b) (hc:0<c) (hcap:0<cap₀) (hLinear:0<cLinear):
    ∃εcap:ℝ,0<εcap ∧ εcap≤1 ∧ ∀ε:ℝ,0<ε→ε≤εcap→∀η:ℝ,
      cLinear*ordinarySafeCleanupScale r p (a*ε) (b*ε) (c*ε) (cap₀*ε^2)≤η→
    ∀(V U:Type) [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U],
    ∀(G:SimpleGraph V) (D m:ℕ) (β:ℝ) (Q:Vortex U G D β ε m),
    G.IsRegularOfDegree D→0<Fintype.card V→(Fintype.card V:ℝ)/2≤D→
    initialIndexDensity U D≤1→∀i,i<Q.length→
    ((ordinaryVortexBufferedVertices Q i 3).card:ℝ)+(ordinaryVortexBufferedHubs Q i 3).card≤
      η*Fintype.card (markedVortexVertexType Q i) :=by
  obtain ⟨εcap,hcap0,hcap1,hsmall⟩:=ordinary_deep_cubic_error_below_packing_tolerance r p a b c cap₀ cLinear 2 hp ha hb hc hcap hLinear (by norm_num)
  refine ⟨εcap,hcap0,hcap1,?_⟩
  intro ε hε hεcap η hη V U _ _ _ _ G D m β Q hreg hn hD hρhi i hi
  have hDpos:0<D:=by
    have hnR:(0:ℝ)<Fintype.card V:=by exact_mod_cast hn
    exact_mod_cast (show (0:ℝ)<D by linarith)
  have hupp:2*(Q.indices i).card≤(Q.vertices i).card:=
    Q.index_size_upper hreg hn hDpos hε.le hρhi hi.le
  have hU:Fintype.card (markedVortexHubType Q i)≤Fintype.card (markedVortexVertexType Q i):=by
    simp only [markedVortexHubType,markedVortexVertexType,Fintype.card_coe,Q.extendedIndices_eq hi.le,Q.extendedVertices_eq hi.le]
    omega
  have hbuf:=ordinary_vortex_buffered_card_bound Q hε.le i 3 hU
  have heps:2*ε^3≤η/2:=hsmall ε hε hεcap η hη
  have hn0:0≤(Fintype.card (markedVortexVertexType Q i):ℝ):=by positivity
  have hh:=mul_le_mul_of_nonneg_right heps hn0
  have hη0:0≤η:=by nlinarith [hε]
  have hh':(η/2)*(Fintype.card (markedVortexVertexType Q i):ℝ)≤η*Fintype.card (markedVortexVertexType Q i):=by
    nlinarith only [mul_nonneg hη0 hn0]
  exact hbuf.trans (by nlinarith only [hh,hh'])
end Oberwolfach

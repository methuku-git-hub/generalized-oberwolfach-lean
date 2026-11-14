module

public import Oberwolfach.OrdinaryVortexTriangleInnerSizeAndIndices

@[expose] public section
/-! A parent-level edit rate chosen after the vortex ratio yields the
relative inner-domain edit bound required by the triangle factors. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
variable {G:SimpleGraph V} {D m:ℕ} {β ε ρ₀:ℝ} (Q:Vortex U G D β ε m)

theorem ordinary_vortex_triangle_inner_edit_budget
    (hreg:G.IsRegularOfDegree D) (hn:0<Fintype.card V) (hD:(Fintype.card V:ℝ)/2≤D)
    (hρ:0<ρ₀) (hρlo:ρ₀ ≤ initialIndexDensity U D) (hρhi:initialIndexDensity U D≤1)
    (hβ:0≤β) (hβ1:β≤1/4) (hε:0<ε) (hm:0<m) (i:ℕ) (hi:i<Q.length)
    (lam rateParent Ledit:ℝ) (hlam:0≤lam) (hrate:rateParent≤lam*ε/4)
    (hEdit:Ledit≤rateParent*Fintype.card (markedVortexVertexType Q i⊕markedVortexHubType Q i)):
    Ledit≤lam*(markedVortexInnerVertices Q i).card:=by
  have hs:=(ordinary_vortex_triangle_inner_size_and_indices Q hreg hn hD hρ hρlo hρhi hβ hβ1 hε hm i hi).1
  have hn0:0≤(Fintype.card (markedVortexVertexType Q i⊕markedVortexHubType Q i):ℝ):=by positivity
  have hr:=mul_le_mul_of_nonneg_right hrate hn0
  have hm:=mul_le_mul_of_nonneg_left hs hlam
  nlinarith only [hEdit,hr,hm]
end Oberwolfach

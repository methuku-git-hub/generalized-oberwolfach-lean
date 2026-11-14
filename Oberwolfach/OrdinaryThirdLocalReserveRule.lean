module

public import Oberwolfach.OrdinaryThirdLocalVortexReserveTolerance

@[expose] public section
/-! Package the locally uniform third-reserve estimate for the ordered
packing-parameter selection. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def OrdinaryThirdLocalReserveRule (r:ℕ) (cLinear:ℝ):Prop :=
  ∀(p a b c cap₀:ℝ),0<p→0<a→0<b→0<c→0<cap₀→
  ∃εcap:ℝ,0<εcap ∧ εcap≤1 ∧ ∀ε:ℝ,0<ε→ε≤εcap→∀η:ℝ,
    cLinear*ordinarySafeCleanupScale r p (a*ε) (b*ε) (c*ε) (cap₀*ε^2)≤η→
  ∀(V U:Type) [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U],
  ∀(G:SimpleGraph V) (D m:ℕ) (β:ℝ) (Q:Vortex U G D β ε m),
  G.IsRegularOfDegree D→0<Fintype.card V→(Fintype.card V:ℝ)/2≤D→
  initialIndexDensity U D≤1→∀i,i<Q.length→
    ((ordinaryVortexBufferedVertices Q i 3).card:ℝ)+(ordinaryVortexBufferedHubs Q i 3).card≤
      η*Fintype.card (markedVortexVertexType Q i)

theorem ordinary_third_local_reserve_rule (r:ℕ) (cLinear:ℝ) (hLinear:0<cLinear):
    OrdinaryThirdLocalReserveRule r cLinear:=by
  intro p a b c cap₀ hp ha hb hc hcap
  exact ordinary_third_local_vortex_reserve_below_packing_tolerance r p a b c cap₀ cLinear hp ha hb hc hcap hLinear
end Oberwolfach

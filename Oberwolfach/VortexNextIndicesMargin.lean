module

public import Oberwolfach.VortexNextIndicesSmall

@[expose] public section
/-! Choosing the vortex contraction below a prescribed positive margin makes
the next set of hubs small enough for the protected-pair assignment. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem Vortex.next_indices_margin {V U:Type*} [Fintype V] [Fintype U]
    {G:SimpleGraph V} {D m:ℕ} {β ε κ:ℝ} (Q:Vortex U G D β ε m)
    (hreg:G.IsRegularOfDegree D) (hn:0<Fintype.card V) (hD:0<D)
    (he:0<ε) (hm:0<m) (hρ:initialIndexDensity U D≤1)
    (hκ:ε≤2*κ) {i:ℕ} (hi:i<Q.length):
    ((Q.indices (i+1)).card:ℝ)≤κ*(Q.vertices i).card:=by
  have hsmall:=Q.next_indices_small hreg hn hD he hm hρ hi
  have hc:(0:ℝ)≤(Q.vertices i).card:=by positivity
  have hh:=mul_le_mul_of_nonneg_right hκ hc
  linarith
end Oberwolfach

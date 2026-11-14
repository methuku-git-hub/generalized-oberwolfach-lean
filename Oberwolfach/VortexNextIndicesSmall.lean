module

public import Oberwolfach.VortexSizeBounds

@[expose] public section
/-! The next index set is small relative to the current vertex set, with an
explicit bound controlled by the freely chosen vortex contraction. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem Vortex.next_indices_small {V U:Type*} [Fintype V] [Fintype U]
    {G:SimpleGraph V} {D m:ℕ} {β ε:ℝ} (Q:Vortex U G D β ε m)
    (hreg:G.IsRegularOfDegree D) (hn:0<Fintype.card V) (hD:0<D)
    (he:0<ε) (hm:0<m) (hρ:initialIndexDensity U D≤1)
    {i:ℕ} (hi:i<Q.length):
    ((Q.indices (i+1)).card:ℝ)≤ε*(Q.vertices i).card/2:=by
  have hidx:=Q.index_size_upper hreg hn hD he.le hρ (show i+1≤Q.length by omega)
  have hidxR:(2:ℝ)*(Q.indices (i+1)).card≤(Q.vertices (i+1)).card:=by exact_mod_cast hidx
  have hv:((Q.vertices (i+1)).card:ℝ)≤ε*(Q.vertices i).card:=
    (Q.consecutive_size_bounds he hm hi).2
  linarith
end Oberwolfach

module

public import Oberwolfach.SaturatedVertexBound

@[expose] public section
/-! An assignment of a finite set of edges can saturate at most its total
size divided by the per-index capacity. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {E W:Type} [Fintype W] [DecidableEq E] [DecidableEq W]

theorem assigned_indices_saturation (T:Finset E) (f:E→W) (K:ℕ) (hK:0<K):
    let S:=Finset.univ.filter (fun w=>K≤(T.filter (fun e=>f e=w)).card);
    (K:ℝ)*(S.card:ℝ)≤T.card := by
  intro S
  let load:W→ℕ:=fun w=>(T.filter (fun e=>f e=w)).card
  have hsum:(∑ w:W,load w)=T.card:=by
    have hh:=Finset.sum_card_fiberwise_eq_card_filter T Finset.univ f
    simpa [load] using hh
  have hsumR:(∑ w:W,(load w:ℝ))=(T.card:ℝ):=by exact_mod_cast hsum
  have hK':(0:ℝ)<K:=by exact_mod_cast hK
  have hh:=saturated_vertex_count_bound load K (T.card:ℝ) hK' hsumR.le
  simpa [S,load] using hh
end Oberwolfach

module

public import Oberwolfach.SaturatedVertexBound

@[expose] public section
/-! Saturated labels counted from the actual finite set of free occurrences. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
open scoped BigOperators

theorem prescribed_embedding_saturated_actual_occurrences {X V:Type}
    [Fintype V] [DecidableEq V] (T:Finset X) (φ:X→V) (δ n:ℝ)
    (hδ:0<δ) (hn:0<n) (hT:(T.card:ℝ)≤δ*n^2):
    ((Finset.univ.filter (fun v=>Real.sqrt δ*n≤((T.filter (fun x=>φ x=v)).card:ℝ))).card:ℝ)≤Real.sqrt δ*n := by
  let f:V→ℕ:=fun v=>(T.filter (fun x=>φ x=v)).card
  have hsum:(∑ v:V,f v)=T.card:=by
    have hh:=Finset.sum_card_fiberwise_eq_card_filter T Finset.univ φ
    simpa [f] using hh
  have hused:(∑ v:V,(f v:ℝ))≤δ*n^2:=by
    have hh:((∑ v:V,f v:ℕ):ℝ)=(T.card:ℝ):=by exact_mod_cast hsum
    push_cast at hh
    linarith
  simpa [f] using prescribed_embedding_saturated_vertices f δ n hδ hn hused
end Oberwolfach

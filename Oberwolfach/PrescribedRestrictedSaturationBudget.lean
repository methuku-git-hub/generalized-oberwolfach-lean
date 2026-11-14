module

public import Oberwolfach.SaturatedVertexBound

@[expose] public section
/-! A second saturation test can track free occurrences in a selected hub
set. Its forbidden-vertex cost is controlled by that set's total use. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
open scoped BigOperators

theorem prescribed_restricted_saturation_budget
    {X V:Type} [Fintype V] [DecidableEq V] (T:Finset X) (φ:X→V)
    (a h n κ θ b:ℝ) (ha:0<a) (hκ:0<κ) (hn:0≤n) (hθ:0≤θ)
    (hh:0≤h) (hha:h≤a) (hθbudget:θ≤κ*b)
    (hT:(T.card:ℝ)≤θ*n*h):
    ((Finset.univ.filter (fun v=>κ*a≤((T.filter (fun x=>φ x=v)).card:ℝ))).card:ℝ)≤b*n :=by
  let f:V→ℕ:=fun v=>(T.filter (fun x=>φ x=v)).card
  have hsum:(∑v:V,f v)=T.card:=by
    have hh:=Finset.sum_card_fiberwise_eq_card_filter T Finset.univ φ
    simpa [f] using hh
  have hused:(∑v:V,(f v:ℝ))≤θ*n*h:=by
    have hh:((∑v:V,f v:ℕ):ℝ)=(T.card:ℝ):=by exact_mod_cast hsum
    push_cast at hh
    linarith
  have hsat:=saturated_vertex_count_bound f (κ*a) (θ*n*h) (by positivity) hused
  have hha':θ*n*h≤θ*n*a:=mul_le_mul_of_nonneg_left hha (mul_nonneg hθ hn)
  have hθ':θ*n*a≤(κ*b)*n*a:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hθbudget hn) ha.le
  have hprod:κ*a*((Finset.univ.filter (fun v=>κ*a≤((T.filter (fun x=>φ x=v)).card:ℝ))).card:ℝ)≤κ*a*(b*n):=by
    dsimp only [f] at hsat
    nlinarith
  exact (mul_le_mul_iff_left₀ (show 0<κ*a by positivity)).mp (by simpa only [mul_comm] using hprod)
end Oberwolfach

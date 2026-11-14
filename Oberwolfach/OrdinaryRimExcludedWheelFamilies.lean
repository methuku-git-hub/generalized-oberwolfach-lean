module

public import Oberwolfach.OrdinaryNonrootWheelLoss

@[expose] public section
/-! Uniform single-excluded-hub and single-excluded-vertex load bounds at
an edge whose endpoints remain. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_rim_excluded_wheel_families (Q F:SimpleGraph V) (H:V→U→Prop) (r:ℕ)
    (hr:2≤r) (hn:0<Fintype.card V) (hu:Fintype.card U≤Fintype.card V)
    (w:OrdinaryWheel Q F H r→ℝ) (B:ℝ) (hB:0≤B)
    (hw:∀C,0≤w C ∧ w C≤B/(Fintype.card V:ℝ)^(r-1))
    (T:Finset V) (W:Finset U) (x y:V) (hxy:x≠y) (hx:x∉T) (hy:y∉T):
    (∀u∈W,(∑C,if (ordinaryWheelRim C).Adj x y ∧ ordinaryWheelHub C=u then w C else 0)≤
      (r:ℝ)^4*B/Fintype.card V) ∧
    (∀z∈T,(∑C,if (ordinaryWheelRim C).Adj x y ∧ z∈(ordinaryWheelRim C).support then w C else 0)≤
      (r:ℝ)^4*B/Fintype.card V):=by
  have hr1:(1:ℝ)≤r:=by exact_mod_cast (show 1≤r by omega)
  have hpow:(r:ℝ)^3≤(r:ℝ)^4:=pow_le_pow_right₀ hr1 (by omega)
  have hnum:(r:ℝ)^3*B/Fintype.card V≤(r:ℝ)^4*B/Fintype.card V:=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hpow hB) (by positivity)
  constructor
  · intro u _
    exact ordinary_rim_excluded_hub_load Q F H r hr hn hu w B hB hw x y u
  · intro z hz
    have hxz:x≠z:=by intro he;subst z;exact hx hz
    have hyz:y≠z:=by intro he;subst z;exact hy hz
    exact (ordinary_rim_excluded_vertex_load Q F H r hr hn hu w B hB hw x y z hxy hxz hyz).trans hnum
end Oberwolfach

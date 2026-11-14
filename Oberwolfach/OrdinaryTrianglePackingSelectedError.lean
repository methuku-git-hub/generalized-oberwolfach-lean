module

public import Oberwolfach.OrdinaryRootFirstPackingExpandedInputs

@[expose] public section
/-! Name the triangle packing threshold and error at the parent margins that
are fixed before the triangle sampling tolerance is selected. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 24000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def ordinaryTrianglePackingThreshold (α:ℝ) (hα:0<α):ℕ :=
  Classical.choose (ordinary_root_first_packing_from_expanded_inputs 3 (by omega) α hα)

def ordinaryTrianglePackingError
    (α:ℝ) (hα:0<α) (k:ℕ) (hk:ordinaryTrianglePackingThreshold α hα≤k)
    (βH c B ω pstar δ h:ℝ)
    (hβH:0<βH) (hc:0<c) (hB:0<B) (hω:0<ω) (hp:0<pstar)
    (hδ:0<δ) (hδ1:δ<1/4) (hh:0<h):ℝ :=
  Classical.choose ((Classical.choose_spec (ordinary_root_first_packing_from_expanded_inputs 3 (by omega) α hα))
    k hk ω (βH/8) (c*(1-δ)^(3-1)) (B/(ω*pstar^(2*3-1))) (h/2) (δ/2)
    hω (by positivity) (by exact mul_pos hc (pow_pos (by linarith) _)) (by positivity) (by positivity) (by positivity) (by linarith))

theorem ordinary_triangle_packing_selected_error_pos
    (α:ℝ) (hα:0<α) (k:ℕ) (hk:ordinaryTrianglePackingThreshold α hα≤k)
    (βH c B ω pstar δ h:ℝ)
    (hβH:0<βH) (hc:0<c) (hB:0<B) (hω:0<ω) (hp:0<pstar)
    (hδ:0<δ) (hδ1:δ<1/4) (hh:0<h):
    0<ordinaryTrianglePackingError α hα k hk βH c B ω pstar δ h hβH hc hB hω hp hδ hδ1 hh:=by
  exact (Classical.choose_spec ((Classical.choose_spec (ordinary_root_first_packing_from_expanded_inputs 3 (by omega) α hα))
    k hk ω (βH/8) (c*(1-δ)^(3-1)) (B/(ω*pstar^(2*3-1))) (h/2) (δ/2)
    hω (by positivity) (by exact mul_pos hc (pow_pos (by linarith) _)) (by positivity) (by positivity) (by positivity) (by linarith))).1
end Oberwolfach

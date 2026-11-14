module

public import Oberwolfach.MarkedParentConfigurationHierarchy

@[expose] public section
/-! Compatible parent neighbourhood and spoke-agreement tolerances under
arbitrary positive upper caps. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem marked_parent_neighbourhood_parameter_choice
    (r:ℕ) (κ x tolcap ζcap:ℝ)
    (hκ:0<κ) (hx:0<x) (htolcap:0<tolcap) (hζcap:0<ζcap):
    ∃ tol ζ:ℝ,0<tol ∧ tol≤tolcap ∧ 0<ζ ∧ ζ≤ζcap ∧
      tol+(r+12:ℕ)*ζ≤κ/4 ∧ tol+(r+12:ℕ)*ζ≤x/2 ∧ ζ≤κ/4:=by
  let b:=min κ x
  have hb:0<b:=by dsimp [b];positivity
  have hbκ:b≤κ:=min_le_left _ _
  have hbx:b≤x:=min_le_right _ _
  let tol:=min tolcap (b/16)
  let ζ:=min ζcap (b/(16*(r+13:ℕ)))
  have htol:0<tol:=by dsimp [tol];positivity
  have hζ:0<ζ:=by dsimp [ζ];positivity
  have htcap:tol≤tolcap:=min_le_left _ _
  have ht:tol≤b/16:=min_le_right _ _
  have hzcap:ζ≤ζcap:=min_le_left _ _
  have hz:ζ≤b/(16*(r+13:ℕ)):=min_le_right _ _
  have hprod:ζ*(16*(r+13:ℕ))≤b:=(le_div_iff₀ (by positivity)).mp hz
  have hless:((r+12:ℕ):ℝ)≤(r+13:ℕ):=by exact_mod_cast (show r+12≤r+13 by omega)
  have hloss:((r+12:ℕ):ℝ)*ζ≤b/16:=by
    nlinarith [mul_nonneg hζ.le (sub_nonneg.mpr hless)]
  have hζsmall:ζ≤b/16:=by
    have hr:(1:ℝ)≤(r+13:ℕ):=by exact_mod_cast (show 1≤r+13 by omega)
    nlinarith [mul_nonneg hζ.le (sub_nonneg.mpr hr)]
  exact ⟨tol,ζ,htol,htcap,hζ,hzcap,by linarith,by linarith,by linarith⟩
end Oberwolfach

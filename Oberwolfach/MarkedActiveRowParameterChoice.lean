module

public import Oberwolfach.MarkedSpokeToleranceMonotone

@[expose] public section
/-! Choose row and retention errors below prescribed caps so that their
sum, with the fixed row order, is at most the required fraction of tstar. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem marked_active_row_parameter_choice (h:ℕ) (tstar tolCap ζCap:ℝ)
    (ht:0<tstar) (htol:0<tolCap) (hζ:0<ζCap):
    ∃ tol ζ:ℝ,0<tol ∧ tol≤tolCap ∧ 0<ζ ∧ ζ≤ζCap ∧ tol+h*ζ≤tstar/8:=by
  let tol:=min tolCap (tstar/32)
  let ζ:=min ζCap (tstar/(32*(h+1:ℕ)))
  have htol':0<tol:=by dsimp [tol];positivity
  have hζ':0<ζ:=by dsimp [ζ];positivity
  have htolcap:tol≤tolCap:=min_le_left _ _
  have hζcap:ζ≤ζCap:=min_le_left _ _
  have htbound:tol≤tstar/32:=min_le_right _ _
  have hζbound:ζ≤tstar/(32*(h+1:ℕ)):=min_le_right _ _
  have hp:(0:ℝ)<32*(h+1:ℕ):=by positivity
  have hz:= (le_div_iff₀ hp).mp hζbound
  have hn:(h:ℝ)≤(h+1:ℕ):=by exact_mod_cast (Nat.le_succ h)
  refine ⟨tol,ζ,htol',htolcap,hζ',hζcap,?_⟩
  nlinarith [mul_nonneg hζ'.le (sub_nonneg.mpr hn)]
end Oberwolfach

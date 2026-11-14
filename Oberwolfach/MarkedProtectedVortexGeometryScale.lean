module

public import Oberwolfach.MarkedProtectedSeparateGeometryBudgets

@[expose] public section

/-! A vortex ratio can be fixed before the correction tolerance. Its
second-level sizes satisfy the independent deep-star deletion bounds. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace Oberwolfach

theorem marked_protected_vortex_geometry_scale
    (C kappa rho t omegaI alpha xi:ℝ)
    (hC:0<C) (hk:0<kappa) (hrho:0<rho) (ht:0<t) (ho:0<omegaI)
    (ha:0<alpha) (hxi:0<xi):
    ∃ eps0:ℝ,0<eps0 ∧  ∀ eps:ℝ,0<eps→ eps≤ eps0→ 
      eps≤ 1 ∧  eps≤ alpha ∧  eps≤ xi/4 ∧ 
      C*eps^2≤ kappa/2 ∧ 
      (1+2/rho)*eps^2≤ t*(omegaI*eps/8)/32:=by
  let A:=1+2/rho
  have hA:0<A:=by dsimp [A];positivity
  let eps0:=min 1 (min alpha (min (xi/4) (min (kappa/(2*C)) (t*omegaI/(256*A)))))
  have he0:0<eps0:=by dsimp [eps0];positivity
  refine ⟨eps0,he0,?_⟩
  intro eps he heps
  have he1:eps≤ 1:=heps.trans (min_le_left _ _)
  have ha':eps≤ alpha:=heps.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hx':eps≤ xi/4:=heps.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hc':eps≤ kappa/(2*C):=heps.trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have hb':eps≤ t*omegaI/(256*A):=heps.trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
  have heSq:eps^2≤ eps:=by nlinarith only [he,he1]
  have hcc:eps*(2*C)≤ kappa:=(le_div_iff₀ (by positivity)).mp hc'
  have hbb:eps*(256*A)≤ t*omegaI:=(le_div_iff₀ (by positivity)).mp hb'
  have hscale:=mul_le_mul_of_nonneg_right hbb he.le
  have hcsq:=mul_le_mul_of_nonneg_left heSq hC.le
  refine ⟨he1,ha',hx',by nlinarith only [hcc,hcsq],?_⟩
  change A*eps^2≤ t*(omegaI*eps/8)/32
  nlinarith only [hscale]

end Oberwolfach

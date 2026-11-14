module

public import Oberwolfach.OrdinaryDeepParentNumericHierarchy

@[expose] public section
/-! The row, index, conflict and endpoint tolerances for the inner triangle
factor can all be fixed before the vortex size is chosen. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach

structure OrdinaryTriangleInnerNumericParameters
    (p κe εfactor ηend εrows δ εcount t lam:ℝ):Prop where
  delta_pos:0<δ
  count_pos:0<εcount
  t_pos:0<t
  lambda_pos:0<lam
  count_rows:εcount≤εrows
  count_geometry:εcount≤min (p^4/16) (p^3/2)
  lambda_conflict:lam≤εfactor
  lambda_inner:lam≤1/24
  lambda_row:4*lam≤εcount/2
  lambda_index:3*lam≤εcount*κe/2
  endpoint_error:δ+(2*40+(1+2*40)/(2*κe*p))*lam+
    (t+10*(40/(κe*p^5))*lam)≤ηend

theorem ordinary_triangle_inner_numeric_hierarchy
    (p κe εfactor ηend εrows:ℝ) (hp:0<p) (hκ:0<κe)
    (hεf:0<εfactor) (hη:0<ηend) (hrows:0<εrows):
    ∃δ εcount t lam:ℝ,OrdinaryTriangleInnerNumericParameters p κe εfactor ηend εrows δ εcount t lam:=by
  let C1:ℝ:=2*40+(1+2*40)/(2*κe*p)
  let C2:ℝ:=10*(40/(κe*p^5))
  let εcount:ℝ:=min εrows (min (p^4/16) (p^3/2))/2
  let δ:ℝ:=ηend/8
  let t:ℝ:=ηend/8
  let lam:ℝ:=min (1/24) (min εfactor (min (εcount/8) (min (εcount*κe/6) (ηend/(4*(C1+C2+1))))))/2
  have hC1:0<C1:=by dsimp [C1];positivity
  have hC2:0<C2:=by dsimp [C2];positivity
  have hε:0<εcount:=by dsimp [εcount];positivity
  have hδ:0<δ:=by dsimp [δ];positivity
  have ht:0<t:=by dsimp [t];positivity
  have hlam:0<lam:=by dsimp [lam];positivity
  have heRows:εcount≤εrows:=by
    have hh:=min_le_left εrows (min (p^4/16) (p^3/2))
    dsimp [εcount];linarith
  have heGeom:εcount≤min (p^4/16) (p^3/2):=by
    have hh:=min_le_right εrows (min (p^4/16) (p^3/2))
    have hz:0≤min (p^4/16) (p^3/2):=by positivity
    dsimp [εcount];linarith
  have h1:lam≤1/24:=by
    have hh:=min_le_left (1/24:ℝ) (min εfactor (min (εcount/8) (min (εcount*κe/6) (ηend/(4*(C1+C2+1))))))
    dsimp only [lam];linarith
  have h2:lam≤εfactor:=by
    have hh:min (1/24:ℝ) (min εfactor (min (εcount/8) (min (εcount*κe/6) (ηend/(4*(C1+C2+1))))))≤εfactor:=
      (min_le_right _ _).trans (min_le_left _ _)
    dsimp only [lam];linarith
  have h3:4*lam≤εcount/2:=by
    have hh:min (1/24:ℝ) (min εfactor (min (εcount/8) (min (εcount*κe/6) (ηend/(4*(C1+C2+1))))))≤εcount/8:=
      ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_left _ _)
    dsimp only [lam];linarith
  have h4:3*lam≤εcount*κe/2:=by
    have hh:min (1/24:ℝ) (min εfactor (min (εcount/8) (min (εcount*κe/6) (ηend/(4*(C1+C2+1))))))≤εcount*κe/6:=
      (((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_left _ _)
    have hz:0≤εcount*κe:=mul_nonneg hε.le hκ.le
    dsimp only [lam];nlinarith only [hh,hz]
  have h5:lam≤ηend/(4*(C1+C2+1)):=by
    have hh:min (1/24:ℝ) (min εfactor (min (εcount/8) (min (εcount*κe/6) (ηend/(4*(C1+C2+1))))))≤ηend/(4*(C1+C2+1)):=
      (((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_right _ _)
    have hz:0≤ηend/(4*(C1+C2+1)):=by positivity
    dsimp only [lam];linarith
  have herr:δ+C1*lam+(t+C2*lam)≤ηend:=by
    have hh:lam*(4*(C1+C2+1))≤ηend:=(le_div_iff₀ (by positivity)).mp h5
    dsimp only [δ,t]
    nlinarith [mul_nonneg hlam.le hC1.le,mul_nonneg hlam.le hC2.le]
  refine ⟨δ,εcount,t,lam,⟨hδ,hε,ht,hlam,heRows,heGeom,h2,h1,h3,h4,?_⟩⟩
  simpa only [C1,C2] using herr
end Oberwolfach

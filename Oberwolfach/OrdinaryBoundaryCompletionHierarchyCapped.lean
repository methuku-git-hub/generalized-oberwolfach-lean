module

public import Oberwolfach.OrdinaryBoundaryCompletionHierarchy

@[expose] public section
/-! Choose endpoint capacity scale before the smaller host, conflict and
cleanup scales; the resulting completion margin is strictly positive. -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach

theorem ordinary_boundary_completion_hierarchy_capped (m:ℕ) (β cap:ℝ) (hβ:0<β) (hcap:0<cap):
    ∃k:ℝ,0<k ∧ k≤1 ∧ k≤cap ∧ ∀δ φ ρ ν slack:ℝ,
      0≤δ→δ≤k^2→φ≤k^2→ρ≤k^2→ν≤k^2→slack≤k^2→
      ((m:ℝ)+1)*δ/k+((m:ℝ)+4)*φ+4*ρ+4*k+((m:ℝ)+9)*δ+3*ν+slack<β:=by
  let a:ℝ:=(m:ℝ)+20
  have ha:0<a:=by dsimp [a];positivity
  let k:ℝ:=min cap (min 1 (β/(100*a)))
  have hk:0<k:=lt_min hcap (lt_min (by norm_num) (div_pos hβ (by positivity)))
  have hk1:k≤1:=(min_le_right _ _).trans (min_le_left _ _)
  have hka:k≤β/(100*a):=(min_le_right _ _).trans (min_le_right _ _)
  have habound:100*a*k≤β:=by
    have hh: k*(100*a)≤β:=(le_div_iff₀ (by positivity)).mp hka
    nlinarith only [hh]
  refine ⟨k,hk,hk1,min_le_left _ _,?_⟩
  intro δ φ ρ ν slack hδ hδk hφ hρ hν hs
  have hk2:k^2≤k:=by nlinarith
  have hδ1:δ≤k:=hδk.trans hk2
  have hφ1:φ≤k:=hφ.trans hk2
  have hρ1:ρ≤k:=hρ.trans hk2
  have hν1:ν≤k:=hν.trans hk2
  have hs1:slack≤k:=hs.trans hk2
  have hquot:δ/k≤k:=(div_le_iff₀ hk).2 (by nlinarith)
  have hm1:0≤(m:ℝ)+1:=by positivity
  have hm4:0≤(m:ℝ)+4:=by positivity
  have hm9:0≤(m:ℝ)+9:=by positivity
  have hq:=mul_le_mul_of_nonneg_left hquot hm1
  have hq':((m:ℝ)+1)*δ/k≤((m:ℝ)+1)*k:=by
    convert hq using 1 <;> ring
  have hf:=mul_le_mul_of_nonneg_left hφ1 hm4
  have hd:=mul_le_mul_of_nonneg_left hδ1 hm9
  have hstrict:((3*(m:ℝ)+26)*k)<β:=by
    dsimp [a] at habound
    nlinarith [hk]
  nlinarith only [hq',hf,hd,hρ1,hν1,hs1,hstrict]
end Oberwolfach

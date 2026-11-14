module

public import Oberwolfach.OrdinaryRelativeErrorQuarterBudget

@[expose] public section
/-! Match-error rates can be fixed below both the placement tolerance and
the cutoff-dependent row bound before selecting the sample. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach

theorem ordinary_matching_mass_rates
    (K:ℕ) (hK:0<K) (θ κ err:ℝ) (hθ:0<θ) (hθ1:θ≤1) (hκ:0<κ) (herr:0<err):
    ∃lam γ a:ℝ,0<lam ∧ 0<γ ∧ 0<a ∧
      lam≤θ/10 ∧ γ≤lam/10 ∧ γ≤κ ∧ a≤κ ∧
      a≤θ/(1600*(K:ℝ)*(K:ℝ)) ∧
      0≤lam+γ*(1-θ+lam) ∧ lam+γ*(1-θ+lam)≤θ/8 ∧
      lam+γ*(1-θ+lam)≤err ∧ lam+γ*(1-θ+lam)<θ :=by
  have hKR:0<(K:ℝ):=by exact_mod_cast hK
  let lam:ℝ:=min (θ/20) (err/4)
  let γ:ℝ:=min (lam/20) (κ/2)
  let a:ℝ:=min (κ/2) (θ/(3200*(K:ℝ)*(K:ℝ)))
  have hl:0<lam:=by dsimp [lam];positivity
  have hg:0<γ:=by dsimp [γ];positivity
  have ha:0<a:=by dsimp [a];positivity
  have hlθ:lam≤θ/20:=min_le_left _ _
  have hlerr:lam≤err/4:=min_le_right _ _
  have hgl:γ≤lam/20:=min_le_left _ _
  have hgκ:γ≤κ/2:=min_le_right _ _
  have haκ:a≤κ/2:=min_le_left _ _
  have haθ:a≤θ/(3200*(K:ℝ)*(K:ℝ)):=min_le_right _ _
  have hfac:1-θ+lam≤1:=by linarith
  have hfac0:0≤1-θ+lam:=by linarith
  have hmul:γ*(1-θ+lam)≤γ:=by
    simpa using mul_le_mul_of_nonneg_left hfac hg.le
  have hq:=ordinary_relative_error_quarter_budget θ lam γ hθ.le hθ1 hl.le hg.le (by linarith) (by linarith)
  refine ⟨lam,γ,a,hl,hg,ha,by linarith,by linarith,by linarith,by linarith,?_,hq.1,hq.2,?_,?_⟩
  · have hd:(0:ℝ)<1600*(K:ℝ)*(K:ℝ):=by positivity
    have heq:3200*(K:ℝ)*(K:ℝ)=2*(1600*(K:ℝ)*(K:ℝ)):=by ring
    rw [heq] at haθ
    have hh:θ/(2*(1600*(K:ℝ)*(K:ℝ)))≤θ/(1600*(K:ℝ)*(K:ℝ)):=by
      apply div_le_div_of_nonneg_left hθ.le hd
      nlinarith
    exact haθ.trans hh
  · linarith
  · linarith [hq.2]
end Oberwolfach

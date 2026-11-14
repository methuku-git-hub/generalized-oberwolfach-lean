module

public import Mathlib.Tactic
public import Oberwolfach.MarkedCorrectionIncidenceBudget

@[expose] public section
/-! Choose the reference tolerance and neighbourhood error after the
correction scale is known, uniformly for every host with at most n hubs. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace Oberwolfach

theorem marked_common_correction_budget_choices
    (r:ℕ) (κmax η₀ cut:ℝ) (hκ:0<κmax) (hη:0<η₀) (hcut:0<cut):
    ∃ κ εRef εNbr:ℝ, 0<κ ∧ κ≤κmax ∧ εRef=κ/4 ∧ 0<εRef ∧ 0<εNbr ∧
      (∀ hNbr:ℕ,εNbr/(2*((hNbr:ℝ)+1))≤14*cut) ∧
      ∀ n u:ℕ,u≤n→
        2*(εRef*n)+2*(εNbr*u)≤η₀*n ∧
        εRef*n+εNbr*u≤η₀*n ∧
        ((((r+4):ℕ):ℝ)+1)*(εNbr*n)≤η₀*n :=by
  let c:ℝ:=((r+4:ℕ):ℝ)+1
  let κ:ℝ:=min κmax η₀/2
  let εRef:ℝ:=κ/4
  let εNbr:ℝ:=min (η₀/(4*c)) (14*cut)
  have hc:1≤c:=by
    dsimp [c]
    have hr:0≤((r+4:ℕ):ℝ):=by positivity
    linarith
  have hcpos:0<c:=lt_of_lt_of_le (by norm_num) hc
  have hkpos:0<κ:=by dsimp [κ];positivity
  have hkmax:κ≤κmax:=by dsimp [κ];have h:=min_le_left κmax η₀;linarith [h]
  have hketa:κ≤η₀/2:=by dsimp [κ];exact div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
  have hrefpos:0<εRef:=by dsimp [εRef];positivity
  have hnpos:0<εNbr:=by dsimp [εNbr];positivity
  have hncut:εNbr≤14*cut:=by dsimp [εNbr];exact min_le_right _ _
  have hnc:εNbr≤η₀/(4*c):=by dsimp [εNbr];exact min_le_left _ _
  have hnη:c*εNbr≤η₀/4:=by
    have hh:εNbr*(4*c)≤η₀:=(le_div_iff₀ (by positivity : 0<4*c)).mp hnc
    nlinarith
  have hnη':εNbr≤η₀/4:=by nlinarith [mul_nonneg (sub_nonneg.mpr hc) hnpos.le]
  have hrefη:εRef≤η₀/8:=by dsimp [εRef];linarith
  refine ⟨κ,εRef,εNbr,hkpos,hkmax,rfl,hrefpos,hnpos,?_,?_⟩
  · intro hNbr
    have hd:1≤2*((hNbr:ℝ)+1):=by
      have hh:0≤(hNbr:ℝ):=by positivity
      linarith
    have hh:εNbr/(2*((hNbr:ℝ)+1))≤εNbr:=div_le_self hnpos.le hd
    exact hh.trans hncut
  · intro n u hu
    have hu':(u:ℝ)≤n:=by exact_mod_cast hu
    have hn:0≤(n:ℝ):=by positivity
    have h1:=mul_le_mul_of_nonneg_right hrefη hn
    have h2:=mul_le_mul_of_nonneg_right hnη' hn
    have h3:=mul_le_mul_of_nonneg_left hu' hnpos.le
    have h4:=mul_le_mul_of_nonneg_right hnη hn
    dsimp only [c] at h4
    constructor
    · nlinarith
    constructor
    · nlinarith
    · nlinarith
/-- A later robust tolerance fits both the event scale and the level losses. -/
theorem marked_correction_robust_budget_choice
    (r:ℕ) (ζEvent gammaLoss sigmaLoss:ℝ)
    (hζ:0<ζEvent) (hγ:0<gammaLoss) (hσ:0<sigmaLoss):
    ∃ ζCorr:ℝ,0<ζCorr ∧ ζCorr≤ζEvent ∧
      (∀ ξ:ℝ,16*((((r+4):ℕ):ℝ)+1)*ξ≤ζCorr→∀ n:ℕ,
        6*(8*((((r+4):ℕ):ℝ)+1)*ξ*n)≤min (gammaLoss*n) (sigmaLoss*n)):=by
  let ζCorr:=min ζEvent (min gammaLoss sigmaLoss/3)/2
  have hp:0<ζCorr:=by dsimp [ζCorr];positivity
  have he:ζCorr≤ζEvent:=by dsimp [ζCorr];have h:=min_le_left ζEvent (min gammaLoss sigmaLoss/3);linarith
  have hg:3*ζCorr≤min gammaLoss sigmaLoss:=by
    dsimp [ζCorr]
    have h:=min_le_right ζEvent (min gammaLoss sigmaLoss/3)
    have hm:0≤min gammaLoss sigmaLoss:=le_min hγ.le hσ.le
    linarith
  exact ⟨ζCorr,hp,he,fun ξ hξ n=>marked_correction_incidence_budget r n ξ ζCorr gammaLoss sigmaLoss hξ hg⟩
end Oberwolfach

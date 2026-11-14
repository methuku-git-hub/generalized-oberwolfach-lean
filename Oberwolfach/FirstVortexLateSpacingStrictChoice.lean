module

public import Mathlib.Tactic

@[expose] public section
/-! Select spacing after the active and sampling rates, then choose the class
cutoff large enough for the same spacing. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_late_spacing_and_class_strict_choice
    (r:ℕ) (θ ε active cBoundary:ℝ)
    (hθ:0<θ) (hε:0<ε) (hactive:0<active) (hboundary:0<cBoundary):
    ∃dMin:ℕ,∀d:ℕ,dMin≤d→3≤d ∧ (r+4)+2≤d ∧
      1/(d:ℝ)≤θ/1024 ∧ 1/(d:ℝ)≤(active*ε/128)/10 ∧
      4/(d:ℝ)<cBoundary ∧ (1/(((r+4:ℕ):ℝ)+1))/(d:ℝ)≤θ ∧
      ∃KMin:ℕ,∀K:ℕ,KMin≤K→3≤K ∧
        5/((((r+4:ℕ):ℝ)+1)*(d:ℝ)+5)+(((r+4:ℕ):ℝ)+1)*(d:ℝ)/(K:ℝ)≤θ/2 :=by
  let δ:ℝ:=min (θ/1024) (min (active*ε/1280) (cBoundary/4))
  have hδ:0<δ:=by dsimp [δ];positivity
  obtain ⟨D,hD⟩:=exists_nat_gt (1/δ)
  let dMin:=max (D+1) (max 3 (r+6))
  refine ⟨dMin,?_⟩
  intro d hd
  have hdD:D<d:=by dsimp [dMin] at hd;omega
  have hd3:3≤d:=by dsimp [dMin] at hd;omega
  have hdr:(r+4)+2≤d:=by dsimp [dMin] at hd;omega
  have hdR:0<(d:ℝ):=by exact_mod_cast (show 0<d by omega)
  have hDd:(D:ℝ)<d:=by exact_mod_cast hdD
  have hInv:1/(d:ℝ)<δ:=by
    have hh:1/δ<(d:ℝ):=lt_trans hD hDd
    have hh':1<(d:ℝ)*δ:=(div_lt_iff₀ hδ).mp hh
    exact (div_lt_iff₀ hdR).2 (by nlinarith)
  have hθδ:δ≤θ/1024:=min_le_left _ _
  have haδ:δ≤active*ε/1280:=(min_le_right _ _).trans (min_le_left _ _)
  have hbδ:δ≤cBoundary/4:=(min_le_right _ _).trans (min_le_right _ _)
  have hsp:1/(d:ℝ)≤θ/1024:=hInv.le.trans hθδ
  have hasp:1/(d:ℝ)≤(active*ε/128)/10:=by linarith
  have hbsp:4/(d:ℝ)<cBoundary:=by
    have hh:4/(d:ℝ)=4*(1/(d:ℝ)):=by ring
    rw [hh];linarith
  let c:ℝ:=((r+4:ℕ):ℝ)+1
  have hc:1≤c:=by dsimp [c];have hr:(0:ℝ)≤r:=Nat.cast_nonneg _;push_cast;linarith
  have hcinv:1/c≤1:=by
    apply (div_le_iff₀ (show 0<c by linarith)).2
    linarith
  have hcut:(1/c)/(d:ℝ)≤θ:=by
    have hh:=div_le_div_of_nonneg_right hcinv hdR.le
    have hp:0≤1/(d:ℝ):=by positivity
    nlinarith
  have hden:0<c*(d:ℝ)+5:=by positivity
  have hfirst:5/(c*(d:ℝ)+5)≤5/(d:ℝ):=by
    apply div_le_div_of_nonneg_left (by norm_num) hdR
    nlinarith
  have hfirst':5/(c*(d:ℝ)+5)≤θ/4:=by
    have hh:5/(d:ℝ)=5*(1/(d:ℝ)):=by ring
    rw [hh] at hfirst
    linarith
  obtain ⟨M,hM⟩:=exists_nat_gt (4*c*(d:ℝ)/θ)
  let KMin:=max (M+1) 3
  refine ⟨hd3,hdr,hsp,hasp,hbsp,by simpa only [c] using hcut,KMin,?_⟩
  intro K hK
  have hK3:3≤K:=by dsimp [KMin] at hK;omega
  have hMK:M<K:=by dsimp [KMin] at hK;omega
  have hKR:0<(K:ℝ):=by exact_mod_cast (show 0<K by omega)
  have hMKreal:(M:ℝ)<K:=by exact_mod_cast hMK
  have hprod:4*c*(d:ℝ)<(K:ℝ)*θ:=(div_lt_iff₀ hθ).mp (lt_trans hM hMKreal)
  have hsecond:c*(d:ℝ)/(K:ℝ)≤θ/4:=by
    apply (div_le_iff₀ hKR).2
    nlinarith
  have hsum:5/(c*(d:ℝ)+5)+c*(d:ℝ)/(K:ℝ)≤θ/2:=by linarith
  exact ⟨hK3,by simpa only [c] using hsum⟩
end Oberwolfach

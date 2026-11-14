module

public import Oberwolfach.FirstVortexSplitChangeRateChoice

@[expose] public section
/-! One late common rate absorbs the actual-complement physical edit and the
conflict edit; the lower bound on the inner set converts it to a local rate. -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach

theorem ordinary_actual_physical_rate_budget
    (cap ρ : ℝ) (hcap : 0<cap) (hρ : 0<ρ) :
    ∃σ : ℝ, 0<σ ∧ ∀(n inner b κ prob t del LF loss e tcol reserve constant : ℝ),
      0≤n → 0 ≤ inner → ρ*n ≤ inner → 
      0≤b → b≤σ*n → 0≤κ → κ≤σ*n → 0≤prob → prob≤σ → 
      0≤t → t≤σ*n → 0≤del → del≤σ*n → 0≤LF → 
      0≤loss → loss≤σ*n → 0≤e → e≤σ*n → 0≤tcol → tcol≤σ*n → 
      0 ≤ reserve → reserve ≤ σ*n → 0≤constant → constant+2*LF≤σ*n → 
      let κref:=κ+prob*n+3*t+constant+del+LF
      let lrim:=b+κref+loss
      let lspoke:=max ((lrim+e)/2) tcol;
      LF+lrim+lspoke+reserve≤cap * inner := by
  let σ : ℝ := cap*ρ/42
  have hσ : 0<σ := by dsimp [σ];positivity
  refine ⟨σ,hσ,?_⟩
  intro n inner b κ prob t del LF loss e tcol reserve constant hn hi hinner
    hb0 hb hκ0 hκ hprob0 hprob ht0 ht hdel0 hdel hLF hloss0 hloss he0 he htcol0 htcol
    hreserve0 hreserve hconstant hconstantCap κref lrim lspoke
  have hmul : prob*n≤σ*n := mul_le_mul_of_nonneg_right hprob hn
  have htarget : 21*σ*n≤cap * inner := by
    have hh := mul_le_mul_of_nonneg_left hinner hcap.le
    dsimp [σ]
    nlinarith
  have hlrim : 0≤lrim := by dsimp [lrim,κref];positivity
  have hspoke : lspoke≤lrim+e+tcol := by
    dsimp [lspoke]
    apply max_le
    · linarith
    · linarith
  dsimp [lrim,κref] at hspoke ⊢
  nlinarith [hconstantCap,hκ,hb,hmul,ht,hdel,hloss,he,htcol,hreserve,htarget]
theorem ordinary_constant_eventually_below_linear_rate
    (σ C : ℝ) (hσ : 0<σ) :
    ∃N:ℕ,∀n:ℕ,N≤n → C≤σ*n := by
  obtain ⟨N,hN⟩:=exists_nat_gt (C/σ)
  refine ⟨N,?_⟩
  intro n hn
  have hn' : (N:ℝ)≤n := by exact_mod_cast hn
  have hh : C/σ≤(n:ℝ) := le_trans hN.le hn'
  simpa [mul_comm] using (div_le_iff₀ hσ).mp hh
theorem ordinary_matching_degree_rate_choice (cap : ℝ) (hcap : 0<cap) :
    ∃σ : ℝ, 0<σ ∧ ∀(n edit inner reserve conflict : ℝ),
      0≤n → edit≤σ*n → inner≤σ*n → reserve≤σ*n → conflict≤σ*n →
      edit+2*inner+reserve+conflict≤cap*n := by
  let σ : ℝ:=cap/8
  have hσ : 0<σ:=by dsimp [σ];linarith
  refine ⟨σ,hσ,?_⟩
  intro n edit inner reserve conflict hn he hi hr hc
  dsimp [σ] at *
  nlinarith
end Oberwolfach

module

public import Oberwolfach.OrdinaryMatchingMassErrorEventually

@[expose] public section
/-! Choose the full-mass error rates after the interval spacing and before n. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_matching_mass_rate_choices (m:ℕ) (err:ℝ) (herr:0<err):
    ∃D:ℕ,∀d≥D,0<d ∧ ∃ζ matchErr:ℝ,0<ζ ∧ 0<matchErr ∧
      1/(8*(d:ℝ))+((m:ℝ)+1)*(d:ℝ)*ζ+matchErr≤err/2:=by
  obtain ⟨D,hD⟩:=exists_nat_gt (1/(2*err))
  refine ⟨max D 1,?_⟩
  intro d hd
  have hd0:0<d:=by omega
  have hdR:0<(d:ℝ):=by exact_mod_cast hd0
  have hmul:1/(2*err)≤(d:ℝ):=le_of_lt (lt_of_lt_of_le hD (by exact_mod_cast (show D≤d by omega)))
  have hm:0<(m:ℝ)+1:=by positivity
  have hfirst:1/(8*(d:ℝ))≤err/4:=by
    have hh:1≤(d:ℝ)*(2*err):=(div_le_iff₀ (show 0<2*err by positivity)).1 hmul
    apply (div_le_iff₀ (show 0<8*(d:ℝ) by positivity)).2
    nlinarith
  let ζ:=err/(8*((m:ℝ)+1)*(d:ℝ))
  let matchErr:=err/8
  refine ⟨hd0,ζ,matchErr,by dsimp [ζ];positivity,by dsimp [matchErr];positivity,?_⟩
  have heq:((m:ℝ)+1)*(d:ℝ)*ζ=err/8:=by
    dsimp [ζ]
    field_simp
    <;> ring
  rw [heq]
  dsimp [matchErr]
  linarith
end Oberwolfach

module

public import Oberwolfach.FiniteLawPositiveLowerBoundWitness

@[expose] public section
/-! Choose the two failure allowances before the sample so the combined
selector's actual lower bound yields a positive-mass outcome. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem long_combined_selector_positive_sample
    (εcap ηcap:ℝ) (hεcap:0<εcap) (hηcap:0<ηcap):
    ∃ε₀ ηEvent:ℝ,0<ε₀ ∧ ε₀<1 ∧ ε₀≤εcap ∧ 0<ηEvent ∧ ηEvent≤ηcap ∧
      0<1-36*(ε₀+6*ηEvent) ∧
      ∀(Ω:Type) [Fintype Ω] (μ:FiniteLaw Ω) (Good:Ω→Prop),
        1-36*(ε₀+6*ηEvent)≤μ.probability Good→∃z,0<μ.mass z ∧ Good z :=by
  let ε₀:=min εcap (1/1000:ℝ)/2
  let η:=min ηcap (1/1000:ℝ)/2
  have he:0<ε₀:=by dsimp [ε₀]; positivity
  have hh:0<η:=by dsimp [η]; positivity
  have hecap:ε₀≤εcap:=by dsimp [ε₀];have :=min_le_left εcap (1/1000:ℝ);linarith
  have he1000:ε₀≤1/1000:=by dsimp [ε₀];have :=min_le_right εcap (1/1000:ℝ);linarith
  have hhcap:η≤ηcap:=by dsimp [η];have :=min_le_left ηcap (1/1000:ℝ);linarith
  have hh1000:η≤1/1000:=by dsimp [η];have :=min_le_right ηcap (1/1000:ℝ);linarith
  have hpos:0<1-36*(ε₀+6*η):=by linarith
  refine ⟨ε₀,η,he,by linarith,hecap,hh,hhcap,hpos,?_⟩
  intro Ω _ μ Good hprob
  exact finiteLaw_positive_lower_bound_witness μ Good _ hpos hprob
end Oberwolfach

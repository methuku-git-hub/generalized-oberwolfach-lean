module

public import Oberwolfach.FiniteAdaptiveStateLaw

@[expose] public section
/-! Select sample-dependent witnesses at every adaptive stage while keeping
the original sample fixed and adding the conditional failure bounds. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {Ω Γ Ξ:Type} [Fintype Ω] [Fintype Γ] [Fintype Ξ]

theorem finite_adaptive_witness_selection
    (μ:FiniteLaw Ω) (ν:ℕ→Ω→FiniteLaw Γ) (E:ℕ→Ω→Prop)
    (Next:ℕ→Ω→Γ→Ω→Prop) (base:Ω→Ξ) (e:ℝ) (δ:ℕ→ℝ)
    (hδ:∀i,0≤δ i) (hinit:1-e≤μ.probability (E 0))
    (hstep:∀i ω,E i ω→1-δ i≤(ν i ω).probability
      (fun c=>∃ω',Next i ω c ω' ∧ E (i+1) ω'))
    (hbase:∀i ω c ω',Next i ω c ω'→base ω'=base ω):
    ∃step:ℕ→Ω→Γ→Ω,
      (∀i ω c,(∃ω',Next i ω c ω' ∧ E (i+1) ω')→
        Next i ω c (step i ω c) ∧ E (i+1) (step i ω c)) ∧
      (∀i ω c,base (step i ω c)=base ω) ∧
      (∀n,1-(e+∑i∈Finset.range n,δ i)≤(finiteAdaptiveStateLaw μ ν step n).probability (E n)) ∧
      (∀n,(finiteAdaptiveStateLaw μ ν step n).map base=μ.map base):=by
  let step:ℕ→Ω→Γ→Ω:=fun i ω c=>
    if h:∃ω',Next i ω c ω' ∧ E (i+1) ω' then Classical.choose h else ω
  have hselected:∀i ω c,(∃ω',Next i ω c ω' ∧ E (i+1) ω')→
      Next i ω c (step i ω c) ∧ E (i+1) (step i ω c):=by
    intro i ω c h
    simpa only [step,dif_pos h] using Classical.choose_spec h
  have hpreserve:∀i ω c,base (step i ω c)=base ω:=by
    intro i ω c
    by_cases h:∃ω',Next i ω c ω' ∧ E (i+1) ω'
    · exact hbase i ω c (step i ω c) (hselected i ω c h).1
    · simp only [step,dif_neg h]
  have hstep':∀i ω,E i ω→1-δ i≤(ν i ω).probability (fun c=>E (i+1) (step i ω c)):=by
    intro i ω he
    apply (hstep i ω he).trans
    apply finiteLaw_probability_mono
    intro c hc
    exact (hselected i ω c hc).2
  exact ⟨step,hselected,hpreserve,finite_adaptive_state_survival μ ν step E e δ hδ hinit hstep',
    finite_adaptive_state_preserves_marginal μ ν step base hpreserve⟩
end Oberwolfach

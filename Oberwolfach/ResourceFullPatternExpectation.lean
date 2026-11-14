module

public import Oberwolfach.ResourceFullPatternConcentration

@[expose] public section
/-! Exact full-pattern expectations when each individual candidate reads
disjoint primitive coordinate sets. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem resource_full_pattern_supported_expectation
    {A I E:Type} [Fintype A] [Fintype I] [Fintype E] [DecidableEq A] [DecidableEq E]
    {Base:E→Type} [∀e,Fintype (Base e)] {State:A→Type}
    (μ:∀e,FiniteLaw (Base e)) (R:I→Finset A) (w:I→ℝ) (s:I→∀a,State a)
    (S:A→Finset E) (state:(∀e,Base e)→∀a,State a)
    (hs:∀a σ τ,(∀e∈S a,σ e=τ e)→state σ a=state τ a)
    (hdisj:∀i,∀a∈R i,∀b∈R i,a≠b→Disjoint (S a) (S b)):
    (FiniteLaw.pi μ).expectation (fun σ=>resourceFullPatternLoad R w s (state σ))=
      ∑i,w i*∏a∈R i,(FiniteLaw.pi μ).probability (fun σ=>state σ a=s i a) :=by
  unfold FiniteLaw.expectation resourceFullPatternLoad
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  have hh:=finiteLaw_disjoint_supported_family μ S (fun a σ=>state σ a=s i a)
    (fun a σ τ hagree=>by rw [hs a σ τ hagree]) (R i) (hdisj i)
  rw [←hh]
  unfold FiniteLaw.probability
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  rw [patternValue_indicator]
  split_ifs <;> ring
end Oberwolfach

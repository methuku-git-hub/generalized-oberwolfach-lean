module

public import Oberwolfach.PreparationConcentratedBalance

@[expose] public section
/-! Add the actual sampled marked and ordinary loads after each has been
compared with its fixed target, retaining its own concentration error. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem preparation_target_errors_balanced_sum {I:Type} [Fintype I]
    (τ a x t:ℝ) (b z errors:I→ℝ)
    (hbalance:a+∑ i,b i=1)
    (hx:|x-a|<t+τ*a)
    (hz:∀ i,|z i-b i|<errors i+τ*b i):
    |x+∑ i,z i-1|<t+(∑ i,errors i)+τ:=by
  have hh:=preparation_concentrated_balanced_sum 0 a a x (t+τ*a) b z b
    (fun i=>errors i+τ*b i) hbalance (by simp) (by intro i;simp) hx hz
  have heq:t+τ*a+(∑ i,(errors i+τ*b i))+0=t+(∑ i,errors i)+τ:=by
    rw [Finset.sum_add_distrib,← Finset.mul_sum]
    have hmul:=congrArg (fun v:ℝ=>τ*v) hbalance
    nlinarith [hmul]
  rwa [heq] at hh
end Oberwolfach

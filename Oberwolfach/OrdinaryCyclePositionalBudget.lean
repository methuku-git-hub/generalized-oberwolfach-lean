module

public import Oberwolfach.DivisibilityRepairScales

@[expose] public section
/-! Uniform positional budgets for a fixed finite family of cycle lengths.
Only a lower bound on the original degree scale is needed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_cycle_positional_budgets
    {I:Type} [Fintype I] (f:I→ℕ) (B:I→ℝ) (hB:∀i,0≤B i)
    (d:ℕ) (τ ε:ℝ) (hτ:0<τ) (hε:ε≤τ/4):
    ∃N:ℕ,∀n:ℕ,N≤n→0<n→∀D:ℝ,(n:ℝ)/2≤D→
      (∀i,6*((f i+2:ℕ):ℝ)^4*(B i)*(2*(3*d))+ε*(n:ℝ)≤τ*D) ∧
      (∀i,5*((f i+2:ℕ):ℝ)^4*(B i)*(2*(3*d))/(n:ℝ)≤τ) :=by
  have hsmall:∀i,∃N:ℕ,∀n:ℕ,N≤n→
      6*((f i+2:ℕ):ℝ)^4*(B i)*(2*(3*d))≤(τ/4)*(n:ℝ):=by
    intro i
    exact eventually_constant_le_linear _ (τ/4) (by positivity)
  choose N hN using hsmall
  refine ⟨Finset.univ.sup N,?_⟩
  intro n hn hn0 D hD
  have hnR:(0:ℝ)<n:=by exact_mod_cast hn0
  have hb (i:I):6*((f i+2:ℕ):ℝ)^4*(B i)*(2*(3*d))≤(τ/4)*(n:ℝ):=
    hN i n ((Finset.le_sup (Finset.mem_univ i)).trans hn)
  have hterm (i:I):0≤((f i+2:ℕ):ℝ)^4*(B i)*(2*(3*d)):=by
    have hBi:=hB i
    positivity
  constructor
  · intro i
    have he:=mul_le_mul_of_nonneg_right hε hnR.le
    have hd:=mul_le_mul_of_nonneg_left hD hτ.le
    nlinarith [hb i]
  · intro i
    apply (div_le_iff₀ hnR).2
    nlinarith [hb i,hterm i]
end Oberwolfach

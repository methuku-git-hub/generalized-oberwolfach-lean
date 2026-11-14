module

public import Mathlib.Tactic

@[expose] public section
/-! Use one host margin for the random regularisation event, compatible with
both the original host margin and the later matching scale. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_common_host_margin_choice
    (αRef αMatch ε:ℝ) (hRef:0<αRef) (hMatch:0<αMatch)
    (hεRef:ε≤(2*αRef)/100000) (hεMatch:ε≤(2*αMatch)/100000):
    ∃αHost:ℝ,0<αHost ∧ αHost≤2*αRef ∧ αHost≤2*αMatch ∧ ε≤αHost/100000 ∧
      ∀n:ℕ,∀D:ℝ,(1/2+2*αRef)*(n:ℝ)≤D→(1/2+αHost)*(n:ℝ)≤D :=by
  let αHost:=min (2*αRef) (2*αMatch)
  have hαHost:0<αHost:=by dsimp [αHost];positivity
  have hRefBound:αHost≤2*αRef:=min_le_left _ _
  have hMatchBound:αHost≤2*αMatch:=min_le_right _ _
  have hε:ε≤αHost/100000:=by
    dsimp [αHost]
    by_cases hh:2*αRef≤2*αMatch
    · rw [min_eq_left hh];exact hεRef
    · rw [min_eq_right (le_of_not_ge hh)];exact hεMatch
  refine ⟨αHost,hαHost,hRefBound,hMatchBound,hε,?_⟩
  intro n D hD
  have hn:(0:ℝ)≤n:=Nat.cast_nonneg n
  have hh:=mul_le_mul_of_nonneg_right hRefBound hn
  nlinarith
end Oberwolfach

module

public import Oberwolfach.AsymptoticMargins

@[expose] public section
/-! The finitely many constant failure tolerances can be fixed below any
positive total budget before the host order is chosen. -/
set_option autoImplicit false
namespace Oberwolfach

theorem marked_adaptive_failure_tolerances_exist
    (ε₀:ℝ) (hε₀:0<ε₀):
    ∃χ χCommon χBal χNbr χLoad χLocal χConfig:ℝ,
      0<χ ∧ 0<χCommon ∧ 0<χBal ∧ 0<χNbr ∧ 0<χLoad ∧ 0<χLocal ∧ 0<χConfig ∧
      χ+χCommon+χBal+2*χNbr+χLoad+χLocal+χConfig<ε₀ := by
  refine ⟨ε₀/16,ε₀/16,ε₀/16,ε₀/16,ε₀/16,ε₀/16,ε₀/16,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> linarith
end Oberwolfach

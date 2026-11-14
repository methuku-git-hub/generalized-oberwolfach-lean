module

public import Oberwolfach.OrdinaryLocalAbsorbers

@[expose] public section

/-! The order threshold for the fixed paired-absorber count is chosen
after the cycle length, neighbourhood density and conflict-degree bound. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_profile_budgets (m:ℕ) (β L:ℝ) (hβ:0<β):
    ∃ N:ℕ,∀ n:ℕ,N≤n →
      (m+3:ℝ)*(L+1)≤β/2*n ∧
      2*(m+1:ℝ)^2≤ordinaryLocalCountCoeff m β*n ∧
      2*(m:ℝ)*(2*(m+1)+(m+1)*m)≤ordinaryLocalCountCoeff m β*n := by
  let c:=ordinaryLocalCountCoeff m β
  have hc:0<c:=ordinaryLocalCountCoeff_pos m β hβ
  let x:ℝ:=(m+3)*(L+1)/(β/2)
  let y:ℝ:=2*(m+1:ℝ)^2/c
  let z:ℝ:=2*(m:ℝ)*(2*(m+1)+(m+1)*m)/c
  obtain ⟨N,hN⟩:=exists_nat_gt (max x (max y z))
  refine ⟨N,?_⟩
  intro n hn
  have hn':(N:ℝ)≤n:=by exact_mod_cast hn
  have hx:x≤n:=(le_max_left _ _).trans (le_of_lt hN) |>.trans hn'
  have hy:y≤n:=((le_max_left y z).trans (le_max_right x (max y z))).trans (le_of_lt hN) |>.trans hn'
  have hz:z≤n:=((le_max_right y z).trans (le_max_right x (max y z))).trans (le_of_lt hN) |>.trans hn'
  refine ⟨?_,?_,?_⟩
  · dsimp [x] at hx
    have hh: (m+3:ℝ)*(L+1)≤n*(β/2):=(div_le_iff₀ (by positivity)).mp hx
    nlinarith only [hh]
  · dsimp [y] at hy
    have hh: 2*(m+1:ℝ)^2≤n*c:=(div_le_iff₀ hc).mp hy
    nlinarith only [hh]
  · dsimp [z] at hz
    have hh:2*(m:ℝ)*(2*(m+1)+(m+1)*m)≤n*c:=(div_le_iff₀ hc).mp hz
    nlinarith only [hh]
end Oberwolfach

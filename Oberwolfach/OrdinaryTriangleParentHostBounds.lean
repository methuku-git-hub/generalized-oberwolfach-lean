module

public import Oberwolfach.Definitions
public import Mathlib.Tactic

@[expose] public section
/-! The triangle parent selectors use half of the original host margin and
finite terminal-size thresholds fixed before the graph. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_triangle_parent_degree_from_host
    (α θhost N D:ℝ) (hθ:1/2≤θhost) (hthreshold:cycleThreshold 3≤θhost)
    (hN:0≤N) (hdegree:(θhost+α)*N≤D):
    (max (1/2) (cycleThreshold 3)+2*(α/2))*N≤D :=by
  have hm:max (1/2) (cycleThreshold 3)≤θhost:=max_le hθ hthreshold
  have hh:=mul_le_mul_of_nonneg_right hm hN
  nlinarith only [hdegree,hh]

theorem ordinary_vortex_parent_terminal_thresholds
    (ε:ℝ) (hε:0<ε) (Mhost Mcut:ℕ):
    ∃m₀:ℕ,1≤m₀ ∧ ∀m:ℕ,m₀≤m→
      (Mhost:ℝ)≤ε*m/2 ∧ (Mcut:ℝ)≤ε*m/2 :=by
  obtain ⟨v,hv⟩:=exists_nat_ge (2*((max Mhost Mcut:ℕ):ℝ)/ε)
  refine ⟨max v 1,by omega,?_⟩
  intro m hm
  have hvreal:(v:ℝ)≤m:=by exact_mod_cast (show v≤m by omega)
  have hparent:(2*((max Mhost Mcut:ℕ):ℝ))≤ε*m:=by
    have hh:2*((max Mhost Mcut:ℕ):ℝ)≤ε*v:=by
      simpa [mul_comm] using (div_le_iff₀ hε).mp hv
    have hh':ε*v≤ε*m:=mul_le_mul_of_nonneg_left hvreal hε.le
    linarith only [hh,hh']
  have hhost:(Mhost:ℝ)≤(max Mhost Mcut:ℕ):=by exact_mod_cast (le_max_left Mhost Mcut)
  have hcut:(Mcut:ℝ)≤(max Mhost Mcut:ℕ):=by exact_mod_cast (le_max_right Mhost Mcut)
  constructor <;> linarith only [hhost,hcut,hparent]
end Oberwolfach

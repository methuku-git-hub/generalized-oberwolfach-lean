module

public import Mathlib.Tactic

@[expose] public section
/-! A fixed absorber-size bound and a small inner index set fit the common
outer-spoke codegree margin once the graph order is large. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem actual_reserved_outer_codegree_loss
    (α:ℝ) (hα:0<α) (B:ℕ):
    ∃ N:ℕ,∀ n:ℕ,N≤n→∀ (I R:ℕ) (ε:ℝ),ε≤α/2→
      (I:ℝ)≤ε*n→R≤B→(I:ℝ)+2*R≤α*n :=by
  obtain ⟨N,hN⟩:=exists_nat_gt (4*(B:ℝ)/α)
  refine ⟨N,?_⟩
  intro n hn I R ε hε hI hR
  have hnR:(N:ℝ)≤n:=by exact_mod_cast hn
  have hdiv:4*(B:ℝ)<α*N:=by
    have h:4*(B:ℝ)<(N:ℝ)*α:=(div_lt_iff₀ hα).mp hN
    nlinarith
  have hR':(R:ℝ)≤B:=by exact_mod_cast hR
  have hn0:(0:ℝ)≤n:=by positivity
  have hI':(I:ℝ)≤(α/2)*n:=hI.trans (mul_le_mul_of_nonneg_right hε hn0)
  nlinarith
end Oberwolfach

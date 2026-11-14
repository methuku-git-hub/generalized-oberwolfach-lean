module

public import Oberwolfach.OrdinaryProfileErrorBound
public import Oberwolfach.CoordinateLocalLemma

@[expose] public section
/-! A positive lower bound on the original-law event yields a sampled outcome. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
theorem ordinary_profile_event_exists {Ω:Type} [Fintype Ω] (μ:FiniteLaw Ω) (E:Ω→Prop)
    (n:ℕ) (hn:2≤n) (errD errR:ℝ)
    (hprob:1-errD-errR≤μ.probability E) (herr:errD+errR≤2/(n:ℝ)^2):
    ∃ σ,0<μ.mass σ∧E σ := by
  have hnR:(2:ℝ)≤n:=by exact_mod_cast hn
  have hn2:0<(n:ℝ)^2:=by positivity
  have hsmall:2/(n:ℝ)^2<1:=(div_lt_one hn2).mpr (by nlinarith)
  have hpos:0<μ.probability E:=by linarith
  exact finiteLaw_positive_event_exists μ E hpos
end Oberwolfach

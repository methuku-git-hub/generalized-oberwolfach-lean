module

public import Oberwolfach.LongPrescribedSpacingSmall

@[expose] public section
/-! The active-level prescribed-set loss is small after the spacing and
host-size choices, using the actual matching rates. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_prescribed_active_eventually
    (d K:ℕ) (ε cap lam θ eps:ℝ) (hd:0<d) (hε:0<ε) (hcap:0<cap) (hlam:lam≤1)
    (hspacing:1/(d:ℝ)≤(cap*ε/128)/10):
    let a:=min (lam/(10*(d:ℝ))) (θ/(200*(K:ℝ)^2))
    let γ:=min (eps/2) (min (1/2:ℝ) (min (lam/(10*(d:ℝ))) (lam/10)));
    ∃N:ℕ,∀n:ℕ,N≤n→
      2*((n:ℝ)+2*(n:ℝ)^(3/4:ℝ))/(d:ℝ)+2*max a γ*n≤cap*(ε*n)/128 :=by
  intro a γ
  have hdreal:0<10*(d:ℝ):=by exact_mod_cast (show 0<10*d by omega)
  have hrate:lam/(10*(d:ℝ))≤1/(10*(d:ℝ)):=div_le_div_of_nonneg_right hlam hdreal.le
  have ha:a≤1/(10*(d:ℝ)):=(min_le_left _ _).trans hrate
  have hg:γ≤1/(10*(d:ℝ)):=by
    have h₁:=min_le_right (eps/2) (min (1/2:ℝ) (min (lam/(10*(d:ℝ))) (lam/10)))
    have h₂:=min_le_right (1/2:ℝ) (min (lam/(10*(d:ℝ))) (lam/10))
    have h₃:=min_le_left (lam/(10*(d:ℝ))) (lam/10)
    dsimp only [γ]
    exact h₁.trans (h₂.trans (h₃.trans hrate))
  obtain ⟨N,hN⟩:=long_prescribed_spacing_eventually_small d (cap*ε/128) hd (by positivity) hspacing
  refine ⟨N,?_⟩
  intro n hn
  have hh:=hN n hn a γ (max_le ha hg)
  convert hh using 1 <;> ring
end Oberwolfach

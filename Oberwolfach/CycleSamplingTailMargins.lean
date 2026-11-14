module

public import Oberwolfach.AsymptoticMargins

@[expose] public section
/-! A polynomial number of fixed vertex and pair tests has vanishing total
failure probability when their tails are respectively quadratic and linear. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem cycle_sampling_union_error_small (c b:ℝ) (hc:0<c) (hb:0<b):
    ∃ N:ℕ,∀ n:ℕ,N≤n→
      2*(n:ℝ)*Real.exp (-c*(n:ℝ)^2)+(n:ℝ)^2*Real.exp (-b*(n:ℝ))<1 := by
  obtain ⟨N1,h1⟩:=eventually_stretchedExp_le_inv_pow 2 1 (c:=c) (p:=2) hc (by norm_num) 1
  obtain ⟨N2,h2⟩:=eventually_stretchedExp_le_inv_pow 1 2 (c:=b) (p:=1) hb (by norm_num) 1
  refine ⟨max 3 (max N1 N2),?_⟩
  intro n hn
  have hn3:3≤n:=(le_max_left _ _).trans hn
  have hnpos:(0:ℝ)<n:=by exact_mod_cast (show 0<n by omega)
  have h1':2*(n:ℝ)*Real.exp (-c*(n:ℝ)^2)≤1/(n:ℝ):=by
    simpa only [Real.rpow_one,Real.rpow_two,pow_one] using h1 n ((le_max_left _ _).trans ((le_max_right _ _).trans hn))
  have h2':(n:ℝ)^2*Real.exp (-b*(n:ℝ))≤1/(n:ℝ):=by
    simpa only [Real.rpow_one,Real.rpow_two,pow_one,one_mul] using h2 n ((le_max_right _ _).trans ((le_max_right _ _).trans hn))
  have hlt:2/(n:ℝ)<1:= (div_lt_one hnpos).mpr (by exact_mod_cast (show 2<n by omega))
  have heq:1/(n:ℝ)+1/(n:ℝ)=2/(n:ℝ):=by ring
  linarith only [h1',h2',hlt,heq]
end Oberwolfach

module

public import Oberwolfach.RawIntervalHubStartInvCard

@[expose] public section
/-! The failure probability of all hub-start tests is uniformly small for
large enough host order, independently of the assigned probabilities. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem eventually_ordinary_start_failure_below (d:ℕ) (hd:2≤d) (ζ:ℝ) (hζ:0<ζ):
    ∃N:ℕ,∀n:ℕ,N≤n→∀(U:Type) [Fintype U],Fintype.card U≤n→
      4*(Fintype.card U:ℝ)*Real.exp
        (-2*((n:ℝ)^(3/4:ℝ)/d)^2/((4*(d:ℝ)+3)^2*(n:ℝ)))≤ζ :=by
  have hdpos:(0:ℝ)<d:=by exact_mod_cast (show 0<d by omega)
  let c:ℝ:=2/((4*(d:ℝ)+3)^2*(d:ℝ)^2)
  have hc:0<c:=by dsimp [c];positivity
  obtain ⟨N,hN⟩:=eventually_stretchedExp_le_inv_pow (4:ℝ) 1 (c:=c) (p:=1/2) hc (by norm_num) 1
  obtain ⟨Nζ,hNζ⟩:=exists_nat_gt (1/ζ)
  refine ⟨max (max N Nζ) 1,?_⟩
  intro n hn U _ hU
  have hnN:N≤n:=by omega
  have hnζ:Nζ≤n:=by omega
  have hnpos:(0:ℝ)<n:=by exact_mod_cast (show 0<n by omega)
  have hUR:(Fintype.card U:ℝ)≤n:=by exact_mod_cast hU
  have hb:=hN n hnN
  simp only [Real.rpow_one,pow_one] at hb
  have heq:((n:ℝ)^(3/4:ℝ))^2=(n:ℝ)^(1/2:ℝ)*(n:ℝ):=by
    calc
      _ = (n:ℝ)^(3/2:ℝ) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hnpos.le];norm_num
      _ = (n:ℝ)^(1/2:ℝ)*(n:ℝ)^(1:ℝ) := by rw [← Real.rpow_add hnpos];norm_num
      _ = _ := by rw [Real.rpow_one]
  have harg: -2*((n:ℝ)^(3/4:ℝ)/d)^2/((4*(d:ℝ)+3)^2*(n:ℝ)) = -c*(n:ℝ)^(1/2:ℝ):=by
    rw [div_pow,heq]
    dsimp [c]
    field_simp
  rw [harg]
  have hcoeff:4*(Fintype.card U:ℝ)*Real.exp (-c*(n:ℝ)^(1/2:ℝ))≤
      4*(n:ℝ)*Real.exp (-c*(n:ℝ)^(1/2:ℝ)):=by
    gcongr
  have hsmall:(1:ℝ)/(n:ℝ)≤ζ:=by
    apply (div_le_iff₀ hnpos).2
    have hnζR:(Nζ:ℝ)≤n:=by exact_mod_cast hnζ
    have hh:1<ζ*(n:ℝ):=by
      have h:= (div_lt_iff₀ hζ).1 hNζ
      nlinarith
    linarith
  exact hcoeff.trans (hb.trans hsmall)
end Oberwolfach

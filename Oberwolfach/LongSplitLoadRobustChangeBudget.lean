module

public import Oberwolfach.LongCommonEventBalanceAndRetention

@[expose] public section
/-! The common-balance row budget bounds the rim graph at the same robust
change scale, with no square-root coupling to the embedding-host error. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem long_split_load_robust_change_budget
    (n:ℕ) (ζret δspoke ηBalance ηphys ζChange capStable:ℝ)
    (hζret:0≤ζret) (hδspoke:0≤δspoke) (hηBalance:0≤ηBalance)
    (hChange:0≤ζChange) (hcap:ζChange≤capStable)
    (hbudget:2*(ζret*n+(δspoke*n+(Real.sqrt δspoke*n+1)))+
      (ηBalance*n+2*ηphys)≤ζChange*n):
    ηphys≤capStable*n :=by
  have hn:(0:ℝ)≤n:=Nat.cast_nonneg _
  have hnonneg:0≤ζret*n+(δspoke*n+(Real.sqrt δspoke*n+1)):=by positivity
  have hbal:0≤ηBalance*n:=mul_nonneg hηBalance hn
  have hc:0≤ζChange*n:=mul_nonneg hChange hn
  have hcs:=mul_le_mul_of_nonneg_right hcap hn
  nlinarith
end Oberwolfach

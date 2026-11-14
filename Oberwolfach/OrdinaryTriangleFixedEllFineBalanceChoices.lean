module

public import Oberwolfach.OrdinaryTriangleEarlyFixedEllLoad
public import Oberwolfach.OrdinarySharpFineBalanceRatesChoice

@[expose] public section
/-! After the rate-dependent cap and geometry margin are known, choose a
triangle fine cover below both without changing the earlier outer allowance. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_triangle_fixed_ell_fine_balance_choices
    (ε δcut ρ₀ γ edit lam ellCap capSmall:ℝ)
    (hε:0<ε) (hδ:0<δcut) (hρ:0<ρ₀) (hγ:0<γ) (hedit:0<edit)
    (hlam:0≤lam) (hell:0<ellCap) (hcap:0<capSmall) (hroot:400*lam≤ellCap):
    ∃aLoad ξroot η₀ ηbal ηInitial:ℝ,
      0<aLoad ∧ aLoad≤1 ∧ aLoad≤γ/1000 ∧ aLoad≤edit/(72*((2:ℝ)+2)) ∧
      ξroot=min (ε/200) (aLoad^2/160) ∧ 0<ξroot ∧ ξroot≤γ/160000 ∧ 10*ξroot≤capSmall ∧
      η₀=δcut*(ρ₀/8)*ξroot/1000 ∧ 0<η₀ ∧ 0<ηbal ∧ ηbal≤η₀ ∧ ηbal≤γ/1000 ∧
      0<ηInitial ∧ ηInitial≤ηbal ∧ ηbal+100*ξroot≤γ/8 ∧ ηInitial+100*ξroot≤γ/8 ∧
      max (18*aLoad+3*lam) ((3*aLoad+lam)*3)≤ellCap :=by
  let other:=min capSmall (edit/(72*((2:ℝ)+2)))
  have hother:0<other:=by dsimp [other];positivity
  obtain ⟨loadCap,hload,hload1,hloadother,hbound⟩:=
    ordinary_triangle_early_fixed_ell_load lam ellCap other hlam hell hother hroot
  obtain ⟨aLoad,ξroot,η₀,ηbal,ηInitial,ha,ha1,hacap,haγ,hξeq,hξ,hξγ,hηeq,hη₀,
    hη,hηcap,hηγ,hηI,hηIcap,hsmall,hsmall'⟩:=
      ordinary_sharp_fine_balance_rates_choice ε δcut ρ₀ γ loadCap hε hδ hρ hγ hload
  have hacapSmall:aLoad≤capSmall:=hacap.trans (hloadother.trans (min_le_left _ _))
  have haedit:aLoad≤edit/(72*((2:ℝ)+2)):=hacap.trans (hloadother.trans (min_le_right _ _))
  have hξsq:ξroot≤aLoad^2/160:=by rw [hξeq];exact min_le_right _ _
  have hasq:aLoad^2≤aLoad:=by nlinarith [mul_nonneg ha.le (sub_nonneg.mpr ha1)]
  have hξcap:10*ξroot≤capSmall:=by nlinarith
  exact ⟨aLoad,ξroot,η₀,ηbal,ηInitial,ha,ha1,haγ,haedit,hξeq,hξ,hξγ,hξcap,hηeq,hη₀,
    hη,hηcap,hηγ,hηI,hηIcap,hsmall,hsmall',hbound aLoad ha.le hacap⟩
end Oberwolfach

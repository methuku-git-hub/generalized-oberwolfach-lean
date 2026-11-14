module

public import Oberwolfach.MarkedVortexPhysicalLocalBudgetsFromSplit

@[expose] public section
/-! Scalar reduction for the two local transfer budgets. It allows the
matching correction rate to be chosen independently of the later balance tolerance. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_local_chain_rate_budget
    (N I c ε ρ t η loc A B E ret bal:ℝ)
    (hN:0≤N) (hI:0≤I) (hIN:I≤N) (hc:0≤c) (hε:0≤ε) (hrho:0<ρ)
    (ht:0≤t) (hη:0≤η) (hηt:η≤t) (hsize:ε*N/2≤I)
    (hA:A≤t*N) (hB:B≤t*N) (hE:E≤t*N) (hret:ret≤t*N) (hbal:bal≤t*N)
    (hloc:loc≤t*N) (hunit:1≤t*N)
    (hrate:(17+4/ρ)*t≤c*ε/2):
    A+2*B+E+loc+(I*η+loc)/ρ+1≤c*I ∧
    2*(ret+B)+bal+2*(A+2*B+E+loc+(I*η+loc)/ρ+1)≤c*I :=by
  have hIη:I*η≤t*N:=by
    have h₁:=mul_nonneg (sub_nonneg.mpr hIN) hη
    have h₂:=mul_nonneg hI (sub_nonneg.mpr hηt)
    nlinarith [h₁,h₂]
  have hquot:(I*η+loc)/ρ≤(2*t*N)/ρ:=
    div_le_div_of_nonneg_right (by linarith) hrho.le
  have hlinear:(17+4/ρ)*t*N≤(c*ε/2)*N:=mul_le_mul_of_nonneg_right hrate hN
  have hinner:(c*ε/2)*N≤c*I:=by
    have hh:=mul_le_mul_of_nonneg_left hsize hc
    nlinarith
  have hrateN:(17+4/ρ)*t*N≤c*I:=hlinear.trans hinner
  have hquotEq:(2*t*N)/ρ=(2/ρ)*t*N:=by ring
  rw [hquotEq] at hquot
  have hnprod:0≤t*N:=mul_nonneg ht hN
  have hdivprod:0≤(1/ρ)*t*N:=by positivity
  have hnorm:(17+4/ρ)*t*N=17*(t*N)+4*((1/ρ)*t*N):=by ring
  have hnorm2:(2/ρ)*t*N=2*((1/ρ)*t*N):=by ring
  rw [hnorm] at hrateN
  rw [hnorm2] at hquot
  constructor <;> linarith only [hA,hB,hE,hret,hbal,hloc,hunit,hquot,hrateN,hnprod,hdivprod]
end Oberwolfach

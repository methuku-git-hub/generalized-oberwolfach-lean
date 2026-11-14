module

public import Mathlib.Tactic

@[expose] public section
/-! Local transfer margins with a total inner indegree error. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_local_chain_inner_sum_budget
    (N I c ε ρ t total loc A B E ret bal:ℝ)
    (hN:0<N) (hI:0≤I) (hc:0≤c) (hε:0≤ε) (hrho:0<ρ)
    (ht:0≤t) (htotal:0≤total) (hcap:total≤c*ρ*N*I/4) (hsize:ε*N/2≤I)
    (hA:A≤t*N) (hB:B≤t*N) (hE:E≤t*N) (hret:ret≤t*N) (hbal:bal≤t*N)
    (hloc:loc≤t*N) (hunit:1≤t*N) (hrate:(17+2/ρ)*t≤c*ε/4):
    A+2*B+E+loc+(total/N+loc)/ρ+1≤c*I ∧
    2*(ret+B)+bal+2*(A+2*B+E+loc+(total/N+loc)/ρ+1)≤c*I :=by
  have hterm:(total/N)/ρ≤c*I/4:=by
    apply (div_le_iff₀ hrho).2
    apply (div_le_iff₀ hN).2
    nlinarith [hcap]
  have hlocρ:loc/ρ≤(t*N)/ρ:=div_le_div_of_nonneg_right hloc hrho.le
  have hlinear:(17+2/ρ)*t*N≤(c*ε/4)*N:=mul_le_mul_of_nonneg_right hrate hN.le
  have hinner:(c*ε/4)*N≤c*I/2:=by
    have hh:=mul_le_mul_of_nonneg_left hsize hc
    nlinarith
  have hrateN:(17+2/ρ)*t*N≤c*I/2:=hlinear.trans hinner
  have hnonneg:0≤t*N:=mul_nonneg ht hN.le
  have hdiv:0≤(t*N)/ρ:=div_nonneg hnonneg hrho.le
  have hrewrite:(total/N+loc)/ρ=(total/N)/ρ+loc/ρ:=by ring
  have hnorm:(17+2/ρ)*t*N=17*(t*N)+2*((t*N)/ρ):=by ring
  rw [hnorm] at hrateN
  rw [hrewrite]
  constructor <;> linarith only [hA,hB,hE,hret,hbal,hloc,hunit,hterm,hlocρ,hrateN,hnonneg,hdiv]
end Oberwolfach

module

public import Mathlib.Tactic

@[expose] public section
/-! Keep the matching error on the inner-set scale rather than bounding it
by the ambient local rate. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_local_chain_split_eta_budget
    (N I c ε ρ t η loc A B E ret bal:ℝ)
    (hN:0≤N) (hI:0≤I) (hc:0≤c) (hε:0≤ε) (hrho:0<ρ)
    (ht:0≤t) (hη:0≤η) (hηcap:η≤c*ρ/4) (hsize:ε*N/2≤I)
    (hA:A≤t*N) (hB:B≤t*N) (hE:E≤t*N) (hret:ret≤t*N) (hbal:bal≤t*N)
    (hloc:loc≤t*N) (hunit:1≤t*N)
    (hrate:(17+2/ρ)*t≤c*ε/4):
    A+2*B+E+loc+(I*η+loc)/ρ+1≤c*I ∧
    2*(ret+B)+bal+2*(A+2*B+E+loc+(I*η+loc)/ρ+1)≤c*I :=by
  have hηI:I*η/ρ≤c*I/4:=by
    apply (div_le_iff₀ hrho).2
    have hh:=mul_le_mul_of_nonneg_left hηcap hI
    nlinarith
  have hlocρ:loc/ρ≤(t*N)/ρ:=div_le_div_of_nonneg_right hloc hrho.le
  have hlinear:(17+2/ρ)*t*N≤(c*ε/4)*N:=mul_le_mul_of_nonneg_right hrate hN
  have hinner:(c*ε/4)*N≤c*I/2:=by
    have hh:=mul_le_mul_of_nonneg_left hsize hc
    nlinarith
  have hrateN:(17+2/ρ)*t*N≤c*I/2:=hlinear.trans hinner
  have hterm:0≤t*N:=mul_nonneg ht hN
  have hdiv:0≤(t*N)/ρ:=div_nonneg hterm hrho.le
  have hrewrite:(I*η+loc)/ρ=I*η/ρ+loc/ρ:=by ring
  have hnorm:(17+2/ρ)*t*N=17*(t*N)+2*((t*N)/ρ):=by ring
  rw [hnorm] at hrateN
  rw [hrewrite]
  constructor <;> linarith only [hA,hB,hE,hret,hbal,hloc,hunit,hηI,hlocρ,hrateN,hterm,hdiv]
end Oberwolfach

module

public import Oberwolfach.FirstVortexLocalChainSplitEtaBudget

@[expose] public section
/-! The local transfer uses the inner indegree error, independently of the
larger global matching error. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_local_chain_inside_rate_budget
    (N I c ε ρ t inside loc A B E ret bal:ℝ)
    (hN:0<N) (hI:0≤I) (hc:0≤c) (hε:0≤ε) (hrho:0<ρ)
    (ht:0≤t) (hinside:0≤ inside) (hinsideCap:inside≤c*ρ*N/4) (hsize:ε*N/2≤I)
    (hA:A≤t*N) (hB:B≤t*N) (hE:E≤t*N) (hret:ret≤t*N) (hbal:bal≤t*N)
    (hloc:loc≤t*N) (hunit:1≤t*N) (hrate:(17+2/ρ)*t≤c*ε/4):
    A+2*B+E+loc+(I*(inside/N)+loc)/ρ+1≤c*I ∧
    2*(ret+B)+bal+2*(A+2*B+E+loc+(I*(inside/N)+loc)/ρ+1)≤c*I :=by
  have hcap:inside/N≤c*ρ/4:=by
    apply (div_le_iff₀ hN).2
    nlinarith [hinsideCap]
  exact first_vortex_local_chain_split_eta_budget N I c ε ρ t (inside/N) loc A B E ret bal
    hN.le hI hc hε hrho ht (div_nonneg hinside hN.le) hcap hsize hA hB hE hret hbal hloc hunit hrate
end Oberwolfach

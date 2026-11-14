module

public import Oberwolfach.FirstVortexOrderedSummedLossMatchingParameters
public import Oberwolfach.FirstVortexRetentionBalanceParameters

@[expose] public section
/-! Retention and common balance are selected after the fixed spacing and
before the finite host and class choices, on the same parameter scales. -/
set_option autoImplicit false
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def FirstVortexRetentionBalanceRates
    (r d:ℕ) (ε cap θ s c ζret ζlocal ηBalance κaux:ℝ):Prop :=
      0<ζret ∧ 0<ζlocal ∧ 0<ηBalance ∧ 0<κaux ∧
      ζret≤s ∧ ζret≤c/1024 ∧ ζret≤θ/4096 ∧
      ζlocal≤cap/128 ∧ ζret≤ζlocal*ε/2 ∧
      ηBalance≤s ∧ ηBalance≤c/1024 ∧
      κaux≤s ∧ κaux≤ζret ∧ κaux≤ηBalance/(8*((((r+4):ℕ):ℝ)+1)) ∧
    ∃Nret:ℕ,
      (∀n:ℕ,Nret≤n→∀q errOrd:ℝ,
        q≤1/(((((r+4):ℕ):ℝ))+1)→errOrd≤θ*n→
        (n:ℝ)*q/d+(((((r+4)+1)*d-1:ℕ):ℝ))*(2*((n:ℝ)^(3/4:ℝ)/d)+ζret*n)+errOrd≤4*θ*n) ∧
      ∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
        [LinearOrder V] [DecidableEq U],
      ∀(G:SimpleGraph V) (D mm:ℕ) (β:ℝ) (Q:Vortex U G D β ε mm) (hmm:0<mm)
        (π:Equiv.Perm V) (σ:RawIntervalFamilyOutcome V U Γ Color) (g:Γ) (t:ℕ)
        (J:StartRetentionOutcome (rawStartHubSet π d σ g) t),
      RetainedRestrictionGood π d σ g t (fun _:Unit=>Finset.univ) (fun _:Unit=>Finset.univ) ζret J→
      RetainedRestrictionLocalGood π d σ g t (Q.extendedVertices 1) Finset.univ ζlocal J

theorem first_vortex_ordered_summed_loss_retention_parameters
    (r:ℕ) (α ε c rho eta localCap active θUpper assignUpper δold δlocal ρmatch globalRate:ℝ)
    (hα:0<α) (hε:0<ε) (hε1:ε≤1/4) (hc:0<c) (hrho:0<rho) (heta:0<eta) (hlocal:0<localCap)
    (hactive:0<active) (hθUpper:0<θUpper) (hAssignUpper:0<assignUpper)
    (hδold:0<δold) (hgap:δold<δlocal) (hρmatch:0<ρmatch) (hGlobalRate:0<globalRate):
    ∃t s lamAssign θ lam ξCap:ℝ,
      0<t ∧ t≤localCap ∧ 0<s ∧ 0<lamAssign ∧ lamAssign≤assignUpper ∧
      0<θ ∧ θ≤s ∧ θ≤θUpper ∧
      8*(θ*ε^2+lamAssign*ε)/((ρmatch/4)/40000)<active*ε/128 ∧
      0<lam ∧ 0<ξCap ∧ lam≤s ∧ lam≤globalRate ∧ ξCap≤s ∧ ξCap≤globalRate ∧
      lam≤θ ∧ lam≤α/128 ∧ lam≤δold*ε/32 ∧
      (∀ξ':ℝ,ξ'≤ξCap→lam+ξ'≤((ρmatch/4)/40000)*θ/4096 ∧
        ξ'/2≤(lamAssign-lam)*ε ∧ ξ'≤α/32 ∧
        ∀n:ℕ,∀(U:Type) [Fintype U] (G:SimpleGraph (Fin n)) (D mm:ℕ) (β:ℝ)
          (Q:Vortex U G D β ε mm),0<mm→ξ'*n≤(δlocal-δold)*((Q.extendedVertices 1).card:ℝ)) ∧
    ∃dMin:ℕ,∀d:ℕ,dMin≤d→3≤d ∧ (r+4)+2≤d ∧
      1/(d:ℝ)≤θ/1024 ∧ 1/(d:ℝ)≤(active*ε/128)/10 ∧
      (1/(((r+4:ℕ):ℝ)+1))/(d:ℝ)≤θ ∧
    ∃ζret ζlocal ηBalance κaux:ℝ,
      FirstVortexRetentionBalanceRates r d ε active θ s c ζret ζlocal ηBalance κaux ∧
    ∃KMin N:ℕ,∀K:ℕ,KMin≤K→3≤K ∧
      5/((((r+4:ℕ):ℝ)+1)*(d:ℝ)+5)+(((r+4:ℕ):ℝ)+1)*(d:ℝ)/(K:ℝ)≤θ/2 ∧
      FirstVortexActualSummedLossNumerics r d K N ε c rho eta s θ :=by
  obtain ⟨t,s,lamAssign,θ,lam,ξCap,ht,htcap,hs,hAssign,hAssignUp,hθ,hθs,hθupper,
    hCeiling,hlam,hξ,hlams,hlamglobal,hξs,hξglobal,hlamθ,hlamα,hlamδ,hCap,dMin,hd⟩:=
    first_vortex_ordered_summed_loss_matching_parameters r α ε c rho eta localCap active θUpper assignUpper δold δlocal ρmatch globalRate
      hα hε hc hrho heta hlocal hactive hθUpper hAssignUpper hδold hgap hρmatch hGlobalRate
  refine ⟨t,s,lamAssign,θ,lam,ξCap,ht,htcap,hs,hAssign,hAssignUp,hθ,hθs,hθupper,
    hCeiling,hlam,hξ,hlams,hlamglobal,hξs,hξglobal,hlamθ,hlamα,hlamδ,hCap,dMin,?_⟩
  intro d hdmin
  obtain ⟨hd3,hdr,hspace,hactiveSpace,hcut,KMin,N,hKN⟩:=hd d hdmin
  obtain ⟨ζret,ζlocal,ηBalance,κaux,hret⟩:=
    first_vortex_retention_balance_parameters ε active θ s c r d hε hε1 hactive hθ hs hc (by omega) hspace
  exact ⟨hd3,hdr,hspace,hactiveSpace,hcut,ζret,ζlocal,ηBalance,κaux,hret,KMin,N,hKN⟩
end Oberwolfach

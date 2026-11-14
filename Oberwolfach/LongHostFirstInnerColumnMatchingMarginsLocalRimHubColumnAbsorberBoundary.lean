module

public import Oberwolfach.LongHostEventMatchingFirstInnerColumnLocalRimHubColumnAbsorberBoundary
public import Oberwolfach.LongHostEventSpecializationFirstInnerColumnLocalRimHubColumnAbsorberBoundary
public import Oberwolfach.LongFixedSpacingEventChoicesInnerColumnLocalRimHubColumnAbsorberBoundary
public import Oberwolfach.LongHostEventMatchingFirstInnerColumnLocalFamily
public import Oberwolfach.LongHostEventSpecializationFirstInnerColumnLocalFamily
public import Oberwolfach.LongFixedSpacingEventChoicesInnerColumnLocalFamily
public import Oberwolfach.LongHostEventMatchingFirstInnerColumnRimRow
public import Oberwolfach.LongHostEventSpecializationFirstInnerColumnRimRow
public import Oberwolfach.LongFixedSpacingEventChoicesInnerColumnRimRow
public import Oberwolfach.ResidualLongErrorBudgetBelow
public import Oberwolfach.LongSelectedListMarginsBelow
public import Oberwolfach.LongCompatibleLargeSpacingChoices
public import Oberwolfach.ResidualLongErrorBudget
public import Oberwolfach.LongProtectedPairMargins
public import Oberwolfach.LongHostEventMatchingFirstInnerColumn
public import Oberwolfach.LongHostEventSpecializationFirstInnerColumn
public import Oberwolfach.LongFixedSpacingEventChoicesInnerColumn
public import Oberwolfach.LongSelectedListMargins
public import Oberwolfach.LongCompatibleParameterChoicesAbove
public import Oberwolfach.LongHostCompatibleCommonEventSelectedTests
public import Oberwolfach.LongHostFixedSpacingEventMatchingSelectedTests
public import Oberwolfach.LongHostFixedSpacingEventSpecializationSelectedTests
public import Oberwolfach.LongFixedSpacingEventChoicesSelectedTests
public import Oberwolfach.LongHostFixedSpacingEventMatchingWithStarts
public import Oberwolfach.LongFixedSpacingEventChoicesWithStarts
public import Oberwolfach.LongCompatibleParameterChoices
public import Oberwolfach.LongHostMatchingVortexAliasDecidable

@[expose] public section
/-! Choose the spacing before a sufficiently large long-cycle cutoff, then
assemble the regular-host event and the same-outcome matching. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 40000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
attribute [local instance] referenceWitnessFinDecidable
attribute [local irreducible] HostMatchingVortexContinuation SuppliedVortexFixedSpacingEventWithInnerColumn HostVortexFixedSpacingEventConclusionWithFirstInnerColumnMatchingAndLocalRimHubColumnAbsorberBoundary

theorem long_host_compatible_first_inner_column_with_matching_margins_and_local_rim_hub_column_absorber_boundary
    (L₀:ℕ) (αHost:ℝ) (hαHost:0<αHost):
    ∃m r k₀:ℕ,∃hm:7≤m,∃hLm:L₀≤m,∃heven:Even (m+1),∃hr:2≤r,
    ∃hrm:r+4=m,∃hlen:r+4+1=(k₀+2)*2,
    ∃hmarginHost:successorCycleRatio k₀+αHost/4≤1/2+αHost/2,
    ∃A BM:ℝ,∃hA:0<A,∃hBM:0<BM,
    ∀(ρ₀:ℝ) (hρ₀:0<ρ₀),
    ∃αRef γRich ω pstarRef kstar tstar:ℝ,
    αRef=αHost/2 ∧
    ∃hαRef:0<αRef,∃hγRich:0<γRich,∃hγRich1:γRich≤1/2,∃hγcap:γRich≤αRef,
    ∃hmargin:successorCycleRatio k₀+αRef/2≤1/2+αRef,
    ∃hω:0<ω,∃hpstar:0<pstarRef,∃hkstar:0<kstar,
    ∃htstar:0<tstar,∃htstar100:tstar≤1/100,∃htstar1:tstar≤1,
    ∃hωBound:4*ω≤ρ₀,∃hpstarBound:4*(m:ℝ)*pstarRef≤ρ₀*(1/100),
    ∃htm:tstar≤(1/100)/(m:ℝ),
    (∀ρ:ℝ,ρ₀≤ρ→kstar≤ρ*(1/100)/2 ∧ kstar≤ρ*((1/100)/(m:ℝ))/2) ∧
    ∀(Qpow:ℕ) (hQpow:0<Qpow) (θ:ℝ) (hθ:0<θ) (hθmax:θ≤1/100) (lamMax ζMax ζretMax:ℝ) (hMax:0<lamMax) (hζMax:0<ζMax) (hζretMax:0<ζretMax),
    ∃βList lam ζList:ℝ,0<βList ∧ βList≤1 ∧ ∃hlam:0<lam,∃hlamθ:lam≤θ,lam≤lamMax ∧ 0<ζList ∧ ζList≤ζMax ∧ ζList≤lam/3 ∧
    ∃d K:ℕ,∃hd:2≤d,∃hdlarge:(r+4)+2≤d,∃hK:3≤K,∃hK5:5≤K,∃hinv:1/(d:ℝ)≤θ/1024,
    ∃hcut:(1/((((r+4):ℕ):ℝ)+1))/(d:ℝ)≤θ,
    5/(((((r+4):ℕ):ℝ)+1)*(d:ℝ)+5)+((((r+4):ℕ):ℝ)+1)*(d:ℝ)/(K:ℝ)≤θ/2 ∧
    1/(8*(d:ℝ))≤θ/2 ∧ 1/(4*(d:ℝ))≤(5/64:ℝ)*θ^2 ∧
    (∃N:ℕ,∀n:ℕ,N≤n→5*(n:ℝ)^(3/4:ℝ)≤(5*θ^2*ρ₀/1024)*n) ∧
    (∃NList:ℕ,∀n≥NList,
      (n:ℝ)^(3/4:ℝ)+2*(2*((3*d:ℕ):ℝ)+1)≤αHost*(ρ₀/200)^2*n ∧
      βList*n+(n:ℝ)^(3/4:ℝ)≤αHost*(ρ₀/200)^2*n*θ ∧
      (lam+2*ζList)*n+(n:ℝ)/(8*(d:ℝ))+2*(n:ℝ)^(3/4:ℝ)/d≤βList*n) ∧
    ∃ζret:ℝ,∃hζret:0<ζret,ζret≤ζretMax ∧ ∃Nret:ℕ,
    (∀n:ℕ,Nret≤n→∀q errOrd:ℝ,
      q≤1/((((r+4):ℕ):ℝ)+1)→errOrd≤θ*n→
      (n:ℝ)*q/d+(((((r+4)+1)*d-1:ℕ):ℝ))*(2*((n:ℝ)^(3/4:ℝ)/d)+ζret*n)+errOrd≤4*θ*n) ∧
    ∀(ε₀:ℝ) (hε₀:ε₀<1),
    ∃eps:ℝ,0<eps ∧ eps≤1 ∧ 3*eps≤lam*(θ/(100*(K:ℝ)^2)) ∧
    let alpha:=min (lam/(10*(d:ℝ))) (θ/(200*(K:ℝ)^2))
    let γ:=min (eps/2) (min (1/2:ℝ) (min (lam/(10*(d:ℝ))) (lam/10)))
    0<alpha ∧ alpha≤θ/(200*(K:ℝ)^2) ∧ 0<γ ∧ γ≤eps ∧
    ∃BO:Fin K→ℝ,∃hBO:∀i,0<BO i,
    ∃hαmargin:2*αRef≤αHost,
    ∃htstarBound:tstar≤(1/100)/(((r+4):ℕ):ℝ),
    ∃hkBound':∀ρ:ℝ,ρ₀≤ρ→kstar≤ρ*(1/100)/2 ∧ kstar≤ρ*((1/100)/(((r+4):ℕ):ℝ))/2,
    HostVortexFixedSpacingEventConclusionWithFirstInnerColumnMatchingAndLocalRimHubColumnAbsorberBoundary r k₀ Qpow hr hQpow hlen
      αRef (1/100) ω γRich tstar kstar hαRef (by norm_num) (by norm_num) hω
      hmargin hγRich hγRich1 hγcap htstar htstar1 htstar100 hkstar
      K hK (by simpa only [hrm] using hm) θ ρ₀ hθ hθmax hρ₀ hωBound ζret hζret ε₀ lam hε₀ hlam hlamθ
      eps d hd hcut BM hBM BO hBO αHost A hαHost hαmargin htstarBound hkBound' :=by
  obtain ⟨m,r,k₀,hm,hLm,heven,hr,hrm,hlen,hmarginHost,A,BM,hA,hBM,hhost⟩:=
    long_host_matching_vortex_alias_decidable L₀ αHost hαHost
  subst m
  refine ⟨r+4,r,k₀,hm,hLm,heven,hr,rfl,hlen,hmarginHost,A,BM,hA,hBM,?_⟩
  intro ρ₀ hρ₀
  obtain ⟨αRef,γRich,ω,pstarRef,kstar,tstar,hαRefEq,hαRef,hγRich,hγRich1,hγcap,
    hmargin,hω,hpstar,hkstar,htstar,htstar100,htstar1,hωBound,hpstarBound,htm,hkBound⟩:=
    long_host_adaptive_reference_parameters (r+4) k₀ (le_trans (by decide : 1≤7) hm) αHost ρ₀ hαHost hρ₀ hmarginHost
  refine ⟨αRef,γRich,ω,pstarRef,kstar,tstar,hαRefEq,hαRef,hγRich,hγRich1,hγcap,
    hmargin,hω,hpstar,hkstar,htstar,htstar100,htstar1,hωBound,hpstarBound,htm,hkBound,?_⟩
  intro Qpow hQpow θ hθ hθmax lamMax ζMax ζretMax hMax hζMax hζretMax
  obtain ⟨βList,lam,ζList,hβList,hβList1,hlam,hlamθ,hlamMax,hζList,hζMax',hζlam,dMin,hList⟩:=
    long_selected_list_margins_below θ αHost (ρ₀/200) lamMax ζMax hθ hαHost (by positivity) hMax hζMax
  obtain ⟨Dpair,hPairMargins⟩:=long_protected_pair_margins θ ρ₀ hθ hρ₀
  obtain ⟨d,hd3,hMin,hinv, hcut,hbuffer,hchoice⟩:=long_compatible_large_spacing_choices (r+4) (max (max dMin Dpair) ((r+4)+2)) θ lam hθ hlam
  have hd:2≤d:=by omega
  have hPairMin:max dMin Dpair≤d:=le_trans (le_max_left _ _) hMin
  have hMin':dMin≤d:=le_trans (le_max_left _ _) hPairMin
  have hdlarge:(r+4)+2≤d:=le_trans (le_max_right _ _) hMin
  obtain ⟨hspace,hspace2,hNpair⟩:=hPairMargins d (le_trans (le_max_right _ _) hPairMin)
  obtain ⟨D,hD⟩:=exists_nat_gt (4*((((r+4):ℕ):ℝ)+1)*(d:ℝ)/θ)
  let K:=max D 5
  have hK5:5≤K:=le_max_right _ _
  have hK:3≤K:=by omega
  have hKlarge:4*((((r+4):ℕ):ℝ)+1)*(d:ℝ)/θ≤K:=
    le_of_lt (lt_of_lt_of_le hD (by exact_mod_cast (le_max_left D 5)))
  obtain ⟨_,_,_,_,_,_,_,_,_,_,hfloor⟩:=hchoice K hK
  have hfloor':5/(((((r+4):ℕ):ℝ)+1)*(d:ℝ)+5)+((((r+4):ℕ):ℝ)+1)*(d:ℝ)/(K:ℝ)≤θ/2:=hfloor hKlarge
  obtain ⟨NList,hNList⟩:=hList d hMin' hd
  have hcut':1/(((((r+4):ℕ):ℝ)+1)*(d:ℝ))≤θ:=by
    convert hcut using 1 <;> field_simp
  obtain ⟨ζret,hζret,hζretMax',Nret,hNret⟩:=residual_long_error_budget_below (r+4) d (by omega) (by omega) θ ζretMax hθ hζretMax hcut'
  refine ⟨βList,lam,ζList,hβList,hβList1,hlam,hlamθ,hlamMax,hζList,hζMax',hζlam,d,K,hd,hdlarge,hK,hK5,hinv,hcut,hfloor',hspace,hspace2,hNpair,⟨NList,hNList⟩,ζret,hζret,hζretMax',Nret,hNret,?_⟩
  intro ε₀ hε₀
  obtain ⟨eps,heps,heps1,hepsAssign,halpha,halphaMass,hγ,hγε,hEvent⟩:=
    long_fixed_spacing_event_choices_with_inner_column_and_local_rim_hub_column_absorber_boundary r k₀ Qpow hr hQpow hlen αRef (1/100) ω γRich tstar kstar
      hαRef (by norm_num) (by norm_num) hω hmargin hγRich hγRich1 hγcap htstar htstar1 htstar100 hkstar
      K hK hm θ ρ₀ hθ hθmax hρ₀ hωBound ζret hζret ε₀ lam hε₀ hlam hlamθ d hd hcut hspace
  obtain ⟨BO,hBO,hHost⟩:=hhost K d (by omega) hd
  have hαmargin:2*αRef≤αHost:=by linarith
  have htstarBound:tstar≤(1/100)/(((r+4):ℕ):ℝ):=htm
  have hkBound':∀ρ:ℝ,ρ₀≤ρ→kstar≤ρ*(1/100)/2 ∧ kstar≤ρ*((1/100)/(((r+4):ℕ):ℝ))/2:=hkBound
  refine ⟨eps,heps,heps1,hepsAssign,halpha,halphaMass,hγ,hγε,BO,hBO,hαmargin,htstarBound,hkBound',?_⟩
  apply host_vortex_fixed_spacing_event_with_first_inner_column_matching_and_local_rim_hub_column_absorber_boundary r k₀ Qpow hr hQpow hlen
      αRef (1/100) ω γRich tstar kstar hαRef (by norm_num) (by norm_num) hω
      hmargin hγRich hγRich1 hγcap htstar htstar1 htstar100 hkstar
      K hK hm θ ρ₀ hθ hθmax hρ₀ hωBound ζret hζret ε₀ lam hε₀ hlam hlamθ
      eps d hd hcut BM hBM BO hBO αHost A hαHost hαmargin htstarBound hkBound'
  unfold HostVortexFixedSpacingEventConclusionWithFirstInnerColumnAndLocalRimHubColumnAbsorberBoundary
  exact long_host_fixed_spacing_event_specialization_with_local_rim_hub_column_absorber_boundary r k₀ Qpow hr hQpow hlen
      αRef (1/100) ω γRich tstar kstar hαRef (by norm_num) (by norm_num) hω
      hmargin hγRich hγRich1 hγcap htstar htstar1 htstar100 hkstar
      K hK hm θ ρ₀ hθ hθmax hρ₀ hωBound ζret hζret ε₀ lam hε₀ hlam hlamθ
      eps d hd hcut BM hBM BO hBO αHost A hαHost hαmargin htstarBound hkBound' hHost (hEvent BM hBM BO hBO)
end Oberwolfach

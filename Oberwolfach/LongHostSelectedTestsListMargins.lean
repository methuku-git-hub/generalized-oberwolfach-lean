module

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
attribute [local irreducible] HostMatchingVortexContinuation SuppliedVortexFixedSpacingEventWithSelectedTests HostVortexFixedSpacingEventConclusionWithSelectedTestsMatching

theorem long_host_compatible_selected_tests_with_list_margins
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
    ∀(Qpow:ℕ) (hQpow:0<Qpow) (θ:ℝ) (hθ:0<θ) (hθmax:θ≤1/100),
    ∃βList lam ζList:ℝ,0<βList ∧ βList≤1 ∧ ∃hlam:0<lam,∃hlamθ:lam≤θ,0<ζList ∧
    ∃d K:ℕ,∃hd:2≤d,∃hK:3≤K,
    ∃hcut:(1/((((r+4):ℕ):ℝ)+1))/(d:ℝ)≤θ,
    5/(((((r+4):ℕ):ℝ)+1)*(d:ℝ)+5)+((((r+4):ℕ):ℝ)+1)*(d:ℝ)/(K:ℝ)≤θ/2 ∧
    (∃NList:ℕ,∀n≥NList,
      (n:ℝ)^(3/4:ℝ)+2*(2*((3*d:ℕ):ℝ)+1)≤αHost*(ρ₀/200)^2*n ∧
      βList*n+(n:ℝ)^(3/4:ℝ)≤αHost*(ρ₀/200)^2*n*θ ∧
      (lam+2*ζList)*n+(n:ℝ)/(8*(d:ℝ))+2*(n:ℝ)^(3/4:ℝ)/d≤βList*n) ∧
    ∀(ε₀:ℝ) (hε₀:ε₀<1),
    ∃eps:ℝ,0<eps ∧ eps≤1 ∧ 3*eps≤lam*(θ/(100*(K:ℝ)^2)) ∧
    let alpha:=min (lam/(10*(d:ℝ))) (θ/(200*(K:ℝ)^2))
    let γ:=min (eps/2) (min (1/2:ℝ) (min (lam/(10*(d:ℝ))) (lam/10)))
    0<alpha ∧ alpha≤θ/(200*(K:ℝ)^2) ∧ 0<γ ∧ γ≤eps ∧
    ∃BO:Fin K→ℝ,∃hBO:∀i,0<BO i,
    ∃hαmargin:2*αRef≤αHost,
    ∃htstarBound:tstar≤(1/100)/(((r+4):ℕ):ℝ),
    ∃hkBound':∀ρ:ℝ,ρ₀≤ρ→kstar≤ρ*(1/100)/2 ∧ kstar≤ρ*((1/100)/(((r+4):ℕ):ℝ))/2,
    HostVortexFixedSpacingEventConclusionWithSelectedTestsMatching r k₀ Qpow hr hQpow hlen
      αRef (1/100) ω γRich tstar kstar hαRef (by norm_num) (by norm_num) hω
      hmargin hγRich hγRich1 hγcap htstar htstar1 htstar100 hkstar
      K hK (by simpa only [hrm] using hm) θ ρ₀ hθ hθmax hρ₀ hωBound ε₀ lam hε₀ hlam hlamθ
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
  intro Qpow hQpow θ hθ hθmax
  obtain ⟨βList,lam,ζList,hβList,hβList1,hlam,hlamθ,hζList,dMin,hList⟩:=
    long_selected_list_margins θ αHost (ρ₀/200) hθ hαHost (by positivity)
  obtain ⟨d,hMin,hd,hcut,hbuffer,hchoice⟩:=long_compatible_parameter_choices_above (r+4) dMin θ lam hθ hlam
  obtain ⟨D,hD⟩:=exists_nat_gt (4*((((r+4):ℕ):ℝ)+1)*(d:ℝ)/θ)
  let K:=max D 3
  have hK:3≤K:=le_max_right _ _
  have hKlarge:4*((((r+4):ℕ):ℝ)+1)*(d:ℝ)/θ≤K:=
    le_of_lt (lt_of_lt_of_le hD (by exact_mod_cast (le_max_left D 3)))
  obtain ⟨_,_,_,_,_,_,_,_,_,_,hfloor⟩:=hchoice K hK
  have hfloor':5/(((((r+4):ℕ):ℝ)+1)*(d:ℝ)+5)+((((r+4):ℕ):ℝ)+1)*(d:ℝ)/(K:ℝ)≤θ/2:=hfloor hKlarge
  obtain ⟨NList,hNList⟩:=hList d hMin hd
  refine ⟨βList,lam,ζList,hβList,hβList1,hlam,hlamθ,hζList,d,K,hd,hK,hcut,hfloor',⟨NList,hNList⟩,?_⟩
  intro ε₀ hε₀
  obtain ⟨eps,heps,heps1,hepsAssign,halpha,halphaMass,hγ,hγε,hEvent⟩:=
    long_fixed_spacing_event_choices_with_selected_tests r k₀ Qpow hr hQpow hlen αRef (1/100) ω γRich tstar kstar
      hαRef (by norm_num) (by norm_num) hω hmargin hγRich hγRich1 hγcap htstar htstar1 htstar100 hkstar
      K hK hm θ ρ₀ hθ hθmax hρ₀ hωBound ε₀ lam hε₀ hlam hlamθ d hd hcut
  obtain ⟨BO,hBO,hHost⟩:=hhost K d (by omega) hd
  have hαmargin:2*αRef≤αHost:=by linarith
  have htstarBound:tstar≤(1/100)/(((r+4):ℕ):ℝ):=htm
  have hkBound':∀ρ:ℝ,ρ₀≤ρ→kstar≤ρ*(1/100)/2 ∧ kstar≤ρ*((1/100)/(((r+4):ℕ):ℝ))/2:=hkBound
  refine ⟨eps,heps,heps1,hepsAssign,halpha,halphaMass,hγ,hγε,BO,hBO,hαmargin,htstarBound,hkBound',?_⟩
  apply host_vortex_fixed_spacing_event_with_selected_tests_matching r k₀ Qpow hr hQpow hlen
      αRef (1/100) ω γRich tstar kstar hαRef (by norm_num) (by norm_num) hω
      hmargin hγRich hγRich1 hγcap htstar htstar1 htstar100 hkstar
      K hK hm θ ρ₀ hθ hθmax hρ₀ hωBound ε₀ lam hε₀ hlam hlamθ
      eps d hd hcut BM hBM BO hBO αHost A hαHost hαmargin htstarBound hkBound'
  unfold HostVortexFixedSpacingEventConclusionWithSelectedTests
  exact long_host_fixed_spacing_event_specialization_with_selected_tests r k₀ Qpow hr hQpow hlen
      αRef (1/100) ω γRich tstar kstar hαRef (by norm_num) (by norm_num) hω
      hmargin hγRich hγRich1 hγcap htstar htstar1 htstar100 hkstar
      K hK hm θ ρ₀ hθ hθmax hρ₀ hωBound ε₀ lam hε₀ hlam hlamθ
      eps d hd hcut BM hBM BO hBO αHost A hαHost hαmargin htstarBound hkBound' hHost (hEvent BM hBM BO hBO)
end Oberwolfach

module

public import Oberwolfach.OrdinaryAsymmetricRootFreeFromCleanupProfile
public import Oberwolfach.OrdinaryAsymmetricRootFreeCertificate

@[expose] public section
/-! A fixed cleanup profile and its same-sample root-free finish give the
actual separate-cost certificate used by the two-step vortex chain. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 24000000
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_asymmetric_certificate_from_cleanup_profile
    (m:ℕ) (hm:3≤m) (γ b B p₀ κ:ℝ)
    (hγ:0<γ) (hb:0<b) (hB:0≤B) (hp₀:0<p₀) (hp₀1:p₀≤1) (hκ:0<κ) (hκ1:κ≤1):
    ∃ηhub ζhub a ηend ζlocal δend:ℝ,
      0<ηhub ∧ 0<ζhub ∧ 0<a ∧ a≤1 ∧ 0<ηend ∧ 0<ζlocal ∧ 0<δend ∧
    ∀(b₀:ℕ) (p ρ εsup:ℝ) (hp:0<p) (hp1:p≤1) (hρ:0<ρ) (hsup:0<εsup),∃N:ℕ,
    ∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [DecidableEq V] [DecidableEq U],
    ∀(P Q F:SimpleGraph V) (H:V→U→Prop) (X T:Finset V) (Z W:Finset U)
      (π:Equiv.Perm V) (d:ℕ) (j:Color) (s:U→Color→ℝ)
      (pR pH density tR tH Ledit βe₀ βh₀ βe βh η ell t ν budget deepBudget δsample:ℝ)
      (raw:RawWheelOutcome V U Γ Color),
    OrdinaryCleanupParentProfiles P Q F H π d X Z pR pH density tR tH Ledit βe₀ βh₀ s j raw→
    X.Nonempty→N≤X.card→Fintype.card {u:U // u∉Z}≤X.card^2→
    Fintype.card {v:V // v∉X}≤(ordinaryPhysicalInnerDomain X Z).card^2→
    γ*X.card≤βe₀*Fintype.card (V⊕U)→κ*X.card≤(Z.card:ℝ)→Z.card≤X.card→
    p₀≤pR→p₀≤pH→pH≤1→0≤tR→0≤tH→0≤Ledit→
    tR+Ledit≤δend*X.card→tH+Ledit≤δend*X.card→(∀v,F.degree v≤b₀)→
    OrdinaryMixedHubWeightsInnerScale m b B ηhub Q F H X Z→
    0≤t→Disjoint Q F→(∀v,Q.degree v=2*(Finset.univ.filter (H v)).card)→
    (∀u,(m+1)∣(Finset.univ.filter (fun v=>H v u)).card)→
    βe*Fintype.card (V⊕U)+3*max η ell≤βe₀*Fintype.card (V⊕U)→
    βh*Fintype.card (V⊕U)+2*ell≤βh₀*Fintype.card (V⊕U)→η≤deepBudget→
    ∀(D:OrdinaryRootCoverData Q F H X T Z W (m+1) η ell),
    let Qfactor:=spanningRestriction Q X;
    let Hfactor:=fun v u=>H v u∧v∈X∧u∈Z;
    let n:ℝ:=(ordinaryPhysicalInnerDomain X Z).card;
    (∀σ (O:OrdinaryRootFirstCleanupOutcome Q F H X T Z W (m+1) η ell t ν D σ),
      BoundaryReserveSupportGood (ordinaryBoundaryGraph Q H X Z) p εsup σ→
      OrdinarySampledCoverDegreeGood (ordinaryPhysicalGraph D.rim D.spokes) p δsample σ→
      OrdinaryGeneralRootFirstAsymmetricMargins m Q Qfactor F H Hfactor X T Z W η ell t ν D σ O
        p ρ ζhub ζlocal n εsup βe budget (p*ell+δsample*Fintype.card (V⊕U)))→
    ∀loss:ℝ,loss≤1/8→
    let μ:=FiniteLaw.pi (fun _:Sym2 (V⊕U)=>FiniteLaw.retentionCoin p hp.le hp1);
    1-loss≤μ.probability (OrdinaryGeneralRootFreeSampledCoverCleanupSample m Q F H X T Z W η ell t ν D p βe βh δsample)→
    OrdinaryWheelLikelySeparateCostsCertificate Q F H X T Z W (m+1) budget deepBudget:=by
  obtain ⟨ηhub,ζhub,a,ηend,ζlocal,δend,hηhub,hζhub,ha,ha1,hηend,hζlocal,hδend,hmain⟩:=
    ordinary_asymmetric_root_free_from_cleanup_profile m hm γ b B p₀ κ hγ hb hB hp₀ hp₀1 hκ hκ1
  refine ⟨ηhub,ζhub,a,ηend,ζlocal,δend,hηhub,hζhub,ha,ha1,hηend,hζlocal,hδend,?_⟩
  intro b₀ p ρ εsup hp hp1 hρ hsup
  obtain ⟨N,hN⟩:=hmain b₀ 1 p ρ εsup hp hp1 hρ hsup
  refine ⟨max N 64,?_⟩
  intro V U Γ Color _ _ _ _ _ _ P Q F H X T Z W π d j s pR pH density tR tH Ledit βe₀ βh₀ βe βh
    η ell t ν budget deepBudget δsample raw profile hX hn hJ hI hscale hZX hZX' hpR hpH hpH1 htR htH hL
    hcostR hcostH hF data ht hQF hbal hdiv hmE hmH hdeep D Qfactor Hfactor n hnum loss hloss μ hclean
  have hX64:64≤X.card:=by omega
  have hXV:X.card≤Fintype.card V:=Finset.card_le_univ X
  have hXW:X.card≤Fintype.card (V⊕U):=
    hXV.trans (Fintype.card_le_of_injective (Function.Embedding.inl:V↪V⊕U) Sum.inl_injective)
  have hXn:X.card≤(ordinaryPhysicalInnerDomain X Z).card:=by rw [ordinary_physical_inner_domain_card];omega
  have hx:(64:ℝ)≤X.card:=by exact_mod_cast hX64
  have hw:(64:ℝ)≤Fintype.card (V⊕U):=by exact_mod_cast (show 64≤Fintype.card (V⊕U) by omega)
  have ht':(64:ℝ)≤n:=by
    dsimp [n]
    exact_mod_cast (show 64≤(ordinaryPhysicalInnerDomain X Z).card by omega)
  have hsmallX:1/(X.card:ℝ)≤1/64:=one_div_le_one_div_of_le (by norm_num) hx
  have hsmallW:1/(Fintype.card (V⊕U):ℝ)≤1/64:=one_div_le_one_div_of_le (by norm_num) hw
  have hsmallT:1/n≤1/64:=one_div_le_one_div_of_le (by norm_num) ht'
  let failure:=loss+1/(Fintype.card (V⊕U):ℝ)+1/(X.card:ℝ)+1/n
  have hfailure:failure≤1/4:=by dsimp [failure];linarith only [hloss,hsmallX,hsmallW,hsmallT]
  have hprob:=hN V U Γ Color P Q F H X T Z W π d j s pR pH density tR tH Ledit βe₀ βh₀ βe βh
    η ell t ν budget deepBudget δsample raw profile hX (by omega) hJ hI hscale hZX hZX' hpR hpH hpH1 htR htH hL
    hcostR hcostH hF data ht hQF hbal hdiv hmE hmH hdeep D hnum loss hclean
  apply ordinary_asymmetric_root_free_certificate m Q Qfactor F H Hfactor X T Z W p ρ ζhub ζlocal n εsup t ν η ell
    βe βh δsample failure budget deepBudget budget deepBudget D μ (by omega) hfailure le_rfl le_rfl
  dsimp [failure]
  simp only [pow_one] at hprob
  linarith only [hprob]
end Oberwolfach

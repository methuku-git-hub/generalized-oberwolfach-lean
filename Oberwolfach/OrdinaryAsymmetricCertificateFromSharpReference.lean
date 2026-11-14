module

public import Oberwolfach.OrdinaryAsymmetricCertificateFromSharpCapacity
public import Oberwolfach.OrdinaryRootFirstRootFreeSharpReferencePerHostSampledCover

@[expose] public section
/-! A fixed sharp root reference supplies the cleanup probability used by
the asymmetric per-host certificate, on the same physical sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_asymmetric_certificate_from_sharp_reference
    (m:ℕ) (hm:3≤m) (α:ℝ) (hα:0<α):
    ∃N:ℕ,∀k:ℕ,N≤k→∀ω β bRoot BRoot hpack δ:ℝ,
      0<ω→0<β→0<bRoot→0<BRoot→0<hpack→0<δ→δ<1/4→
    ∃εstar cLinear:ℝ,0<εstar ∧ 0<cLinear ∧
    ∀(γ bHub BHub p₀ κ:ℝ),0<γ→0<bHub→0≤BHub→0<p₀→p₀≤1→0<κ→κ≤1→
    ∃ηhub ζhub a ηend ζlocal δend:ℝ,
      0<ηhub ∧ 0<ζhub ∧ 0<a ∧ a≤1 ∧ 0<ηend ∧ 0<ζlocal ∧ 0<δend ∧
    ∀(b₀:ℕ) (p βe βh ν cap εsup δsample:ℝ),
      0<p→p≤1→0<βe→0<βh→0<ν→0<cap→0<εsup→0<δsample→
    ∃τ:ℝ,τ=ordinarySafeCleanupScale (m+1) p βe (βh/2) ν (min cap 1) ∧ 0<τ ∧ τ≤cap ∧ τ≤1 ∧
    ∀L:ℝ,0≤L→∃ηpack:ℝ,0<ηpack ∧ cLinear*τ≤ηpack ∧ ∃n₀ Nclean:ℕ,
    ∀εgeom:ℝ,0<εgeom→∃Nreserve Ncert:ℕ,
    ∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [DecidableEq U],Nclean≤Fintype.card (V⊕U)→
    ∀(loss:ℝ),0≤loss→loss+2/(Fintype.card (V⊕U):ℝ)≤1/8→
    ∀(P Q F:SimpleGraph V) (H:V→U→Prop) (π:Equiv.Perm V) (d:ℕ)
      (X T:Finset V) (Z W:Finset U) (ηrate ellrate bin cin deep crossLoss:ℝ)
      (D:OrdinaryRootCoverNonrootData Q F H X T Z W (m+1)
        (ηrate*Fintype.card (V⊕U)) (ellrate*Fintype.card (V⊕U)))
      (βparent h εparent ξ ζ f binner cross:ℝ)
      (pR pH density tR tH Ledit βe₀ βh₀:ℝ) (s:U→Color→ℝ) (j:Color) (raw:RawWheelOutcome V U Γ Color),
    hpack≤h-ξ-ζ→T⊆X→W⊆Z→n₀≤Fintype.card ↥(Finset.univ\T)→
    Nreserve≤Fintype.card (↥(Finset.univ\T)⊕↥(Finset.univ\W))→
    1/(Fintype.card (↥(Finset.univ\T)⊕↥(Finset.univ\W)):ℝ)≤loss→
    Nonempty (OrdinaryRootCoverSharpReferenceData P Q F H X T Z W (m+1) k (by omega)
      (ηrate*Fintype.card (V⊕U)) (ellrate*Fintype.card (V⊕U)) bin cin deep crossLoss D
      α ω βparent β bRoot BRoot h δ εparent εstar ηpack ξ ζ p εgeom f binner cross)→
    (T.card:ℝ)≤(βe/4)*Fintype.card (V⊕U)→(W.card:ℝ)≤(βh/2)*Fintype.card (V⊕U)→
    Disjoint Q F→(∀v,(F.degree v:ℝ)≤L)→(∀v,F.degree v≤b₀)→
    OrdinaryCleanupParentProfiles P Q F H π d X Z pR pH density tR tH Ledit βe₀ βh₀ s j raw→
    βe*Fintype.card (V⊕U)+3*max (ηrate*Fintype.card (V⊕U)) (ellrate*Fintype.card (V⊕U))≤βe₀*Fintype.card (V⊕U)→
    βh*Fintype.card (V⊕U)+2*(ellrate*Fintype.card (V⊕U))≤βh₀*Fintype.card (V⊕U)→
    X.Nonempty→Ncert≤X.card→Fintype.card {u:U // u∉Z}≤X.card^2→
    Fintype.card {v:V // v∉X}≤(ordinaryPhysicalInnerDomain X Z).card^2→
    γ*X.card≤βe₀*Fintype.card (V⊕U)→κ*X.card≤(Z.card:ℝ)→Z.card≤X.card→
    p₀≤pR→p₀≤pH→pH≤1→0≤tR→0≤tH→0≤Ledit→
    tR+Ledit≤δend*X.card→tH+Ledit≤δend*X.card→
    OrdinaryMixedHubWeightsInnerScale m bHub BHub ηhub Q F H X Z→
    (∀v,Q.degree v=2*(Finset.univ.filter (H v)).card)→
    (∀u,(m+1)∣(Finset.univ.filter (fun v=>H v u)).card)→
    ∀(rate κh κinner θmatch:ℝ),
    0≤κh→0≤κinner→0<θmatch→θmatch≤ζhub*κh→θmatch≤ζlocal*κinner→
    εsup≤p^2/4→τ+ν≤p^2/4→τ+ν+(p*ellrate+δsample)≤θmatch*p/4→ν+ηrate≤θmatch*p/4→
    p≤4*θmatch→20*Real.sqrt (2*p)≤θmatch/2→2≤θmatch*p*Fintype.card (V⊕U)/4→
    κh*Fintype.card (V⊕U)≤γ*X.card→κinner*Fintype.card (V⊕U)≤(ordinaryPhysicalInnerDomain X Z).card→
    ∀(Kcap Dmax:ℕ),0<Kcap→(2*p)*Fintype.card (V⊕U)≤(Dmax:ℝ)→
    ∀Lconf:ℝ,0≤Lconf→(∀v,(F.degree v:ℝ)≤Lconf)→
    ((Fintype.card (V⊕U)*Dmax*(m+1):ℕ):ℝ)/(Kcap:ℝ)+
      (((m+1:ℕ):ℝ)+3)*(Lconf+1)+2*(2*((2*p)*Fintype.card (V⊕U))+2*((Kcap+Dmax:ℕ):ℝ))+
      (Dmax:ℝ)+((Dmax*(m+1):ℕ):ℝ)+3*Dmax < (βe/4)*Fintype.card (V⊕U)-3*(ν*Fintype.card (V⊕U))→
    ν*Fintype.card (V⊕U)+ηrate*Fintype.card (V⊕U)+2*((2*p)*Fintype.card (V⊕U))+
      ((3*(Kcap+Dmax)+Dmax*(m+1):ℕ):ℝ)≤rate*Fintype.card (V⊕U)→
    OrdinaryWheelLikelySeparateCostsCertificate Q F H X T Z W (m+1)
      (rate*Fintype.card (V⊕U)) (ηrate*Fintype.card (V⊕U)):=by
  obtain ⟨Nroot,hroot⟩:=ordinary_root_first_root_free_sharp_reference_per_host_sampled_cover (m+1) (by omega) α hα
  refine ⟨Nroot,?_⟩
  intro k hk ω β bRoot BRoot hpack δ hω hβ hbRoot hBRoot hhpack hδ hδ1
  obtain ⟨εstar,cLinear,hεstar,hcLinear,hroot⟩:=hroot k hk ω β bRoot BRoot hpack δ hω hβ hbRoot hBRoot hhpack hδ hδ1
  refine ⟨εstar,cLinear,hεstar,hcLinear,?_⟩
  intro γ bHub BHub p₀ κ hγ hbHub hBHub hp₀ hp₀1 hκ hκ1
  obtain ⟨ηhub,ζhub,a,ηend,ζlocal,δend,hηhub,hζhub,ha,ha1,hηend,hζlocal,hδend,hcert⟩:=
    ordinary_asymmetric_certificate_from_sharp_capacity m hm γ bHub BHub p₀ κ hγ hbHub hBHub hp₀ hp₀1 hκ hκ1
  refine ⟨ηhub,ζhub,a,ηend,ζlocal,δend,hηhub,hζhub,ha,ha1,hηend,hζlocal,hδend,?_⟩
  intro b₀ p βe βh ν cap εsup δsample hp hp1 hβe hβh hν hcap hsup hδsample
  obtain ⟨τ,hτeq,hτ,hτcap,hτ1,hroot⟩:=hroot p βe βh ν cap hp hp1 hβe hβh hν hcap δsample hδsample 1
  obtain ⟨Ncert,hcert⟩:=hcert b₀ p εsup hp hp1 hsup
  refine ⟨τ,hτeq,hτ,hτcap,hτ1,?_⟩
  intro L hL
  obtain ⟨ηpack,hηpack,hlinear,n₀,Nclean,hroot⟩:=hroot L hL
  refine ⟨ηpack,hηpack,hlinear,n₀,Nclean,?_⟩
  intro εgeom hεgeom
  obtain ⟨Nreserve,hroot⟩:=hroot εgeom hεgeom
  refine ⟨Nreserve,Ncert,?_⟩
  intro V U Γ Color _ _ _ _ _ _ hn loss hloss hlossSmall P Q F H π d X T Z W ηrate ellrate bin cin deep crossLoss D
    βparent h εparent ξ ζ f binner cross pR pH density tR tH Ledit βe₀ βh₀ s j raw
    hcut hTX hWZ hsize hreserve hlossbound href hT hW hQF hF hFn profile hmE hmH
    hX hnCert hJ hI hscale hZX hZX' hpR hpH hpH1 htR htH hLedit hcostR hcostH data hbal hdiv
    rate κh κinner θmatch hκh hκinner hθ hθh hθe hεsup hsupport hclass hblock hpθ hsqrt horder hκscale hinner
    Kcap Dmax hKcap hDmax Lconf hLconf hFconf hcompletion hcost
  have hTroot:(T.card:ℝ)≤(βe/2)*Fintype.card (V⊕U):=by
    have hnonneg:(0:ℝ)≤Fintype.card (V⊕U):=by positivity
    nlinarith [hT,hβe]
  have hprob:=hroot V U Γ Color hn loss hloss P Q F H π d X T Z W
    (ηrate*Fintype.card (V⊕U)) (ellrate*Fintype.card (V⊕U)) bin cin deep crossLoss D
    βparent h εparent ξ ζ f binner cross pR pH density tR tH Ledit βe₀ βh₀ s j raw
    hcut hTX hWZ hsize hreserve (by simpa only [pow_one] using hlossbound) href hTroot hW hQF hF profile hmE hmH
  have hmE':(βe/2)*Fintype.card (V⊕U)+3*max (ηrate*Fintype.card (V⊕U))
      (ellrate*Fintype.card (V⊕U))≤βe₀*Fintype.card (V⊕U):=by
    have hn0:(0:ℝ)≤Fintype.card (V⊕U):=by positivity
    nlinarith [hβe]
  apply hcert V U Γ Color P Q F H X T Z W π d j s pR pH density tR tH Ledit βe₀ βh₀ (βe/2) βh raw
    profile hX hnCert hJ hI hscale hZX hZX' hpR hpH hpH1 htR htH hLedit hcostR hcostH hFn data hQF hbal hdiv
    τ ν ηrate ellrate rate δsample κh κinner θmatch hτ.le hκh hκinner hθ hθh hθe hεsup hsupport hclass hblock hpθ hsqrt horder
    hκscale hinner hmE' hmH Kcap Dmax hKcap hDmax Lconf hLconf hFconf (by nlinarith only [hT])
    (by convert hcompletion using 1 <;> ring) hcost D.toOrdinaryRootCoverData
    (loss+2/(Fintype.card (V⊕U):ℝ)) hlossSmall
  simpa only [pow_one] using hprob
end Oberwolfach

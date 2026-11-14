module

public import Oberwolfach.OrdinaryVortexAsymmetricPairingGeometryProp
public import Oberwolfach.OrdinaryAsymmetricCertificateFromSharpReference
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

theorem ordinary_asymmetric_vortex_certificate_from_sharp_reference
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
    ∀(V₀ U₀:Type) [Fintype V₀] [Fintype U₀] [LinearOrder V₀] [LinearOrder U₀],
    ∀(G₀:SimpleGraph V₀) (D₀ mv:ℕ) (βv εv:ℝ) (Vort:Vortex U₀ G₀ D₀ βv εv mv) (i:ℕ),
    let V:=markedVortexVertexType Vort i;let U:=markedVortexHubType Vort i;
    letI : DecidableEq V:=Classical.decEq _;letI : DecidableEq U:=Classical.decEq _;
    let X:=markedVortexInnerVertices Vort i;let Z:=markedVortexInnerHubs Vort i;
    ∀(Γ Color:Type) [Fintype Γ] [Fintype Color],Nclean≤Fintype.card (V⊕U)→
    ∀(loss:ℝ),0≤loss→loss+2/(Fintype.card (V⊕U):ℝ)≤1/8→
    ∀(P Q F:SimpleGraph V) (H:V→U→Prop) (π:Equiv.Perm V) (d:ℕ)
      (T:Finset V) (W:Finset U) (ηrate ellrate bin cin deep crossLoss:ℝ)
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
    ∀(ρ₀ εR εH eCoeff:ℝ),tR=εR*X.card→tH=εH*Z.card→βe₀=eCoeff*εv→κ≤ρ₀/8→
    OrdinaryVortexAsymmetricPairingGeometryAt Vort i Ncert ρ₀ δend εR εH Ledit ζhub ζlocal γ eCoeff→
    p₀≤pR→p₀≤pH→pH≤1→0≤tR→0≤tH→0≤Ledit→
    OrdinaryMixedHubWeightsInnerScale m bHub BHub ηhub Q F H X Z→
    (∀v,Q.degree v=2*(Finset.univ.filter (H v)).card)→
    (∀u,(m+1)∣(Finset.univ.filter (fun v=>H v u)).card)→
    ∀(rate θmatch:ℝ),0<θmatch→
    θmatch≤(min (ζhub*γ*(1/4:ℝ)) (ζlocal*(1/4:ℝ))/2)*εv→
    let κh:=γ*(1/4:ℝ)*εv;let κinner:=(1/4:ℝ)*εv;

    εsup≤p^2/4→τ+ν≤p^2/4→τ+ν+(p*ellrate+δsample)≤θmatch*p/4→ν+ηrate≤θmatch*p/4→
    p≤4*θmatch→20*Real.sqrt (2*p)≤θmatch/2→2≤θmatch*p*Fintype.card (V⊕U)/4→
    ∀(Kcap Dmax:ℕ),0<Kcap→(2*p)*Fintype.card (V⊕U)≤(Dmax:ℝ)→
    ∀Lconf:ℝ,0≤Lconf→(∀v,(F.degree v:ℝ)≤Lconf)→
    ((Fintype.card (V⊕U)*Dmax*(m+1):ℕ):ℝ)/(Kcap:ℝ)+
      (((m+1:ℕ):ℝ)+3)*(Lconf+1)+2*(2*((2*p)*Fintype.card (V⊕U))+2*((Kcap+Dmax:ℕ):ℝ))+
      (Dmax:ℝ)+((Dmax*(m+1):ℕ):ℝ)+3*Dmax < (βe/4)*Fintype.card (V⊕U)-3*(ν*Fintype.card (V⊕U))→
    ν*Fintype.card (V⊕U)+ηrate*Fintype.card (V⊕U)+2*((2*p)*Fintype.card (V⊕U))+
      ((3*(Kcap+Dmax)+Dmax*(m+1):ℕ):ℝ)≤rate*Fintype.card (V⊕U)→
    OrdinaryWheelLikelySeparateCostsCertificate Q F H X T Z W (m+1)
      (rate*Fintype.card (V⊕U)) (ηrate*Fintype.card (V⊕U)):=by
  obtain ⟨Nroot,hroot⟩:=ordinary_asymmetric_certificate_from_sharp_reference m hm α hα
  refine ⟨Nroot,?_⟩
  intro k hk ω β bRoot BRoot hpack δ hω hβ hbRoot hBRoot hhpack hδ hδ1
  obtain ⟨εstar,cLinear,hεstar,hcLinear,hroot⟩:=hroot k hk ω β bRoot BRoot hpack δ hω hβ hbRoot hBRoot hhpack hδ hδ1
  refine ⟨εstar,cLinear,hεstar,hcLinear,?_⟩
  intro γ bHub BHub p₀ κ hγ hbHub hBHub hp₀ hp₀1 hκ hκ1
  obtain ⟨ηhub,ζhub,a,ηend,ζlocal,δend,hηhub,hζhub,ha,ha1,hηend,hζlocal,hδend,hroot⟩:=
    hroot γ bHub BHub p₀ κ hγ hbHub hBHub hp₀ hp₀1 hκ hκ1
  refine ⟨ηhub,ζhub,a,ηend,ζlocal,δend,hηhub,hζhub,ha,ha1,hηend,hζlocal,hδend,?_⟩
  intro b₀ p βe βh ν cap εsup δsample hp hp1 hβe hβh hν hcap hsup hδsample
  obtain ⟨τ,hτeq,hτ,hτcap,hτ1,hroot⟩:=hroot b₀ p βe βh ν cap εsup δsample hp hp1 hβe hβh hν hcap hsup hδsample
  refine ⟨τ,hτeq,hτ,hτcap,hτ1,?_⟩
  intro L hL
  obtain ⟨ηpack,hηpack,hlinear,n₀,Nclean,hroot⟩:=hroot L hL
  refine ⟨ηpack,hηpack,hlinear,n₀,Nclean,?_⟩
  intro εgeom hεgeom
  obtain ⟨Nreserve,Ncert,hroot⟩:=hroot εgeom hεgeom
  refine ⟨Nreserve,Ncert,?_⟩
  intro V₀ U₀ _ _ _ _ G₀ D₀ mv βv εv Vort i V U X Z Γ Color _ _ hn loss hloss hlossSmall
    P Q F H π d T W ηrate ellrate bin cin deep crossLoss D
    βparent h εparent ξ ζ f binner cross pR pH density tR tH Ledit βe₀ βh₀ s j raw
    hcut hTX hWZ hsize hreserve hlossbound href hT hW hQF hF hFn profile hmE hmH
    ρ₀ εR εH eCoeff hTR hTH hβe0 hκρ hgeo hpR hpH hpH1 htR htH hLedit data hbal hdiv
    rate θmatch hθpos hθcap κh κinner hεsup hsupport hclass hblock hpθ hsqrt horder
    Kcap Dmax hKcap hDmax Lconf hLconf hFconf hcompletion hcost
  letI : DecidableEq V:=Classical.decEq _
  letI : DecidableEq U:=Classical.decEq _
  dsimp only [OrdinaryVortexAsymmetricPairingGeometryAt] at hgeo
  obtain ⟨hX,hnCert,hZX,hZX',hJ,hI,hcostR,hcostH,hκh,hκinner,hc,hθ,hκscale,hinner,hθh,hθe,hscale⟩:=hgeo
  have hJ':Fintype.card {u:U // u∉Z}≤X.card^2:=by
    convert hJ using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  have hI':Fintype.card {v:V // v∉X}≤(ordinaryPhysicalInnerDomain X Z).card^2:=by
    convert hI using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  have hinner':κinner*Fintype.card (V⊕U)≤(ordinaryPhysicalInnerDomain X Z).card:=by
    convert hinner using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  have hA0:(0:ℝ)≤X.card:=by positivity
  have hκZ:κ*X.card≤(Z.card:ℝ):=(mul_le_mul_of_nonneg_right hκρ hA0).trans hZX
  have hscale':γ*X.card≤βe₀*Fintype.card (V⊕U):=by rw [hβe0];exact hscale
  have hcostR':tR+Ledit≤δend*X.card:=by rw [hTR];exact hcostR
  have hcostH':tH+Ledit≤δend*X.card:=by rw [hTH];exact hcostH
  exact hroot V U Γ Color hn loss hloss hlossSmall P Q F H π d X T Z W ηrate ellrate bin cin deep crossLoss D
    βparent h εparent ξ ζ f binner cross pR pH density tR tH Ledit βe₀ βh₀ s j raw
    hcut hTX hWZ hsize hreserve hlossbound href hT hW hQF hF hFn profile hmE hmH
    hX hnCert hJ' hI' hscale' hκZ hZX' hpR hpH hpH1 htR htH hLedit hcostR' hcostH' data hbal hdiv
    rate κh κinner θmatch hκh.le hκinner.le hθpos (hθcap.trans hθh) (hθcap.trans hθe)
    hεsup hsupport hclass hblock hpθ hsqrt horder hκscale hinner'
    Kcap Dmax hKcap hDmax Lconf hLconf hFconf hcompletion hcost
end Oberwolfach

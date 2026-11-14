module

public import Oberwolfach.OrdinaryAsymmetricFinishSchedule
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

theorem ordinary_vortex_fine_cover_certificate_from_schedule
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
    ∀(Γ Color:Type) [Fintype Γ] [Fintype Color],
    ∀(P Q F:SimpleGraph V) (H:V→U→Prop) (π:Equiv.Perm V) (d:ℕ)
      (T:Finset V) (W:Finset U) (ξroot aLoad lam bin cin deep crossLoss:ℝ),
    let n:ℝ:=Fintype.card (V⊕U);let cover:=10*ξroot*X.card;
    let ell:=max (18*aLoad*Fintype.card V+3*((W.card:ℝ)+T.card))
      (3*aLoad*Fintype.card V*((m:ℝ)+1)+(T.card:ℝ)*((m:ℝ)+1));
    ∀(D:OrdinaryRootCoverNonrootData Q F H X T Z W (m+1) cover ell)
      (βparent h εparent ξ ζ f binner cross:ℝ)
      (pR pH density Ledit ρ₀ εR εH eParent hParent:ℝ)
      (s:U→Color→ℝ) (j:Color) (raw:RawWheelOutcome V U Γ Color),
    hpack≤h-ξ-ζ→T⊆X→W⊆Z→
    Nonempty (OrdinaryRootCoverSharpReferenceData P Q F H X T Z W (m+1) k (by omega)
      cover ell bin cin deep crossLoss D α ω βparent β bRoot BRoot h δ εparent εstar ηpack ξ ζ p εgeom f binner cross)→
    (T.card:ℝ)≤(βe/4)*n→(W.card:ℝ)≤(βh/2)*n→
    Disjoint Q F→(∀v,(F.degree v:ℝ)≤L)→(∀v,F.degree v≤b₀)→
    OrdinaryCleanupParentProfiles P Q F H π d X Z pR pH density (εR*X.card) (εH*Z.card)
      Ledit (eParent*εv) (hParent*εv) s j raw→
    κ≤ρ₀/8→OrdinaryVortexAsymmetricPairingGeometryAt Vort i Ncert ρ₀ δend εR εH Ledit ζhub ζlocal γ eParent→
    p₀≤pR→p₀≤pH→pH≤1→0≤εR→0≤εH→0≤Ledit→
    OrdinaryMixedHubWeightsInnerScale m bHub BHub ηhub Q F H X Z→
    (∀v,Q.degree v=2*(Finset.univ.filter (H v)).card)→
    (∀u,(m+1)∣(Finset.univ.filter (fun v=>H v u)).card)→
    ∀(Nfinish:ℕ) (rate θmatch ellCap finishCap kcap:ℝ),0<θmatch→
    θmatch≤(min (ζhub*γ*(1/4:ℝ)) (ζlocal*(1/4:ℝ))/2)*εv→
    εsup≤p^2/4→p≤4*θmatch→20*Real.sqrt (2*p)≤θmatch/2→
    0≤ξroot→0≤aLoad→0≤lam→lam≤1/4→
    max (max (max (4*n₀) (4*Nreserve)) (max Nclean 64)) (max Ncert Nfinish)≤X.card→
    (T.card:ℝ)+W.card≤lam*Fintype.card V→
    max (18*aLoad+3*lam) ((3*aLoad+lam)*((m:ℝ)+1))≤ellCap→10*ξroot≤finishCap→
    L≤kcap^2*n→
    OrdinaryAsymmetricFinishSchedule m Nfinish eParent hParent εv βe βh θmatch p δsample ellCap finishCap kcap rate ν cap→
    OrdinaryWheelLikelySeparateCostsCertificate Q F H X T Z W (m+1) (rate*n) cover:=by
  obtain ⟨Nroot,hroot⟩:=ordinary_asymmetric_vortex_certificate_from_sharp_reference m hm α hα
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
  intro V₀ U₀ _ _ _ _ G₀ D₀ mv βv εv Vort i V U X Z Γ Color _ _
    P Q F H π d T W ξroot aLoad lam bin cin deep crossLoss n cover ell D
    βparent h εparent ξ ζ f binner cross pR pH density Ledit ρ₀ εR εH eParent hParent s j raw
    hcut hTX hWZ href hT hW hQF hF hFn profile hκρ hgeo hpR hpH hpH1 hεR hεH hLedit data hbal hdiv
    Nfinish rate θmatch ellCap finishCap kcap hθpos hθcap hεsup hpθ hsqrt hξroot haLoad hlam hlam1
    hsize hrootSize hell hcover hLcap hfinish
  letI : DecidableEq V:=Classical.decEq _
  letI : DecidableEq U:=Classical.decEq _
  have hnum:=ordinary_finish_inputs_from_schedule m n₀ Nreserve Nclean Ncert Nfinish X T Z W
    ξroot aLoad lam eParent hParent εv βe βh θmatch p δsample ellCap finishCap kcap rate ν cap τ L
    hξroot haLoad hlam hlam1 hsize hrootSize hell hcover hτ.le hτcap hLcap hfinish
  obtain ⟨ηrate,ellrate,Kcap,Dmax,hη,hηcap,hell0,hellcap,hηeq,helleq,hnCert,hn₀,hreserve,hclean,
    hlossbound,hlossSmall,horder,hK,hDmax,hmargin,hrates,hcompletion,hcost⟩:=hnum
  have hRef':∃D':OrdinaryRootCoverNonrootData Q F H X T Z W (m+1) (ηrate*n) (ellrate*n),
      Nonempty (OrdinaryRootCoverSharpReferenceData P Q F H X T Z W (m+1) k (by omega)
        (ηrate*n) (ellrate*n) bin cin deep crossLoss D' α ω βparent β bRoot BRoot h δ εparent
        εstar ηpack ξ ζ p εgeom f binner cross):=by
    rw [hηeq,helleq]
    exact ⟨D,href⟩
  obtain ⟨D',href'⟩:=hRef'
  have htR:0≤εR*X.card:=by positivity
  have htH:0≤εH*Z.card:=by positivity
  have hh:=hroot V₀ U₀ G₀ D₀ mv βv εv Vort i Γ Color hclean (1/16) (by norm_num) hlossSmall
    P Q F H π d T W ηrate ellrate bin cin deep crossLoss D'
    βparent h εparent ξ ζ f binner cross pR pH density (εR*X.card) (εH*Z.card) Ledit
    (eParent*εv) (hParent*εv) s j raw hcut hTX hWZ hn₀ hreserve hlossbound href' hT hW hQF hF hFn profile
    hmargin.1 hmargin.2 ρ₀ εR εH eParent rfl rfl rfl hκρ hgeo hpR hpH hpH1 htR htH hLedit data hbal hdiv
    rate θmatch hθpos hθcap hεsup hrates.1 hrates.2.1 hrates.2.2 hpθ hsqrt horder
    Kcap Dmax hK hDmax L hL hF hcompletion hcost
  rw [hηeq] at hh
  exact hh
end Oberwolfach

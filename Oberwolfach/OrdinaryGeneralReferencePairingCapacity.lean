module

public import Oberwolfach.OrdinaryGeneralReferenceAndPairing
public import Oberwolfach.OrdinaryGeneralMarginsFromCapacity
public import Oberwolfach.OrdinaryPairingParentHubSize
public import Oberwolfach.OrdinaryRootSmallDeepCompletion

@[expose] public section
/-! The root reference, actual pairing parent and uniform capacity give
    the protected general-wheel finish on one sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 80000000
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_general_reference_pairing_capacity
    (m:ℕ) (hm:3≤m) (α γ κ bFactor BFactor p₀ a εf ηf ζfresh:ℝ) (hα:0<α) (hκ:0<κ) (hζ:0<ζfresh)
    (hfresh:OrdinaryGeneralFreshPairingProbabilityProperty m γ κ bFactor BFactor p₀ a εf ηf ζfresh):
    ∃N:ℕ,∀k:ℕ,N≤k→∀ω β b B hpack δ:ℝ,
      0<ω→0<β→0<b→0<B→0<hpack→0<δ→δ<1/4→
    ∃εstar:ℝ,0<εstar ∧
    ∀(b₀:ℕ) (p βe βh ν cap εsup:ℝ) (hp:0<p) (hp1:p≤1) (hβe:0<βe) (hβh:0<βh)
      (hν:0<ν) (hcap:0<cap) (hsup:0<εsup) (q:ℕ),
    ∃τ:ℝ,0<τ ∧ τ≤cap ∧ ∀L:ℝ,0≤L→∃ηpack:ℝ,0<ηpack ∧ ∃n₀ Nclean:ℕ,
    ∀ε:ℝ,0<ε→∃Nreserve Nfresh:ℕ,
    ∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [DecidableEq U],Nclean≤Fintype.card (V⊕U)→Nfresh≤Fintype.card V→Fintype.card U≤Fintype.card V→
    ∀(loss:ℝ),0≤loss→
    ∀(P Q Qfactor F:SimpleGraph V) (H Hfactor:V→U→Prop) (π:Equiv.Perm V) (d:ℕ)
      (X T:Finset V) (Z W:Finset U) (ηrate ellrate bin cin:ℝ)
      (D:OrdinaryRootCoverNonrootData Q F H X T Z W (m+1)
        (ηrate*Fintype.card (V⊕U)) (ellrate*Fintype.card (V⊕U)))
      (βparent h εparent ξ ζ f binner cross:ℝ)
      (pR pH density tR tH Ledit βe₀ βh₀:ℝ) (s:U→Color→ℝ) (j:Color) (raw:RawWheelOutcome V U Γ Color),
    hpack≤h-ξ-ζ→T⊆X→W⊆Z→n₀≤Fintype.card ↥(Finset.univ\T)→
    Nreserve≤Fintype.card (↥(Finset.univ\T)⊕↥(Finset.univ\W))→
    1/(Fintype.card (↥(Finset.univ\T)⊕↥(Finset.univ\W)):ℝ)^q≤loss→
    Nonempty (OrdinaryRootCoverReferenceData P Q F H X T Z W (m+1) k (by omega)
      (ηrate*Fintype.card (V⊕U)) (ellrate*Fintype.card (V⊕U)) bin cin D
      α ω βparent β b B h δ εparent εstar ηpack ξ ζ p ε f binner cross)→
    (T.card:ℝ)≤((p^3*βe/2)/2)*Fintype.card (V⊕U)→
    Disjoint Q F→(∀v,(F.degree v:ℝ)≤L)→
    OrdinaryCleanupParentProfiles P Q F H π d X Z pR pH density tR tH Ledit βe₀ βh₀ s j raw→
    βe*Fintype.card (V⊕U)+3*max (ηrate*Fintype.card (V⊕U)) (ellrate*Fintype.card (V⊕U))≤βe₀*Fintype.card (V⊕U)→
    βh*Fintype.card (V⊕U)+2*(ellrate*Fintype.card (V⊕U))≤βh₀*Fintype.card (V⊕U)→
    ∀(tw:{v:V // v∉X}→ℝ),
    MixedFreshPairingParentInsideRoots m b₀ γ κ bFactor BFactor p₀ a εf ηf Qfactor F
      (ordinaryPhysicalGraph Qfactor Hfactor) (ordinaryPhysicalGraph F (fun _ _=>False))
      (Function.Embedding.inl:V↪V⊕U) (ordinaryBoundaryHubSet H Z X)
      (fun i=>(ordinaryBoundaryRimSet Q X i).image Sum.inl)
      (fun i=>(ordinaryBoundaryRowSet H X Z i).image Sum.inr) tw→
    εsup≤p^2/4→τ+ν≤p^2/4→
    τ+ν+ellrate≤ζfresh*min (κ/2) 1*p/4→ν+ηrate≤ζfresh*min (κ/2) 1*p/4→
    p≤4*ζfresh*min (κ/2) 1→20*Real.sqrt (2*p)≤ζfresh*min (κ/2) 1/2→
    2≤ζfresh*min (κ/2) 1*p*Fintype.card (V⊕U)/4→
    (∀v,Q.degree v=2*(Finset.univ.filter (H v)).card)→
    (∀u,(m+1)∣(Finset.univ.filter (fun v=>H v u)).card)→
    ordinaryPhysicalGraph Qfactor Hfactor≤spanningRestriction (ordinaryPhysicalGraph Q H) (ordinaryInnerVertices X Z)→
    ∀(Kcap Dmax:ℕ),0<Kcap→(2*p)*Fintype.card (V⊕U)≤(Dmax:ℝ)→
    ∀Lconf rate:ℝ,0≤Lconf→(∀v,(F.degree v:ℝ)≤Lconf)→
    ((Fintype.card (V⊕U)*Dmax*(m+1):ℕ):ℝ)/(Kcap:ℝ)+
      (((m+1:ℕ):ℝ)+3)*(Lconf+1)+2*(2*((2*p)*Fintype.card (V⊕U))+2*((Kcap+Dmax:ℕ):ℝ))+
      (Dmax:ℝ)+((Dmax*(m+1):ℕ):ℝ)+3*Dmax < (βe/2)*Fintype.card (V⊕U)-3*(ν*Fintype.card (V⊕U))→
    ν*Fintype.card (V⊕U)+ηrate*Fintype.card (V⊕U)+2*((2*p)*Fintype.card (V⊕U))+
      ((3*(Kcap+Dmax)+Dmax*(m+1):ℕ):ℝ)≤rate*Fintype.card (V⊕U)→
    let law:=FiniteLaw.pi (fun _:Sym2 (V⊕U)=>FiniteLaw.retentionCoin p hp.le hp1);
    1-(loss+2/(Fintype.card (V⊕U):ℝ)^q)-
      (1/(Fintype.card V:ℝ)^q+1/(Fintype.card (V⊕U):ℝ)^q)≤law.probability (fun σ=>
      OrdinaryGeneralRootFirstCleanupSample m Q F H X T Z W (ηrate*Fintype.card (V⊕U)) (ellrate*Fintype.card (V⊕U))
        (τ*Fintype.card (V⊕U)) (ν*Fintype.card (V⊕U)) D.toOrdinaryRootCoverData p βe βh σ ∧
      OrdinaryGeneralFreshPairingSample m Q Qfactor F H Hfactor X Z p (2*p) ζfresh εsup σ ∧
      OrdinaryProtectedHostCoverDownResult Q F H X T Z W (m+1)
        (rate*Fintype.card (V⊕U)) (rate*Fintype.card (V⊕U))) :=by
  obtain ⟨N,hmain⟩:=ordinary_general_reference_and_pairing m hm α γ κ bFactor BFactor p₀ a εf ηf ζfresh hα hfresh
  refine ⟨N,?_⟩
  intro k hk ω β b B hpack δ hω hβ hb hB hh hδ hδ1
  obtain ⟨εstar,hεstar,hmain⟩:=hmain k hk ω β b B hpack δ hω hβ hb hB hh hδ hδ1
  refine ⟨εstar,hεstar,?_⟩
  intro b₀ p βe βh ν cap εsup hp hp1 hβe hβh hν hcap hsup q
  obtain ⟨τ,hτ,hτcap,hmain⟩:=hmain b₀ p βe βh ν cap εsup (2*p) hp hp1 hβe hβh hν hcap hsup (by positivity) q
  refine ⟨τ,hτ,hτcap,?_⟩
  intro L hL
  obtain ⟨ηpack,hηpack,n₀,Nclean,hmain⟩:=hmain L hL
  refine ⟨ηpack,hηpack,n₀,Nclean,?_⟩
  intro ε hε
  obtain ⟨Nreserve,Nfresh,hmain⟩:=hmain ε hε
  refine ⟨Nreserve,Nfresh,?_⟩
  intro V U Γ Color _ _ _ _ _ _ hn hnFresh hu loss hloss P Q Qfactor F H Hfactor π d X T Z W ηrate ellrate bin cin D
    βparent h εparent ξ ζ f binner cross pR pH density tR tH Ledit βe₀ βh₀ s j raw
    hcut hTX hWZ hsize hreserve hlossbound href hT hQF hF hprofile hmE hmH tw data
    hεsup hsupport hclass hblock hpκ hsqrt horder hbal hdiv hbase Kcap Dmax hKcap hDmax Lconf rate hLconf hFconf hcompletion hcost law
  have hκ':0<min (κ/2) 1:=lt_min (by positivity) (by norm_num)
  have hκone:min (κ/2) 1≤1:=min_le_right _ _
  have hY:=ordinary_pairing_parent_hub_size m b₀ γ κ bFactor BFactor p₀ a εf ηf hκ.le Q Qfactor F H Hfactor X Z tw data hu
  have hT':(T.card:ℝ)≤(βe/2)*Fintype.card (V⊕U):=
    ordinary_root_small_deep_completion p βe (Fintype.card (V⊕U)) T.card hp.le hp1 hβe.le (by positivity) hT
  have hnum:∀σ (O:OrdinaryRootFirstCleanupOutcome Q F H X T Z W (m+1)
      (ηrate*Fintype.card (V⊕U)) (ellrate*Fintype.card (V⊕U))
      (τ*Fintype.card (V⊕U)) (ν*Fintype.card (V⊕U)) D.toOrdinaryRootCoverData σ),
      BoundaryReserveSupportGood (ordinaryBoundaryGraph Q H X Z) p εsup σ→
      OrdinaryGeneralRootFirstMargins m Q Qfactor F H Hfactor X T Z W
        (ηrate*Fintype.card (V⊕U)) (ellrate*Fintype.card (V⊕U))
        (τ*Fintype.card (V⊕U)) (ν*Fintype.card (V⊕U)) D.toOrdinaryRootCoverData σ O p (2*p) ζfresh εsup βe (rate*Fintype.card (V⊕U)):=by
    intro σ O hsample
    exact ordinary_general_margins_from_capacity m Q Qfactor F H Hfactor X T Z W p εsup τ ν ηrate ellrate
      (min (κ/2) 1) ζfresh βe rate D.toOrdinaryRootCoverData σ O hp hp1 hτ.le hκ' hκone hζ
      hεsup hsupport hclass hblock hpκ hsqrt horder hY hsample hbase Kcap Dmax hKcap hDmax Lconf hLconf hFconf hT' hcompletion hcost
  exact hmain V U Γ Color hn hnFresh hu loss hloss P Q Qfactor F H Hfactor π d X T Z W
    (ηrate*Fintype.card (V⊕U)) (ellrate*Fintype.card (V⊕U)) bin cin D
    βparent h εparent ξ ζ f binner cross pR pH density tR tH Ledit βe₀ βh₀ s j raw
    hcut hTX hWZ hsize hreserve hlossbound href hT hQF hF hprofile hmE hmH tw data
    (rate*Fintype.card (V⊕U)) hτ.le hbal hdiv hnum
end Oberwolfach

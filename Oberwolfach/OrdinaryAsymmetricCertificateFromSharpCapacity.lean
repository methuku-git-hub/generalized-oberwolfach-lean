module

public import Oberwolfach.OrdinaryAsymmetricCertificateFromSharpCleanupEvent
public import Oberwolfach.OrdinaryAsymmetricCapacityFromProfile

@[expose] public section
/-! The sharp-reference cleanup event and the ordered asymmetric capacities
give a per-host level certificate without a pairing-parent hypothesis. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 26000000
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_asymmetric_certificate_from_sharp_capacity
    (m:ℕ) (hm:3≤m) (γ b B p₀ κ:ℝ)
    (hγ:0<γ) (hb:0<b) (hB:0≤B) (hp₀:0<p₀) (hp₀1:p₀≤1) (hκ:0<κ) (hκ1:κ≤1):
    ∃ηhub ζhub a ηend ζlocal δend:ℝ,
      0<ηhub ∧ 0<ζhub ∧ 0<a ∧ a≤1 ∧ 0<ηend ∧ 0<ζlocal ∧ 0<δend ∧
    ∀(b₀:ℕ) (p εsup:ℝ) (hp:0<p) (hp1:p≤1) (hsup:0<εsup),∃N:ℕ,
    ∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [DecidableEq V] [DecidableEq U],
    ∀(P Q F:SimpleGraph V) (H:V→U→Prop) (X T:Finset V) (Z W:Finset U)
      (π:Equiv.Perm V) (d:ℕ) (j:Color) (s:U→Color→ℝ)
      (pR pH density tR tH Ledit βe₀ βh₀ βe βh:ℝ) (raw:RawWheelOutcome V U Γ Color),
    OrdinaryCleanupParentProfiles P Q F H π d X Z pR pH density tR tH Ledit βe₀ βh₀ s j raw→
    X.Nonempty→N≤X.card→Fintype.card {u:U // u∉Z}≤X.card^2→
    Fintype.card {v:V // v∉X}≤(ordinaryPhysicalInnerDomain X Z).card^2→
    γ*X.card≤βe₀*Fintype.card (V⊕U)→κ*X.card≤(Z.card:ℝ)→Z.card≤X.card→
    p₀≤pR→p₀≤pH→pH≤1→0≤tR→0≤tH→0≤Ledit→
    tR+Ledit≤δend*X.card→tH+Ledit≤δend*X.card→(∀v,F.degree v≤b₀)→
    OrdinaryMixedHubWeightsInnerScale m b B ηhub Q F H X Z→
    Disjoint Q F→(∀v,Q.degree v=2*(Finset.univ.filter (H v)).card)→
    (∀u,(m+1)∣(Finset.univ.filter (fun v=>H v u)).card)→
    ∀(τ ν η ell rate δsample κh κinner θmatch:ℝ),
    0≤τ→0≤κh→0≤κinner→0<θmatch→θmatch≤ζhub*κh→θmatch≤ζlocal*κinner→
    εsup≤p^2/4→τ+ν≤p^2/4→τ+ν+(p*ell+δsample)≤θmatch*p/4→ν+η≤θmatch*p/4→
    p≤4*θmatch→20*Real.sqrt (2*p)≤θmatch/2→2≤θmatch*p*Fintype.card (V⊕U)/4→
    κh*Fintype.card (V⊕U)≤γ*X.card→κinner*Fintype.card (V⊕U)≤(ordinaryPhysicalInnerDomain X Z).card→
    βe*Fintype.card (V⊕U)+3*max (η*Fintype.card (V⊕U)) (ell*Fintype.card (V⊕U))≤βe₀*Fintype.card (V⊕U)→
    βh*Fintype.card (V⊕U)+2*(ell*Fintype.card (V⊕U))≤βh₀*Fintype.card (V⊕U)→
    ∀(Kcap Dmax:ℕ),0<Kcap→(2*p)*Fintype.card (V⊕U)≤(Dmax:ℝ)→
    ∀Lconf:ℝ,0≤Lconf→(∀v,(F.degree v:ℝ)≤Lconf)→
    (T.card:ℝ)≤(βe/2)*Fintype.card (V⊕U)→
    ((Fintype.card (V⊕U)*Dmax*(m+1):ℕ):ℝ)/(Kcap:ℝ)+
      (((m+1:ℕ):ℝ)+3)*(Lconf+1)+2*(2*((2*p)*Fintype.card (V⊕U))+2*((Kcap+Dmax:ℕ):ℝ))+
      (Dmax:ℝ)+((Dmax*(m+1):ℕ):ℝ)+3*Dmax < (βe/2)*Fintype.card (V⊕U)-3*(ν*Fintype.card (V⊕U))→
    ν*Fintype.card (V⊕U)+η*Fintype.card (V⊕U)+2*((2*p)*Fintype.card (V⊕U))+
      ((3*(Kcap+Dmax)+Dmax*(m+1):ℕ):ℝ)≤rate*Fintype.card (V⊕U)→
    ∀(D:OrdinaryRootCoverData Q F H X T Z W (m+1) (η*Fintype.card (V⊕U)) (ell*Fintype.card (V⊕U))),
    ∀loss:ℝ,loss≤1/8→
    let μ:=FiniteLaw.pi (fun _:Sym2 (V⊕U)=>FiniteLaw.retentionCoin p hp.le hp1);
    1-loss≤μ.probability (fun σ=>
      ((∃O:OrdinaryRootFirstCleanupOutcome Q F H X T Z W (m+1) (η*Fintype.card (V⊕U))
        (ell*Fintype.card (V⊕U)) (τ*Fintype.card (V⊕U)) (ν*Fintype.card (V⊕U)) D σ,
        Disjoint (ordinaryPhysicalGraph (wheelFamilyRim O.cleanup.wheels) (wheelFamilySpokes O.cleanup.wheels))
          (ordinaryDeepRootStar T W)) ∧
      OrdinaryBoundaryExtensionGood (Q\D.rim) (fun v u=>H v u∧¬D.spokes v u) (X\T) βe p σ ∧
      OrdinaryBoundaryHubPairGood (fun v u=>H v u∧¬D.spokes v u) Z βh p σ) ∧
      OrdinarySampledCoverDegreeGood (ordinaryPhysicalGraph D.rim D.spokes) p δsample σ)→
    OrdinaryWheelLikelySeparateCostsCertificate Q F H X T Z W (m+1)
      (rate*Fintype.card (V⊕U)) (η*Fintype.card (V⊕U)):=by
  obtain ⟨ηhub,ζhub,a,ηend,ζlocal,δend,hηhub,hζhub,ha,ha1,hηend,hζlocal,hδend,hmain⟩:=
    ordinary_asymmetric_certificate_from_sharp_cleanup_event m hm γ b B p₀ κ hγ hb hB hp₀ hp₀1 hκ hκ1
  refine ⟨ηhub,ζhub,a,ηend,ζlocal,δend,hηhub,hζhub,ha,ha1,hηend,hζlocal,hδend,?_⟩
  intro b₀ p εsup hp hp1 hsup
  obtain ⟨N,hN⟩:=hmain b₀ p (2*p) εsup hp hp1 (by positivity) hsup
  refine ⟨N,?_⟩
  intro V U Γ Color _ _ _ _ _ _ P Q F H X T Z W π d j s pR pH density tR tH Ledit βe₀ βh₀ βe βh raw
    profile hX hn hJ hI hscale hZX hZX' hpR hpH hpH1 htR htH hL hcostR hcostH hF data hQF hbal hdiv
    τ ν η ell rate δsample κh κinner θmatch hτ hκh hκinner hθ hθh hθe hε hsupport hclass hblock hpθ hsqrt horder
    hκscale hinner hmE hmH Kcap Dmax hKcap hDmax Lconf hLconf hFconf hT hcompletion hcost D loss hloss μ hclean
  have hnum:=ordinary_asymmetric_capacity_from_profile m P Q F H X T Z W π d j s pR pH density tR tH Ledit βe₀ βh₀ γ raw
    profile hX hscale p εsup τ ν η ell κh κinner ζhub ζlocal θmatch (ordinaryPhysicalInnerDomain X Z).card βe rate δsample
    D hp hp1 hτ hκh hκinner hζhub.le hζlocal.le hθ hθh hθe hε hsupport hclass hblock hpθ hsqrt horder hκscale hinner
    Kcap Dmax hKcap hDmax Lconf hLconf hFconf hT hcompletion hcost
  have ht:0≤τ*Fintype.card (V⊕U):=by positivity
  exact hN V U Γ Color P Q F H X T Z W π d j s pR pH density tR tH Ledit βe₀ βh₀ βe βh
    (η*Fintype.card (V⊕U)) (ell*Fintype.card (V⊕U)) (τ*Fintype.card (V⊕U)) (ν*Fintype.card (V⊕U))
    (rate*Fintype.card (V⊕U)) (η*Fintype.card (V⊕U)) δsample raw profile hX hn hJ hI hscale hZX hZX'
    hpR hpH hpH1 htR htH hL hcostR hcostH hF data ht hQF hbal hdiv hmE hmH le_rfl D hnum loss hloss hclean
end Oberwolfach

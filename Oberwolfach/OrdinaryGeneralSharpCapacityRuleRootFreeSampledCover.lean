module

public import Oberwolfach.OrdinaryGeneralSharpReferencePairingCapacityRootFreeSampledCover

@[expose] public section
/-! Name the capacity rule with its packing error fixed before pairing rates. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 60000000
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def OrdinaryGeneralSharpCapacityRuleRootFreeSampledCover
    (m k:ℕ) (hm:3≤m) (α ω β b B hpack δ εstar cLinear:ℝ):Prop :=
    ∀(γ κ bFactor BFactor p₀ a εf ηf ζfresh:ℝ),0<κ→0<ζfresh→
    OrdinaryGeneralFreshPairingProbabilityProperty m γ κ bFactor BFactor p₀ a εf ηf ζfresh→
    ∀(b₀:ℕ) (p βe βh ν cap εsup:ℝ) (hp:0<p) (hp1:p≤1) (hβe:0<βe) (hβh:0<βh)
      (hν:0<ν) (hcap:0<cap) (hsup:0<εsup) (δsample:ℝ) (hδsample:0<δsample) (q:ℕ),
    ∃τ:ℝ,τ=ordinarySafeCleanupScale (m+1) p βe (βh/2) ν (min cap 1) ∧ 0<τ ∧ τ≤cap ∧ τ≤1 ∧ ∀L:ℝ,0≤L→∃ηpack:ℝ,0<ηpack ∧ cLinear*τ≤ηpack ∧ ∃n₀ Nclean:ℕ,
    ∀ε:ℝ,0<ε→∃Nreserve Nfresh:ℕ,
    ∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [DecidableEq U],Nclean≤Fintype.card (V⊕U)→Nfresh≤Fintype.card V→Fintype.card U≤Fintype.card V→
    ∀(loss:ℝ),0≤loss→
    ∀(P Q Qfactor F:SimpleGraph V) (H Hfactor:V→U→Prop) (π:Equiv.Perm V) (d:ℕ)
      (X T:Finset V) (Z W:Finset U) (ηrate ellrate bin cin deep crossLoss:ℝ)
      (D:OrdinaryRootCoverNonrootData Q F H X T Z W (m+1)
        (ηrate*Fintype.card (V⊕U)) (ellrate*Fintype.card (V⊕U)))
      (βparent h εparent ξ ζ f binner cross:ℝ)
      (pR pH density tR tH Ledit βe₀ βh₀:ℝ) (s:U→Color→ℝ) (j:Color) (raw:RawWheelOutcome V U Γ Color),
    hpack≤h-ξ-ζ→T⊆X→W⊆Z→n₀≤Fintype.card ↥(Finset.univ\T)→
    Nreserve≤Fintype.card (↥(Finset.univ\T)⊕↥(Finset.univ\W))→
    1/(Fintype.card (↥(Finset.univ\T)⊕↥(Finset.univ\W)):ℝ)^q≤loss→
    Nonempty (OrdinaryRootCoverSharpReferenceData P Q F H X T Z W (m+1) k (by omega)
      (ηrate*Fintype.card (V⊕U)) (ellrate*Fintype.card (V⊕U)) bin cin deep crossLoss D
      α ω βparent β b B h δ εparent εstar ηpack ξ ζ p ε f binner cross)→
    (T.card:ℝ)≤(βe/4)*Fintype.card (V⊕U)→
    (W.card:ℝ)≤(βh/2)*Fintype.card (V⊕U)→
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
    τ+ν+(p*ellrate+δsample)≤ζfresh*min (κ/2) 1*p/4→ν+ηrate≤ζfresh*min (κ/2) 1*p/4→
    p≤4*ζfresh*min (κ/2) 1→20*Real.sqrt (2*p)≤ζfresh*min (κ/2) 1/2→
    2≤ζfresh*min (κ/2) 1*p*Fintype.card (V⊕U)/4→
    (∀v,Q.degree v=2*(Finset.univ.filter (H v)).card)→
    (∀u,(m+1)∣(Finset.univ.filter (fun v=>H v u)).card)→
    ordinaryPhysicalGraph Qfactor Hfactor≤spanningRestriction (ordinaryPhysicalGraph Q H) (ordinaryInnerVertices X Z)→
    ∀(Kcap Dmax:ℕ),0<Kcap→(2*p)*Fintype.card (V⊕U)≤(Dmax:ℝ)→
    ∀Lconf rate:ℝ,0≤Lconf→(∀v,(F.degree v:ℝ)≤Lconf)→
    ((Fintype.card (V⊕U)*Dmax*(m+1):ℕ):ℝ)/(Kcap:ℝ)+
      (((m+1:ℕ):ℝ)+3)*(Lconf+1)+2*(2*((2*p)*Fintype.card (V⊕U))+2*((Kcap+Dmax:ℕ):ℝ))+
      (Dmax:ℝ)+((Dmax*(m+1):ℕ):ℝ)+3*Dmax < (βe/4)*Fintype.card (V⊕U)-3*(ν*Fintype.card (V⊕U))→
    ν*Fintype.card (V⊕U)+ηrate*Fintype.card (V⊕U)+2*((2*p)*Fintype.card (V⊕U))+
      ((3*(Kcap+Dmax)+Dmax*(m+1):ℕ):ℝ)≤rate*Fintype.card (V⊕U)→
    let law:=FiniteLaw.pi (fun _:Sym2 (V⊕U)=>FiniteLaw.retentionCoin p hp.le hp1);
    1-(loss+2/(Fintype.card (V⊕U):ℝ)^q)-
      (1/(Fintype.card V:ℝ)^q+1/(Fintype.card (V⊕U):ℝ)^q)≤law.probability (fun σ=>
      OrdinaryGeneralRootFreeSampledCoverCleanupSample m Q F H X T Z W (ηrate*Fintype.card (V⊕U)) (ellrate*Fintype.card (V⊕U))
        (τ*Fintype.card (V⊕U)) (ν*Fintype.card (V⊕U)) D.toOrdinaryRootCoverData p (βe/2) βh δsample σ ∧
      OrdinaryGeneralFreshPairingSample m Q Qfactor F H Hfactor X Z p (2*p) ζfresh εsup σ ∧
      OrdinaryProtectedHostCoverDownResult Q F H X T Z W (m+1)
        (rate*Fintype.card (V⊕U)) (ηrate*Fintype.card (V⊕U)))

theorem ordinary_general_sharp_capacity_rule_root_free_sampled_cover_choice
    (m:ℕ) (hm:3≤m) (α:ℝ) (hα:0<α):
    ∃N:ℕ,∀k:ℕ,N≤k→∀ω β b B hpack δ:ℝ,
      0<ω→0<β→0<b→0<B→0<hpack→0<δ→δ<1/4→
    ∃εstar cLinear:ℝ,0<εstar ∧ 0<cLinear ∧ OrdinaryGeneralSharpCapacityRuleRootFreeSampledCover m k hm α ω β b B hpack δ εstar cLinear :=by
  exact ordinary_general_sharp_reference_pairing_capacity_root_free_sampled_cover m hm α hα
end Oberwolfach

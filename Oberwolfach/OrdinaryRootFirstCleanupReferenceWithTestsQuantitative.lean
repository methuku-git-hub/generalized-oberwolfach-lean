module

public import Oberwolfach.OrdinaryRootFirstPackingExpandedInputsLinear
public import Oberwolfach.OrdinaryAdaptiveRootCoverInputsEvent
public import Oberwolfach.OrdinaryRootFirstCleanupRestrictedWithTestsCappedExplicit

@[expose] public section
/-! Starting from a common earlier event carrying an actual root cover,
its pre-reserve reference and cleanup profile, construct the packing and
deep-avoiding cleanup on one expanded sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 24000000
set_option synthInstance.maxSize 8192
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_root_first_cleanup_from_reference_with_tests_quantitative (r:ℕ) (hr:3≤r) (α:ℝ) (hα:0<α):
    ∃N:ℕ,∀k:ℕ,N≤k→∀ω β b B hpack δ:ℝ,
      0<ω→0<β→0<b→0<B→0<hpack→0<δ→δ<1/4→
    ∃εstar cLinear:ℝ,0<εstar ∧ 0<cLinear ∧
    ∀(p βe βh ν cap:ℝ) (hp:0<p) (hp1:p≤1) (hβe:0<βe) (hβh:0<βh) (hν:0<ν) (hcap:0<cap) (q:ℕ),
    ∃τ:ℝ,τ=ordinarySafeCleanupScale r p βe βh ν (min cap 1) ∧ 0<τ ∧ τ≤cap ∧ τ≤1 ∧ ∀L:ℝ,0≤L→∃η:ℝ,0<η ∧ cLinear*τ≤η ∧ ∃n₀ Nclean:ℕ,
    ∀ε:ℝ,0<ε→∃Nreserve:ℕ,
    ∀(V U Γ Color Ω:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [Fintype Ω]
      [LinearOrder V] [DecidableEq U],Nclean≤Fintype.card (V⊕U)→
    ∀(μ:FiniteLaw Ω) (E:Ω→Prop) (e₀ loss:ℝ),0≤loss→1-e₀≤μ.probability E→
    ∀(P Q F:Ω→SimpleGraph V) (H:Ω→V→U→Prop) (π:Equiv.Perm V) (d:ℕ)
      (X T:Ω→Finset V) (Z W:Ω→Finset U) (ηcover ell b₀ c₀:ℝ)
      (D:∀s,OrdinaryRootCoverNonrootData (Q s) (F s) (H s) (X s) (T s) (Z s) (W s) r ηcover ell)
      (βparent h εparent ξ ζ f binner c:ℝ)
      (pR pH density tR tH Ledit βe₀ βh₀:ℝ) (s:U→Color→ℝ) (j:Color) (raw:Ω→RawWheelOutcome V U Γ Color),
    hpack≤h-ξ-ζ→(∀a,E a→T a⊆X a)→(∀a,E a→W a⊆Z a)→
    (∀a,E a→n₀≤Fintype.card ↥(Finset.univ\T a))→
    (∀a,E a→Nreserve≤Fintype.card (↥(Finset.univ\T a)⊕↥(Finset.univ\W a)))→
    (∀a,E a→1/(Fintype.card (↥(Finset.univ\T a)⊕↥(Finset.univ\W a)):ℝ)^q≤loss)→
    (∀a,E a→Nonempty (OrdinaryRootCoverReferenceData (P a) (Q a) (F a) (H a) (X a) (T a) (Z a) (W a)
      r k hr ηcover ell b₀ c₀ (D a) α ω βparent β b B h δ εparent εstar η ξ ζ p ε f binner c))→
    (∀a,E a→((T a).card:ℝ)≤((p^3*βe/2)/2)*Fintype.card (V⊕U))→
    (∀a,E a→Disjoint (Q a) (F a))→(∀a,E a→∀v,((F a).degree v:ℝ)≤L)→
    (∀a,E a→OrdinaryCleanupParentProfiles (P a) (Q a) (F a) (H a) π d (X a) (Z a)
      pR pH density tR tH Ledit βe₀ βh₀ s j (raw a))→
    βe*Fintype.card (V⊕U)+3*max ηcover ell≤βe₀*Fintype.card (V⊕U)→
    βh*Fintype.card (V⊕U)+2*ell≤βh₀*Fintype.card (V⊕U)→
    let law:=FiniteLaw.pi (fun _:Sym2 (V⊕U)=>FiniteLaw.retentionCoin p hp.le hp1);
    1-((e₀+loss)+2/(Fintype.card (V⊕U):ℝ)^q)≤(μ.sigma (fun _=>law)).probability (fun z=>E z.1 ∧
      Nonempty (OrdinaryRootFirstCleanupOutcome (Q z.1) (F z.1) (H z.1) (X z.1) (T z.1) (Z z.1) (W z.1)
        r ηcover ell (τ*Fintype.card (V⊕U)) (ν*Fintype.card (V⊕U)) (D z.1).toOrdinaryRootCoverData z.2) ∧
      OrdinaryBoundaryExtensionGood (Q z.1\(D z.1).rim)
        (fun v u=>H z.1 v u∧¬(D z.1).spokes v u) (X z.1) βe p z.2 ∧
      OrdinaryBoundaryHubPairGood (fun v u=>H z.1 v u∧¬(D z.1).spokes v u) (Z z.1) βh p z.2):=by
  obtain ⟨N,hN⟩:=ordinary_root_first_packing_from_expanded_inputs_linear r hr α hα
  refine ⟨N,?_⟩
  intro k hk ω β b B hpack δ hω hβ hb hB hh hδ hδ1
  obtain ⟨εstar,cLinear,hεstar,hcLinear,hpackrule⟩:=hN k hk ω β b B hpack δ hω hβ hb hB hh hδ hδ1
  refine ⟨εstar,cLinear,hεstar,hcLinear,?_⟩
  intro p βe βh ν cap hp hp1 hβe hβh hν hcap q
  obtain ⟨τ,hτeq,hτ,hτcap,hcleanup⟩:=ordinary_root_first_cleanup_restricted_with_tests_capped_explicit r hr p βe βh ν (min cap 1) hp hp1 hβe hβh hν (by positivity) q
  have hτone:τ≤1:=hτcap.trans (min_le_right _ _)
  refine ⟨τ,hτeq,hτ,hτcap.trans (min_le_left _ _),hτone,?_⟩
  intro L hL
  obtain ⟨Nclean,hNclean⟩:=hcleanup L hL
  obtain ⟨η,hη,hlinear,n₀,hn₀⟩:=hpackrule τ hτ hτone
  refine ⟨η,hη,hlinear,n₀,Nclean,?_⟩
  intro ε hε
  obtain ⟨Nreserve,hNreserve⟩:=ordinary_adaptive_root_cover_inputs_event q ε hε
  refine ⟨Nreserve,?_⟩
  intro V U Γ Color Ω _ _ _ _ _ _ _ hnclean μ E e₀ loss hloss hE P Q F H π d X T Z W ηcover ell b₀ c₀ D
    βparent h εparent ξ ζ f binner c pR pH density tR tH Ledit βe₀ βh₀ s j raw hcut hTX hWZ
    hsize hreserve hlossbound href hT hQF hF hprofile hmE hmH law
  have hinput:=hNreserve V U Ω μ E e₀ loss hloss hE P Q F H X T Z W r k hr ηcover ell b₀ c₀ D
    α ω βparent β b B h δ εparent εstar η ξ ζ p f binner c hp.le hp1 hreserve hlossbound href
  have hpacks:=hn₀ V U Ω μ E (e₀+loss) P Q F H X T Z W ηcover ell D βparent h εparent ξ ζ p ε f binner c
    hp.le hp1 hcut hTX hWZ hsize hinput
  exact hNclean V U Γ Color Ω hnclean μ E (e₀+loss) P Q F H π d X T Z W ηcover ell
    (fun s=>(D s).toOrdinaryRootCoverData) pR pH density tR tH Ledit βe₀ βh₀ s j raw hT hQF hF hprofile hmE hmH hpacks
end Oberwolfach

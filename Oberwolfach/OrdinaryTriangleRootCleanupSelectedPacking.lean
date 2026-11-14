module

public import Oberwolfach.OrdinaryRootFirstCleanupReferenceWithTests
public import Oberwolfach.OrdinaryTrianglePackingSelectedError

@[expose] public section
/-! Construct the root-first packing and cleanup with the exact packing
error selected before the triangle sampling tolerance. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 35000000
set_option synthInstance.maxSize 8192
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_triangle_root_cleanup_selected_packing
    (α:ℝ) (hα:0<α) (k:ℕ) (hk:ordinaryTrianglePackingThreshold α hα≤k)
    (βH cBase Bbase ω pstar δbase hBase:ℝ)
    (hβH:0<βH) (hc:0<cBase) (hB:0<Bbase) (hω:0<ω) (hpstar:0<pstar)
    (hδbase:0<δbase) (hδbase1:δbase<1/4) (hhBase:0<hBase):
    let r:ℕ:=3;let hr:3≤r:=by omega
    let β:=βH/8;let b:=cBase*(1-δbase)^(3-1);let B:=Bbase/(ω*pstar^(2*3-1));
    let hpack:=hBase/2;let δ:=δbase/2;
    let εstar:=ordinaryTrianglePackingError α hα k hk βH cBase Bbase ω pstar δbase hBase
      hβH hc hB hω hpstar hδbase hδbase1 hhBase;
    ∀(p βe βh ν:ℝ) (hp:0<p) (hp1:p≤1) (hβe:0<βe) (hβh:0<βh) (hν:0<ν) (q:ℕ),
    ∃τ:ℝ,0<τ ∧ ∀L:ℝ,0≤L→∃η:ℝ,0<η ∧ ∃n₀ Nclean:ℕ,
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
      OrdinaryBoundaryHubPairGood (fun v u=>H z.1 v u∧¬(D z.1).spokes v u) (Z z.1) βh p z.2) :=by
  intro r hr β b B hpack δ εstar
  have hpacking:=Classical.choose_spec ((Classical.choose_spec
    (ordinary_root_first_packing_from_expanded_inputs 3 (by omega) α hα))
      k hk ω (βH/8) (cBase*(1-δbase)^(3-1)) (Bbase/(ω*pstar^(2*3-1))) (hBase/2) (δbase/2)
      hω (by positivity) (by exact mul_pos hc (pow_pos (by linarith) _)) (by positivity)
      (by positivity) (by positivity) (by linarith))
  have hpackrule:=hpacking.2
  intro p βe βh ν hp hp1 hβe hβh hν q
  obtain ⟨τ,hτ,hcleanup⟩:=ordinary_root_first_cleanup_restricted_with_tests r hr p βe βh ν hp hp1 hβe hβh hν q
  refine ⟨τ,hτ,?_⟩
  intro L hL
  obtain ⟨Nclean,hNclean⟩:=hcleanup L hL
  obtain ⟨η,hη,n₀,hn₀⟩:=hpackrule τ hτ
  refine ⟨η,hη,n₀,Nclean,?_⟩
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

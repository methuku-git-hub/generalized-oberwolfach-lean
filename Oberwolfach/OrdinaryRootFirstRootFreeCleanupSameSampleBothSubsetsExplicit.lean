module

public import Oberwolfach.OrdinarySafeCleanupScale
public import Oberwolfach.OrdinaryRootFirstRootFreeCleanupOutcomeBothSubsetsExplicit
public import Oberwolfach.OrdinaryAttachRootCoverCleanupBothSubsetEventsAtRate

@[expose] public section
/-! Attach the reserve tests to the selected root-first packing and
complete cleanup on that same expanded outcome. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
set_option synthInstance.maxSize 4096
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_root_first_root_free_cleanup_same_sample_both_subsets_explicit (r:ℕ) (hr:3≤r) (p βe βh ν cap:ℝ)
    (hp:0<p) (hp1:p≤1) (hβe:0<βe) (hβh:0<βh) (hν:0<ν) (hcap:0<cap) (q:ℕ):
    ∃τ:ℝ,τ=ordinarySafeCleanupScale r p βe (βh/2) ν cap ∧ 0<τ ∧ τ≤cap ∧ ∀L:ℝ,0≤L→∃N:ℕ,
    ∀(V U Γ Color Ω:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [Fintype Ω]
      [DecidableEq V] [DecidableEq U],N≤Fintype.card (V⊕U)→
    ∀(μ:FiniteLaw Ω) (E:Ω→Prop) (e:ℝ)
      (P Q F:Ω→SimpleGraph V) (H:Ω→V→U→Prop) (π:Equiv.Perm V) (d:ℕ)
      (X T:Ω→Finset V) (Z W:Ω→Finset U) (η ell:ℝ)
      (D:∀a,OrdinaryRootCoverData (Q a) (F a) (H a) (X a) (T a) (Z a) (W a) r η ell)
      (pR pH density tR tH Ledit βe₀ βh₀:ℝ) (s:U→Color→ℝ) (j:Color) (raw:Ω→RawWheelOutcome V U Γ Color),
    (∀a,E a→((T a).card:ℝ)≤(βe/2)*Fintype.card (V⊕U))→
    (∀a,E a→((W a).card:ℝ)≤(βh/2)*Fintype.card (V⊕U))→
    (∀a,E a→Disjoint (Q a) (F a))→(∀a,E a→∀v,((F a).degree v:ℝ)≤L)→
    (∀a,E a→OrdinaryCleanupParentProfiles (P a) (Q a) (F a) (H a) π d (X a) (Z a)
      pR pH density tR tH Ledit βe₀ βh₀ s j (raw a))→
    βe*Fintype.card (V⊕U)+3*max η ell≤βe₀*Fintype.card (V⊕U)→
    βh*Fintype.card (V⊕U)+2*ell≤βh₀*Fintype.card (V⊕U)→
    let law:=FiniteLaw.pi (fun _:Sym2 (V⊕U)=>FiniteLaw.retentionCoin p hp.le hp1);
    1-e≤(μ.sigma (fun _=>law)).probability (fun z=>E z.1 ∧
      ∃K:OrdinaryRootFirstPackingContext (Q z.1) (F z.1) (H z.1) (X z.1) (T z.1) (Z z.1) (W z.1)
        r η ell (τ*Fintype.card (V⊕U)),
      K.cover=D z.1 ∧ K.reserve=retainedGraph (ordinaryBoundaryGraph (Q z.1\(D z.1).rim)
        (fun v u=>H z.1 v u∧¬(D z.1).spokes v u) (X z.1) (Z z.1)) z.2)→
    1-(e+2/(Fintype.card (V⊕U):ℝ)^q)≤(μ.sigma (fun _=>law)).probability (fun z=>E z.1 ∧
      (∃O:OrdinaryRootFirstCleanupOutcome (Q z.1) (F z.1) (H z.1) (X z.1) (T z.1) (Z z.1) (W z.1)
        r η ell (τ*Fintype.card (V⊕U)) (ν*Fintype.card (V⊕U)) (D z.1) z.2,
        Disjoint (ordinaryPhysicalGraph (wheelFamilyRim O.cleanup.wheels) (wheelFamilySpokes O.cleanup.wheels))
          (ordinaryDeepRootStar (T z.1) (W z.1))) ∧
      OrdinaryBoundaryExtensionGood (Q z.1\(D z.1).rim)
        (fun v u=>H z.1 v u∧¬(D z.1).spokes v u) (X z.1\T z.1) (βe/2) p z.2 ∧
      OrdinaryBoundaryHubPairGood (fun v u=>H z.1 v u∧¬(D z.1).spokes v u) (Z z.1) βh p z.2):=by
  obtain ⟨τ,hτeq,hτ,hτcap,hcleanup⟩:=ordinary_root_first_root_free_cleanup_outcome_both_subsets_explicit r hr p βe βh ν cap hp hβe hβh hν hcap
  obtain ⟨Ntest,htest⟩:=ordinary_attach_root_cover_cleanup_both_subset_events_at_rate βe βh p hβe hβh hp hp1 q
  refine ⟨τ,hτeq,hτ,hτcap,?_⟩
  intro L hL
  obtain ⟨Nclean,hclean⟩:=hcleanup L hL
  refine ⟨max Ntest Nclean,?_⟩
  intro V U Γ Color Ω _ _ _ _ _ _ _ hn μ E e P Q F H π d X T Z W η ell D
    pR pH density tR tH Ledit βe₀ βh₀ s j raw hT hW hQF hF hprofile hmE hmH law hpack
  let B:=fun z:(Σ _ : Ω,Sym2 (V⊕U)→Bool)=>E z.1 ∧
      ∃K:OrdinaryRootFirstPackingContext (Q z.1) (F z.1) (H z.1) (X z.1) (T z.1) (Z z.1) (W z.1)
        r η ell (τ*Fintype.card (V⊕U)),
      K.cover=D z.1 ∧ K.reserve=retainedGraph (ordinaryBoundaryGraph (Q z.1\(D z.1).rim)
        (fun v u=>H z.1 v u∧¬(D z.1).spokes v u) (X z.1) (Z z.1)) z.2
  have hj:=htest V U Γ Color Ω (by omega) μ E e B hpack (by intro z hz;exact hz.1)
    P Q F H π d X T Z W r η ell D pR pH density tR tH Ledit βe₀ βh₀ s j raw hT hprofile hmE hmH
  apply hj.trans
  apply finiteLaw_probability_mono
  intro z hz
  obtain ⟨⟨⟨hzE,K,hcover,hreserve⟩,hevent,hhevent⟩,hfree⟩:=hz
  refine ⟨hzE,?_,hevent,hhevent⟩
  exact hclean V U Γ Color (by omega) (P z.1) (Q z.1) (F z.1) (H z.1) π d (X z.1) (T z.1) (Z z.1) (W z.1)
    η ell z.2 (D z.1) pR pH density tR tH Ledit βe₀ βh₀ s j (raw z.1) (hW z.1 hzE) (hQF z.1 hzE)
    (hF z.1 hzE) (hprofile z.1 hzE) hmE hmH K hcover hreserve hevent hfree
end Oberwolfach

module

public import Oberwolfach.OrdinarySafeCleanupScale
public import Oberwolfach.OrdinaryRootFirstCleanupOutcomeFromSample
public import Oberwolfach.OrdinaryAttachRootCoverCleanupEvents
public import Oberwolfach.OrdinaryRootFirstCleanupSameSampleSafeSubsetExplicit
public import Oberwolfach.OrdinaryRootFirstPackingEventWeaken
public import Oberwolfach.OrdinaryNonrootCleanupThreshold

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

theorem ordinary_root_first_cleanup_restricted_safe_subset_explicit (r:ℕ) (hr:3≤r) (p βe βh ν cap:ℝ)
    (hp:0<p) (hp1:p≤1) (hβe:0<βe) (hβh:0<βh) (hν:0<ν) (hcap:0<cap) (q:ℕ):
    ∃τ:ℝ,τ=ordinarySafeCleanupScale r p βe βh ν cap ∧ 0<τ ∧ τ≤cap ∧ ∀L:ℝ,0≤L→∃N:ℕ,
    ∀(V U Γ Color Ω:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [Fintype Ω]
      [DecidableEq V] [DecidableEq U],N≤Fintype.card (V⊕U)→
    ∀(μ:FiniteLaw Ω) (E:Ω→Prop) (e:ℝ)
      (P Q F:Ω→SimpleGraph V) (H:Ω→V→U→Prop) (π:Equiv.Perm V) (d:ℕ)
      (X T:Ω→Finset V) (Z W:Ω→Finset U) (η ell:ℝ)
      (D:∀a,OrdinaryRootCoverData (Q a) (F a) (H a) (X a) (T a) (Z a) (W a) r η ell)
      (pR pH density tR tH Ledit βe₀ βh₀:ℝ) (s:U→Color→ℝ) (j:Color) (raw:Ω→RawWheelOutcome V U Γ Color),
    (∀a,E a→((T a).card:ℝ)≤(βe/2)*Fintype.card (V⊕U))→
    (∀a,E a→Disjoint (Q a) (F a))→(∀a,E a→∀v,((F a).degree v:ℝ)≤L)→
    (∀a,E a→OrdinaryCleanupParentProfiles (P a) (Q a) (F a) (H a) π d (X a) (Z a)
      pR pH density tR tH Ledit βe₀ βh₀ s j (raw a))→
    βe*Fintype.card (V⊕U)+3*max η ell≤βe₀*Fintype.card (V⊕U)→
    βh*Fintype.card (V⊕U)+2*ell≤βh₀*Fintype.card (V⊕U)→
    let law:=FiniteLaw.pi (fun _:Sym2 (V⊕U)=>FiniteLaw.retentionCoin p hp.le hp1);
    1-e≤(μ.sigma (fun _=>law)).probability (fun z=>E z.1 ∧
      ∃K:OrdinaryRootFirstPackingContext (Q z.1) (F z.1) (H z.1) (X z.1) (T z.1) (Z z.1) (W z.1)
        r η ell (τ*Fintype.card (↥(Finset.univ\T z.1)⊕↥(Finset.univ\W z.1))),
      K.cover=D z.1 ∧ K.reserve=retainedGraph (ordinaryBoundaryGraph (Q z.1\(D z.1).rim)
        (fun v u=>H z.1 v u∧¬(D z.1).spokes v u) (X z.1) (Z z.1)) z.2)→
    1-(e+2/(Fintype.card (V⊕U):ℝ)^q)≤(μ.sigma (fun _=>law)).probability (fun z=>E z.1 ∧
      Nonempty (OrdinaryRootFirstCleanupOutcome (Q z.1) (F z.1) (H z.1) (X z.1) (T z.1) (Z z.1) (W z.1)
        r η ell (τ*Fintype.card (V⊕U)) (ν*Fintype.card (V⊕U)) (D z.1) z.2) ∧
      OrdinaryBoundaryExtensionGood (Q z.1\(D z.1).rim)
        (fun v u=>H z.1 v u∧¬(D z.1).spokes v u) (X z.1\T z.1) (βe/2) p z.2 ∧
      OrdinaryBoundaryHubPairGood (fun v u=>H z.1 v u∧¬(D z.1).spokes v u) (Z z.1) βh p z.2) :=by
  obtain ⟨τ,hτeq,hτ,hτcap,hbase⟩:=ordinary_root_first_cleanup_same_sample_safe_subset_explicit r hr p βe βh ν cap hp hp1 hβe hβh hν hcap q
  refine ⟨τ,hτeq,hτ,hτcap,?_⟩
  intro L hL
  obtain ⟨N,hN⟩:=hbase L hL
  refine ⟨N,?_⟩
  intro V U Γ Color Ω _ _ _ _ _ _ _ hn μ E e P Q F H π d X T Z W η ell D
    pR pH density tR tH Ledit βe₀ βh₀ s j raw hT hQF hF hprofile hmE hmH law hpack
  have hw:=ordinary_root_first_packing_event_weaken (μ.sigma (fun _=>law)) (fun z=>E z.1) e
    (fun z=>Q z.1) (fun z=>F z.1) (fun z=>H z.1) (fun z=>X z.1) (fun z=>T z.1)
    (fun z=>Z z.1) (fun z=>W z.1) r η ell
    (fun z=>τ*Fintype.card (↥(Finset.univ\T z.1)⊕↥(Finset.univ\W z.1)))
    (fun _=>τ*Fintype.card (V⊕U)) (fun z=>D z.1)
    (fun z=>retainedGraph (ordinaryBoundaryGraph (Q z.1\(D z.1).rim)
      (fun v u=>H z.1 v u∧¬(D z.1).spokes v u) (X z.1) (Z z.1)) z.2)
    (by intro z _;exact ordinary_nonroot_cleanup_threshold (T z.1) (W z.1) τ hτ.le) hpack
  exact hN V U Γ Color Ω hn μ E e P Q F H π d X T Z W η ell D pR pH density tR tH Ledit βe₀ βh₀ s j raw
    hT hQF hF hprofile hmE hmH hw
end Oberwolfach

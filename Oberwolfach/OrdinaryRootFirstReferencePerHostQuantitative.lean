module

public import Oberwolfach.OrdinaryRootFirstCleanupReferenceWithTestsQuantitative
public import Oberwolfach.OrdinaryTriangleRootFirstSampleEvent
public import Oberwolfach.TwoStageEvents

@[expose] public section
/-! For a fixed admissible host, the root-cover reference supplies the
    root-first cleanup and its post-cover tests on a fresh sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 40000000
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_root_first_reference_per_host_quantitative (r:ℕ) (hr:3≤r) (α:ℝ) (hα:0<α):
    ∃N:ℕ,∀k:ℕ,N≤k→∀ω β b B hpack δ:ℝ,
      0<ω→0<β→0<b→0<B→0<hpack→0<δ→δ<1/4→
    ∃εstar cLinear:ℝ,0<εstar ∧ 0<cLinear ∧
    ∀(p βe βh ν cap:ℝ) (hp:0<p) (hp1:p≤1) (hβe:0<βe) (hβh:0<βh) (hν:0<ν) (hcap:0<cap) (q:ℕ),
    ∃τ:ℝ,τ=ordinarySafeCleanupScale r p βe βh ν (min cap 1) ∧ 0<τ ∧ τ≤cap ∧ τ≤1 ∧ ∀L:ℝ,0≤L→∃η:ℝ,0<η ∧ cLinear*τ≤η ∧ ∃n₀ Nclean:ℕ,
    ∀ε:ℝ,0<ε→∃Nreserve:ℕ,
    ∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [DecidableEq U],Nclean≤Fintype.card (V⊕U)→
    ∀(loss:ℝ),0≤loss→
    ∀(P Q F:SimpleGraph V) (H:V→U→Prop) (π:Equiv.Perm V) (d:ℕ)
      (X T:Finset V) (Z W:Finset U) (ηcover ell b₀ c₀:ℝ)
      (D:OrdinaryRootCoverNonrootData Q F H X T Z W r ηcover ell)
      (βparent h εparent ξ ζ f binner c:ℝ)
      (pR pH density tR tH Ledit βe₀ βh₀:ℝ) (s:U→Color→ℝ) (j:Color) (raw:RawWheelOutcome V U Γ Color),
    hpack≤h-ξ-ζ→T⊆X→W⊆Z→n₀≤Fintype.card ↥(Finset.univ\T)→
    Nreserve≤Fintype.card (↥(Finset.univ\T)⊕↥(Finset.univ\W))→
    1/(Fintype.card (↥(Finset.univ\T)⊕↥(Finset.univ\W)):ℝ)^q≤loss→
    Nonempty (OrdinaryRootCoverReferenceData P Q F H X T Z W r k hr ηcover ell b₀ c₀ D
      α ω βparent β b B h δ εparent εstar η ξ ζ p ε f binner c)→
    (T.card:ℝ)≤((p^3*βe/2)/2)*Fintype.card (V⊕U)→
    Disjoint Q F→(∀v,(F.degree v:ℝ)≤L)→
    OrdinaryCleanupParentProfiles P Q F H π d X Z pR pH density tR tH Ledit βe₀ βh₀ s j raw→
    βe*Fintype.card (V⊕U)+3*max ηcover ell≤βe₀*Fintype.card (V⊕U)→
    βh*Fintype.card (V⊕U)+2*ell≤βh₀*Fintype.card (V⊕U)→
    let law:=FiniteLaw.pi (fun _:Sym2 (V⊕U)=>FiniteLaw.retentionCoin p hp.le hp1);
    1-(loss+2/(Fintype.card (V⊕U):ℝ)^q)≤law.probability (fun σ=>
      Nonempty (OrdinaryRootFirstCleanupOutcome Q F H X T Z W r ηcover ell
        (τ*Fintype.card (V⊕U)) (ν*Fintype.card (V⊕U)) D.toOrdinaryRootCoverData σ) ∧
      OrdinaryBoundaryExtensionGood (Q\D.rim) (fun v u=>H v u∧¬D.spokes v u) X βe p σ ∧
      OrdinaryBoundaryHubPairGood (fun v u=>H v u∧¬D.spokes v u) Z βh p σ) :=by
  obtain ⟨N,hN⟩:=ordinary_root_first_cleanup_from_reference_with_tests_quantitative r hr α hα
  refine ⟨N,?_⟩
  intro k hk ω β b B hpack δ hω hβ hb hB hh hδ hδ1
  obtain ⟨εstar,cLinear,hεstar,hcLinear,hmain⟩:=hN k hk ω β b B hpack δ hω hβ hb hB hh hδ hδ1
  refine ⟨εstar,cLinear,hεstar,hcLinear,?_⟩
  intro p βe βh ν cap hp hp1 hβe hβh hν hcap q
  obtain ⟨τ,hτeq,hτ,hτcap,hτone,hmain⟩:=hmain p βe βh ν cap hp hp1 hβe hβh hν hcap q
  refine ⟨τ,hτeq,hτ,hτcap,hτone,?_⟩
  intro L hL
  obtain ⟨η,hη,hlinear,n₀,Nclean,hmain⟩:=hmain L hL
  refine ⟨η,hη,hlinear,n₀,Nclean,?_⟩
  intro ε hε
  obtain ⟨Nreserve,hmain⟩:=hmain ε hε
  refine ⟨Nreserve,?_⟩
  intro V U Γ Color _ _ _ _ _ _ hn loss hloss P Q F H π d X T Z W ηcover ell b₀ c₀ D
    βparent h εparent ξ ζ f binner c pR pH density tR tH Ledit βe₀ βh₀ s j raw
    hcut hTX hWZ hsize hreserve hlossbound href hT hQF hF hprofile hmE hmH law
  let μ:FiniteLaw Unit:={mass:=fun _=>1,nonneg:=by intro _;norm_num,total:=by simp}
  have hE:1-(0:ℝ)≤μ.probability (fun _:Unit=>True):=by simp [FiniteLaw.probability,μ]
  have hp':=hmain V U Γ Color Unit hn μ (fun _=>True) 0 loss hloss hE
    (fun _=>P) (fun _=>Q) (fun _=>F) (fun _=>H) π d (fun _=>X) (fun _=>T) (fun _=>Z) (fun _=>W)
    ηcover ell b₀ c₀ (fun _=>D) βparent h εparent ξ ζ f binner c
    pR pH density tR tH Ledit βe₀ βh₀ s j (fun _=>raw) hcut
    (by intro _ _;exact hTX) (by intro _ _;exact hWZ) (by intro _ _;exact hsize)
    (by intro _ _;exact hreserve) (by intro _ _;exact hlossbound) (by intro _ _;exact href)
    (by intro _ _;exact hT) (by intro _ _;exact hQF) (by intro _ _;exact hF)
    (by intro _ _;exact hprofile) hmE hmH
  dsimp only at hp'
  rw [finiteLaw_sigma_probability] at hp'
  simpa [FiniteLaw.expectation, μ] using hp'
end Oberwolfach

module

public import Oberwolfach.OrdinaryRootFirstCleanupOutcome
public import Oberwolfach.OrdinaryRootFirstSampledCleanupCapped

@[expose] public section
/-! Package the sampled cleanup together with the original selected
cover, packing and boundary coins. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_root_first_cleanup_outcome_from_sample_capped (r:ℕ) (hr:3≤r) (p βe βh ν cap:ℝ)
    (hp:0<p) (hβe:0<βe) (hβh:0<βh) (hν:0<ν) (hcap:0<cap):
    ∃τ:ℝ,0<τ ∧ τ≤cap ∧ ∀L:ℝ,0≤L→∃N:ℕ,
    ∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [DecidableEq V] [DecidableEq U],N≤Fintype.card (V⊕U)→
    ∀(P Q F:SimpleGraph V) (H:V→U→Prop) (π:Equiv.Perm V) (d:ℕ)
      (X T:Finset V) (Z W:Finset U) (η ell:ℝ) (σ:Sym2 (V⊕U)→Bool)
      (D:OrdinaryRootCoverData Q F H X T Z W r η ell)
      (pR pH density tR tH Ledit βe₀ βh₀:ℝ) (s:U→Color→ℝ) (j:Color)
      (raw:RawWheelOutcome V U Γ Color),
    (T.card:ℝ)≤((p^3*βe/2)/2)*Fintype.card (V⊕U)→
    Disjoint Q F→(∀v,(F.degree v:ℝ)≤L)→
    OrdinaryCleanupParentProfiles P Q F H π d X Z pR pH density tR tH Ledit βe₀ βh₀ s j raw→
    βe*Fintype.card (V⊕U)+3*max η ell≤βe₀*Fintype.card (V⊕U)→
    βh*Fintype.card (V⊕U)+2*ell≤βh₀*Fintype.card (V⊕U)→
    ∀(K:OrdinaryRootFirstPackingContext Q F H X T Z W r η ell (τ*Fintype.card (V⊕U))),
    K.cover=D→K.reserve=retainedGraph (ordinaryBoundaryGraph (Q\D.rim)
      (fun v u=>H v u∧¬D.spokes v u) X Z) σ→
    OrdinaryBoundaryExtensionGood (Q\D.rim) (fun v u=>H v u∧¬D.spokes v u) X βe p σ→
    OrdinaryBoundaryHubPairGood (fun v u=>H v u∧¬D.spokes v u) Z βh p σ→
    Nonempty (OrdinaryRootFirstCleanupOutcome Q F H X T Z W r η ell
      (τ*Fintype.card (V⊕U)) (ν*Fintype.card (V⊕U)) D σ):=by
  obtain ⟨τ,hτ,hτcap,hcleanup⟩:=ordinary_root_first_sampled_cleanup_capped r hr p βe βh ν cap hp hβe hβh hν hcap
  refine ⟨τ,hτ,hτcap,?_⟩
  intro L hL
  obtain ⟨N,hN⟩:=hcleanup L hL
  refine ⟨N,?_⟩
  intro V U Γ Color _ _ _ _ _ _ hn P Q F H π d X T Z W η ell σ D
    pR pH density tR tH Ledit βe₀ βh₀ s j raw hT hQF hF profile hmE hmH K hcover hreserve hevent hhevent
  have hrsv:K.reserve=retainedGraph (ordinaryBoundaryGraph (Q\K.cover.rim)
      (fun v u=>H v u∧¬K.cover.spokes v u) X Z) σ:=by rw [hcover];exact hreserve
  have he:OrdinaryBoundaryExtensionGood (Q\K.cover.rim)
      (fun v u=>H v u∧¬K.cover.spokes v u) X βe p σ:=by rw [hcover];exact hevent
  have hh:OrdinaryBoundaryHubPairGood (fun v u=>H v u∧¬K.cover.spokes v u) Z βh p σ:=by
    rw [hcover];exact hhevent
  obtain ⟨C,hdeep⟩:=hN V U Γ Color hn P Q F H π d X T Z W η ell σ pR pH density tR tH Ledit βe₀ βh₀
    s j raw hT hQF hF profile hmE hmH K hrsv he hh
  exact ⟨⟨K,hcover,hreserve,C,hdeep⟩⟩
end Oberwolfach

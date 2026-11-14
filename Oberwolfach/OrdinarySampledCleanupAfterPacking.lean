module

public import Oberwolfach.OrdinaryCleanupAfterPackingFacts
public import Oberwolfach.OrdinaryCleanupCountsAfterPacking

@[expose] public section
/-! Complete sparse outside cleanup after an unreserved packing on the same
common and fresh samples, without assuming its extension counts separately. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
set_option synthInstance.maxSize 2048
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_sampled_cleanup_after_packing (r:ℕ) (hr:3≤r) (p βe βh ν:ℝ)
    (hp:0<p) (hβe:0<βe) (hβh:0<βh) (hν:0<ν):
    ∃τ:ℝ,0<τ ∧ ∀L:ℝ,0≤L→∃N:ℕ,
    ∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [DecidableEq V] [DecidableEq U],N≤Fintype.card (V⊕U)→
    ∀(P Q F:SimpleGraph V) (H:V→U→Prop) (π:Equiv.Perm V) (d:ℕ)
      (X:Finset V) (Z:Finset U) (pR pH density tR tH Ledit:ℝ)
      (s:U→Color→ℝ) (j:Color) (raw:RawWheelOutcome V U Γ Color) (σ:Sym2 (V⊕U)→Bool),
    OrdinaryCleanupParentProfiles P Q F H π d X Z pR pH density tR tH Ledit βe βh s j raw→
    (∀v,(F.degree v:ℝ)≤L)→
    (∀v,Q.degree v=2*(Finset.univ.filter (H v)).card)→
    (∀u,r∣(Finset.univ.filter (fun v=>H v u)).card)→
    OrdinaryBoundaryExtensionGood Q H X βe p σ→OrdinaryBoundaryHubPairGood H Z βh p σ→
    let R:=retainedGraph (ordinaryBoundaryGraph Q H X Z) σ;
    ∀(M:OrdinaryUnreservedPackingData Q F H X Z R r (τ*Fintype.card (V⊕U))),
    Nonempty (OrdinaryOutsideCleanupData
      (ordinaryPackingPostRim Q F H X Z R r (τ*Fintype.card (V⊕U)) M) F
      (ordinaryPackingPostSpokes Q F H X Z R r (τ*Fintype.card (V⊕U)) M) X Z
      (ordinaryPackingUsedGraph Q F H X Z R r (τ*Fintype.card (V⊕U)) M) r
      (ν*Fintype.card (V⊕U))):=by
  have hbV:0<p^3*βe/2:=by positivity
  have hbU:0<p^2*βh/2:=by positivity
  obtain ⟨τ,hτ,hcleanup⟩:=ordinary_cleanup_after_packing_facts r hr (p^3*βe/2) (p^2*βh/2) ν hbV hbU hν
  refine ⟨τ,hτ,?_⟩
  intro L hL
  obtain ⟨N,hN⟩:=hcleanup L hL
  refine ⟨N,?_⟩
  intro V U Γ Color _ _ _ _ _ _ hn P Q F H π d X Z pR pH density tR tH Ledit s j raw σ
    profile hF hbal hdiv hevent hhevent R M
  have hfacts:=ordinary_packing_post_facts Q F H X Z R r (τ*Fintype.card (V⊕U)) M hbal hdiv
  have hcounts:=ordinary_cleanup_counts_after_packing P Q F H π d r X Z pR pH p density tR tH Ledit βe βh
    (τ*Fintype.card (V⊕U)) s j raw σ profile hevent hhevent M hfacts
  exact hN V U hn Q F H X Z σ profile.forbidden_disjoint hF M hfacts hcounts.1 hcounts.2
end Oberwolfach

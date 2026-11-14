module

public import Oberwolfach.OrdinarySampledCleanupAfterPacking
public import Oberwolfach.OrdinaryPackingDataWeaken
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

theorem ordinary_sampled_cleanup_after_packing_capped (r:ℕ) (hr:3≤r) (p βe βh ν cap:ℝ)
    (hp:0<p) (hβe:0<βe) (hβh:0<βh) (hν:0<ν) (hcap:0<cap):
    ∃τ:ℝ,0<τ ∧ τ≤cap ∧ ∀L:ℝ,0≤L→∃N:ℕ,
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
  obtain ⟨τ₀,hτ₀,hcleanup⟩:=ordinary_sampled_cleanup_after_packing r hr p βe βh ν hp hβe hβh hν
  let τ:=min (τ₀/2) (cap/2)
  have hτ:0<τ:=by dsimp [τ];positivity
  have hτ₀':τ≤τ₀:=by have hh:=min_le_left (τ₀/2) (cap/2);linarith
  have hτcap:τ≤cap:=by have hh:=min_le_right (τ₀/2) (cap/2);linarith
  refine ⟨τ,hτ,hτcap,?_⟩
  intro L hL
  obtain ⟨N,hN⟩:=hcleanup L hL
  refine ⟨N,?_⟩
  intro V U Γ Color _ _ _ _ _ _ hn P Q F H π d X Z pR pH density tR tH Ledit s j raw σ
    profile hF hbal hdiv hevent hhevent R M
  have hscale:τ*Fintype.card (V⊕U)≤τ₀*Fintype.card (V⊕U):=
    mul_le_mul_of_nonneg_right hτ₀' (Nat.cast_nonneg _)
  let M':=ordinaryPackingDataWeaken Q F H X Z R r (τ*Fintype.card (V⊕U))
    (τ₀*Fintype.card (V⊕U)) hscale M
  exact hN V U Γ Color hn P Q F H π d X Z pR pH density tR tH Ledit s j raw σ
    profile hF hbal hdiv hevent hhevent M'
end Oberwolfach

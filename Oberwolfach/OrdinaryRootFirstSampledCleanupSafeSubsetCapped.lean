module

public import Oberwolfach.OrdinaryRootFirstSampledCleanupSafeSubset
public import Oberwolfach.OrdinaryRootFirstPackingBoundMono
public import Oberwolfach.OrdinaryRootFirstCleanupCountsFromProfile

@[expose] public section
/-! Apply deep-avoiding sparse cleanup to the actual root-first packing,
using the pre-cover profile and the same boundary sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_root_first_sampled_cleanup_safe_subset_capped (r:ℕ) (hr:3≤r) (p βe βh ν cap:ℝ)
    (hp:0<p) (hβe:0<βe) (hβh:0<βh) (hν:0<ν) (hcap:0<cap):
    ∃τ:ℝ,0<τ ∧ τ≤cap ∧ ∀L:ℝ,0≤L→∃N:ℕ,
    ∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [DecidableEq V] [DecidableEq U],N≤Fintype.card (V⊕U)→
    ∀(P Q F:SimpleGraph V) (H:V→U→Prop) (π:Equiv.Perm V) (d:ℕ)
      (X T:Finset V) (Z W:Finset U) (η ell:ℝ) (σ:Sym2 (V⊕U)→Bool)
      (pR pH density tR tH Ledit βe₀ βh₀:ℝ) (s:U→Color→ℝ) (j:Color)
      (raw:RawWheelOutcome V U Γ Color),
    Disjoint Q F→(∀v,(F.degree v:ℝ)≤L)→
    OrdinaryCleanupParentProfiles P Q F H π d X Z pR pH density tR tH Ledit βe₀ βh₀ s j raw→
    βe*Fintype.card (V⊕U)+3*max η ell≤βe₀*Fintype.card (V⊕U)→
    βh*Fintype.card (V⊕U)+2*ell≤βh₀*Fintype.card (V⊕U)→
    ∀(K:OrdinaryRootFirstPackingContext Q F H X T Z W r η ell (τ*Fintype.card (V⊕U))),
    K.reserve=retainedGraph (ordinaryBoundaryGraph (Q\K.cover.rim)
      (fun v u=>H v u∧¬K.cover.spokes v u) X Z) σ→
    OrdinaryBoundaryExtensionGood (Q\K.cover.rim)
      (fun v u=>H v u∧¬K.cover.spokes v u) (X\T) (βe/2) p σ→
    OrdinaryBoundaryHubPairGood (fun v u=>H v u∧¬K.cover.spokes v u) Z βh p σ→
    let A:=Finset.univ\T;let B:=Finset.univ\W;
    let φ:A↪V:=⟨Subtype.val,Subtype.val_injective⟩;
    let ψ:B↪U:=⟨Subtype.val,Subtype.val_injective⟩;
    let Q₀:=Q\K.cover.rim;let H₀:=fun v u=>H v u∧¬K.cover.spokes v u;
    let D:=(ordinaryWheelRimGraph K.packing.wheels).map φ;
    let E:=ordinaryMappedSpokes (ordinaryPackingSpokes K.packing.wheels) φ ψ;
    let C:=ordinaryPhysicalGraph D E;
    let Q':=Q₀\D;let H':=fun v u=>H₀ v u∧¬E v u;
    ∃K':OrdinaryOutsideCleanupData Q' F H' X Z C r (ν*Fintype.card (V⊕U)),
      Disjoint (ordinaryPhysicalGraph (wheelFamilyRim K'.wheels) (wheelFamilySpokes K'.wheels)) (ordinaryDeepBlocker T W):=by
  obtain ⟨τ₀,hτ₀,hcleanup⟩:=ordinary_root_first_sampled_cleanup_safe_subset r hr p βe βh ν hp hβe hβh hν
  let τ:=min τ₀ cap
  have hτ:0<τ:=lt_min hτ₀ hcap
  have hτ₀cap:τ≤τ₀:=min_le_left _ _
  refine ⟨τ,hτ,min_le_right _ _,?_⟩
  intro L hL
  obtain ⟨N,hN⟩:=hcleanup L hL
  refine ⟨N,?_⟩
  intro V U Γ Color _ _ _ _ _ _ hn P Q F H π d X T Z W η ell σ pR pH density tR tH Ledit βe₀ βh₀ s j raw
    hQF hF profile hmE hmH K hreserve hevent hhevent
  have hscale:τ*Fintype.card (V⊕U)≤τ₀*Fintype.card (V⊕U):=
    mul_le_mul_of_nonneg_right hτ₀cap (Nat.cast_nonneg _)
  let K₀:=K.increaseBound hscale
  have hclean:=hN V U Γ Color hn P Q F H π d X T Z W η ell σ pR pH density tR tH Ledit βe₀ βh₀
    s j raw hQF hF profile hmE hmH K₀ hreserve hevent hhevent
  exact hclean
end Oberwolfach

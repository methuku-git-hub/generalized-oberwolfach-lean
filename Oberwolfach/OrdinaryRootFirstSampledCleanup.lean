module

public import Oberwolfach.OrdinaryRootFirstCleanupGivenCounts
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

theorem ordinary_root_first_sampled_cleanup (r:ℕ) (hr:3≤r) (p βe βh ν:ℝ)
    (hp:0<p) (hβe:0<βe) (hβh:0<βh) (hν:0<ν):
    ∃τ:ℝ,0<τ ∧ ∀L:ℝ,0≤L→∃N:ℕ,
    ∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [DecidableEq V] [DecidableEq U],N≤Fintype.card (V⊕U)→
    ∀(P Q F:SimpleGraph V) (H:V→U→Prop) (π:Equiv.Perm V) (d:ℕ)
      (X T:Finset V) (Z W:Finset U) (η ell:ℝ) (σ:Sym2 (V⊕U)→Bool)
      (pR pH density tR tH Ledit βe₀ βh₀:ℝ) (s:U→Color→ℝ) (j:Color)
      (raw:RawWheelOutcome V U Γ Color),
    (T.card:ℝ)≤((p^3*βe/2)/2)*Fintype.card (V⊕U)→
    Disjoint Q F→(∀v,(F.degree v:ℝ)≤L)→
    OrdinaryCleanupParentProfiles P Q F H π d X Z pR pH density tR tH Ledit βe₀ βh₀ s j raw→
    βe*Fintype.card (V⊕U)+3*max η ell≤βe₀*Fintype.card (V⊕U)→
    βh*Fintype.card (V⊕U)+2*ell≤βh₀*Fintype.card (V⊕U)→
    ∀(K:OrdinaryRootFirstPackingContext Q F H X T Z W r η ell (τ*Fintype.card (V⊕U))),
    K.reserve=retainedGraph (ordinaryBoundaryGraph (Q\K.cover.rim)
      (fun v u=>H v u∧¬K.cover.spokes v u) X Z) σ→
    OrdinaryBoundaryExtensionGood (Q\K.cover.rim)
      (fun v u=>H v u∧¬K.cover.spokes v u) X βe p σ→
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
  have hbV:0<p^3*βe/2:=by positivity
  have hbU:0<p^2*βh/2:=by positivity
  obtain ⟨τ,hτ,hcleanup⟩:=ordinary_root_first_cleanup_given_counts r hr (p^3*βe/2) (p^2*βh/2) ν hbV hbU hν
  refine ⟨τ,hτ,?_⟩
  intro L hL
  obtain ⟨N,hN⟩:=hcleanup L hL
  refine ⟨N,?_⟩
  intro V U Γ Color _ _ _ _ _ _ hn P Q F H π d X T Z W η ell σ pR pH density tR tH Ledit βe₀ βh₀ s j raw
    hT hQF hF profile hmE hmH K hreserve hevent hhevent A B φ ψ Q₀ H₀ D E C Q' H'
  have ht:0≤τ*Fintype.card (V⊕U):=mul_nonneg hτ.le (Nat.cast_nonneg _)
  have hc:=ordinary_root_first_cleanup_counts_from_profile P Q F H π d X T Z W r η ell _ K ht
    pR pH p density tR tH Ledit βe₀ βh₀ βe βh s j raw σ hreserve profile hmE hmH hevent hhevent
  apply hN V U hn Q F H X T Z W η ell σ hT hQF hF K hreserve
  · intro u a c
    convert hc.1 u a c using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  · intro a ha c hc' hac
    convert hc.2 a ha c hc' hac using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
end Oberwolfach

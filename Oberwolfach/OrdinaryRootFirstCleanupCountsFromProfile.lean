module

public import Oberwolfach.OrdinaryRootFirstCleanupCountsFromEvents
public import Oberwolfach.OrdinaryRootCoverCleanupParentCounts

@[expose] public section
/-! The pre-cover sample profile and the same reserve events supply both
cleanup counts for the actual root-first packing. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]

theorem ordinary_root_first_cleanup_counts_from_profile
    (P Q F:SimpleGraph V) (H:V→U→Prop) (π:Equiv.Perm V) (d:ℕ)
    (X T:Finset V) (Z W:Finset U) (r:ℕ) (η ell t:ℝ)
    (K:OrdinaryRootFirstPackingContext Q F H X T Z W r η ell t) (ht:0≤t)
    (pR pH p density tR tH L βe₀ βh₀ βe βh:ℝ) (s:U→Color→ℝ) (j:Color)
    (raw:RawWheelOutcome V U Γ Color) (σ:Sym2 (V⊕U)→Bool)
    (hreserve:K.reserve=retainedGraph (ordinaryBoundaryGraph (Q\K.cover.rim)
      (fun v u=>H v u∧¬K.cover.spokes v u) X Z) σ)
    (profile:OrdinaryCleanupParentProfiles P Q F H π d X Z pR pH density tR tH L βe₀ βh₀ s j raw)
    (hmE:βe*Fintype.card (V⊕U)+3*max η ell≤βe₀*Fintype.card (V⊕U))
    (hmH:βh*Fintype.card (V⊕U)+2*ell≤βh₀*Fintype.card (V⊕U))
    (hevent:OrdinaryBoundaryExtensionGood (Q\K.cover.rim)
      (fun v u=>H v u∧¬K.cover.spokes v u) X βe p σ)
    (hhevent:OrdinaryBoundaryHubPairGood (fun v u=>H v u∧¬K.cover.spokes v u) Z βh p σ):
    let A:=Finset.univ\T;let B:=Finset.univ\W;
    let φ:A↪V:=⟨Subtype.val,Subtype.val_injective⟩;
    let ψ:B↪U:=⟨Subtype.val,Subtype.val_injective⟩;
    let Q₀:=Q\K.cover.rim;let H₀:=fun v u=>H v u∧¬K.cover.spokes v u;
    let D:=(ordinaryWheelRimGraph K.packing.wheels).map φ;
    let E:=ordinaryMappedSpokes (ordinaryPackingSpokes K.packing.wheels) φ ψ;
    let Q':=Q₀\D;let H':=fun v u=>H₀ v u∧¬E v u;
    (∀u a c,(p^3*βe/2)*Fintype.card (V⊕U)≤
      (((X.filter (fun v=>H' v u))∩Q'.neighborFinset a∩Q'.neighborFinset c).card:ℝ)) ∧
    (∀a∉X,∀c∉X,Q'.Adj a c→(p^2*βh/2)*Fintype.card (V⊕U)≤
      ((Z.filter (fun u=>H' a u∧H' c u)).card:ℝ)):=by
  intro A B φ ψ Q₀ H₀ D E Q' H'
  have hp:=ordinary_root_cover_cleanup_parent_counts P Q Q' F H π d X T Z W r η ell K.cover
    pR pH density tR tH L βe₀ βh₀ βe βh s j raw profile (show Q'≤Q₀ from sdiff_le) hmE hmH
  have hh:=ordinary_root_first_cleanup_counts_from_events Q F H X T Z W r η ell t K ht βe βh p σ
    hreserve hevent hhevent (by
      intro a ha c hc hac
      convert hp.2 a ha c hc hac using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
  constructor
  · intro u a c
    convert hh.1 u a c using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  · intro a ha c hc hac
    convert hh.2 a ha c hc hac using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
end Oberwolfach

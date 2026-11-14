module

public import Oberwolfach.OrdinaryRootCoverCleanupParentCounts

@[expose] public section
/-! Reserve extension candidates outside the deeper set before sampling;
    their deterministic count loses only the size of that set. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]

theorem ordinary_root_cover_subset_extension_counts
    (P Q F:SimpleGraph V) (H:V→U→Prop) (π:Equiv.Perm V) (d:ℕ)
    (X T:Finset V) (Z W:Finset U) (r:ℕ) (η ell:ℝ)
    (D:OrdinaryRootCoverData Q F H X T Z W r η ell)
    (pR pH density tR tH L βe₀ βh₀ βe βh:ℝ) (s:U→Color→ℝ) (j:Color)
    (raw:RawWheelOutcome V U Γ Color)
    (profile:OrdinaryCleanupParentProfiles P Q F H π d X Z pR pH density tR tH L βe₀ βh₀ s j raw)
    (hmE:βe*Fintype.card (V⊕U)+3*max η ell≤βe₀*Fintype.card (V⊕U))
    (hmH:βh*Fintype.card (V⊕U)+2*ell≤βh₀*Fintype.card (V⊕U))
    (hT:(T.card:ℝ)≤(βe/2)*Fintype.card (V⊕U)):
    ∀a c u,(βe/2)*Fintype.card (V⊕U)≤
      (((X\T).filter (fun v=>(Q\D.rim).Adj a v∧(Q\D.rim).Adj v c∧(H v u∧¬D.spokes v u))).card:ℝ) :=by
  have hparent:=ordinary_root_cover_cleanup_parent_counts P Q (Q\D.rim) F H π d X T Z W r η ell D
    pR pH density tR tH L βe₀ βh₀ βe βh s j raw profile le_rfl hmE hmH
  intro a c u
  let A:=X.filter (fun v=>(Q\D.rim).Adj a v∧(Q\D.rim).Adj v c∧(H v u∧¬D.spokes v u))
  have hcard:=Finset.card_sdiff_add_card_inter A T
  have hinter:(A∩T).card≤T.card:=Finset.card_le_card Finset.inter_subset_right
  have hreal:(A.card:ℝ)≤(A\T).card+T.card:=by exact_mod_cast (show A.card≤(A\T).card+T.card by omega)
  have heq:(A\T)=(X\T).filter (fun v=>(Q\D.rim).Adj a v∧(Q\D.rim).Adj v c∧(H v u∧¬D.spokes v u)):=by
    ext v
    simp [A, and_left_comm, and_comm, and_assoc]
  rw [heq] at hreal
  have hp:=hparent.1 a c u
  change βe*Fintype.card (V⊕U)≤(A.card:ℝ) at hp
  linarith
end Oberwolfach

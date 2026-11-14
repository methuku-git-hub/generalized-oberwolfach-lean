module

public import Oberwolfach.OrdinaryRootCoverAllExtensions
public import Oberwolfach.OrdinaryRootCoverOutsideHubPairs
public import Oberwolfach.OrdinaryCleanupParentProfiles

@[expose] public section
/-! The pre-cover common sample gives post-cover cleanup parent counts;
the two margins pay for the actual root-cover deletions. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]

theorem ordinary_root_cover_cleanup_parent_counts
    (P Q Qpost F:SimpleGraph V) (H:V→U→Prop) (π:Equiv.Perm V) (d:ℕ)
    (X T:Finset V) (Z W:Finset U) (r:ℕ) (η ell:ℝ)
    (D:OrdinaryRootCoverData Q F H X T Z W r η ell)
    (pR pH density tR tH L βe₀ βh₀ βe βh:ℝ) (s:U→Color→ℝ) (j:Color)
    (raw:RawWheelOutcome V U Γ Color)
    (profile:OrdinaryCleanupParentProfiles P Q F H π d X Z pR pH density tR tH L βe₀ βh₀ s j raw)
    (hpost:Qpost≤Q\D.rim)
    (hmE:βe*Fintype.card (V⊕U)+3*max η ell≤βe₀*Fintype.card (V⊕U))
    (hmH:βh*Fintype.card (V⊕U)+2*ell≤βh₀*Fintype.card (V⊕U)):
    (∀a c u,βe*Fintype.card (V⊕U)≤
      ((X.filter (fun v=>(Q\D.rim).Adj a v∧(Q\D.rim).Adj v c∧(H v u∧¬D.spokes v u))).card:ℝ)) ∧
    (∀a∉X,∀c∉X,Qpost.Adj a c→βh*Fintype.card (V⊕U)≤
      ((Z.filter (fun u=>(H a u∧¬D.spokes a u)∧(H c u∧¬D.spokes c u))).card:ℝ)):=by
  have hc:=ordinary_boundary_parent_common_of_min_degree P X density profile.parent_min_degree
  have he:=ordinary_boundary_parent_extensions_from_common_sample P Q H π d X pR pH (2*density-1)
    tR L βe₀ profile.rim_nonneg profile.rim_le_one profile.spoke_nonneg (by linarith [profile.density_large])
    s j raw profile.spoke_probability profile.rows hc profile.rim_edit profile.spoke_column_edit profile.extension_margin
  have hh:=ordinary_boundary_parent_hub_pairs_from_common_sample Q Qpost F H π d Z pH tH L βh₀ j raw
    (hpost.trans sdiff_le) profile.forbidden_disjoint profile.columns profile.spoke_row_edit profile.hub_margin
  constructor
  · intro a c u
    have hsurvive:=ordinary_root_cover_all_extensions Q F H X T Z W r η ell D u a c
    have heq₀:(X.filter (fun v=>Q.Adj a v∧Q.Adj v c∧H v u))=
        (X.filter (fun v=>H v u))∩Q.neighborFinset a∩Q.neighborFinset c:=by
      ext v
      simp only [Finset.mem_filter,Finset.mem_inter,SimpleGraph.mem_neighborFinset]
      have hs:Q.Adj v c↔Q.Adj c v:=Q.adj_comm _ _
      tauto
    have heq₁:(X.filter (fun v=>(Q\D.rim).Adj a v∧(Q\D.rim).Adj v c∧(H v u∧¬D.spokes v u)))=
        (X.filter (fun v=>H v u∧¬D.spokes v u))∩(Q\D.rim).neighborFinset a∩(Q\D.rim).neighborFinset c:=by
      ext v
      simp only [Finset.mem_filter,Finset.mem_inter,SimpleGraph.mem_neighborFinset]
      have hs:(Q\D.rim).Adj v c↔(Q\D.rim).Adj c v:=(Q\D.rim).adj_comm _ _
      tauto
    have he' := he a c u
    rw [heq₀] at he'
    rw [heq₁]
    linarith only [he',hsurvive,hmE]
  · intro a ha c hc' hac
    have hsurvive:=ordinary_root_cover_outside_hub_pairs Q F H X T Z W r η ell D a c ha hc'
    have hh' := hh a c hac
    linarith only [hh',hsurvive,hmH]
end Oberwolfach

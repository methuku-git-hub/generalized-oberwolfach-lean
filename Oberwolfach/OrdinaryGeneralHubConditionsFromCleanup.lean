module

public import Oberwolfach.OrdinaryCleanupParentProfiles
public import Oberwolfach.OrdinaryBoundaryParentCommon
public import Oberwolfach.OrdinaryBoundaryExtensionFromCommonSample
public import Oberwolfach.OrdinaryBoundaryRootSets

@[expose] public section
/-! For wheel lengths at least four, two-root common neighborhoods of every
    hub class follow from the same sampled cleanup profile and density above
    one half; no triangle-density threshold is used. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 8000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]

theorem ordinary_general_hub_conditions_from_cleanup
    (P Q F:SimpleGraph V) (H:V→U→Prop) (A:Finset V) (B:Finset U)
    (π:Equiv.Perm V) (d:ℕ) (j:Color) (s:U→Color→ℝ)
    (γ κ pR pH density tR tH Ledit βe βh:ℝ) (σ:RawWheelOutcome V U Γ Color)
    (profile:OrdinaryCleanupParentProfiles P Q F H π d A B pR pH density tR tH Ledit βe βh s j σ)
    (hA:A.Nonempty)
    (hγscale:γ*Fintype.card V≤βe*Fintype.card (V⊕U))
    (hκscale:κ*Fintype.card V≤βe*Fintype.card (V⊕U)):
    (∀j:{u:U // u∉B},κ*Fintype.card V≤((ordinaryBoundaryHubSet H B A j).card:ℝ)) ∧
    (∀j:{u:U // u∉B},∀S:Finset V,S⊆ordinaryBoundaryHubSet H B A j→S.card≤2→
      γ*Fintype.card V≤((common (ordinaryBoundaryHubSet H B A j) S
        (fun x=>(spanningRestriction Q A).neighborFinset x)).card:ℝ)):=by
  have hparent:=ordinary_boundary_parent_common_of_min_degree P A density profile.parent_min_degree
  have hpair:=ordinary_boundary_parent_extensions_from_common_sample P Q H π d A pR pH (2*density-1)
    tR Ledit βe profile.rim_nonneg profile.rim_le_one profile.spoke_nonneg (by linarith [profile.density_large])
    s j σ profile.spoke_probability profile.rows hparent profile.rim_edit profile.spoke_column_edit profile.extension_margin
  obtain ⟨v₀,hv₀⟩:=hA
  have hrepr (S:Finset V) (hS:S.card≤2):∃a c:V,S⊆{a,c}:=by
    by_cases h0:S=∅
    · exact ⟨v₀,v₀,by simp [h0]⟩
    by_cases h1:∃a:V,S={a}
    · obtain ⟨a,ha⟩:=h1
      exact ⟨a,a,by simp [ha]⟩
    have hc0:S.card≠0:=by intro hh;exact h0 (Finset.card_eq_zero.mp hh)
    have hc1:S.card≠1:=by intro hh;exact h1 (Finset.card_eq_one.mp hh)
    have hc:S.card=2:=by omega
    obtain ⟨a,c,_,hh⟩:=Finset.card_eq_two.mp hc
    exact ⟨a,c,by rw [hh]⟩
  have hbound (u:U) (S:Finset V) (hS:S.card≤2):
      βe*Fintype.card (V⊕U)≤((common (A.filter (fun v=>H v u)) S (fun v=>Q.neighborFinset v)).card:ℝ):=by
    obtain ⟨a,c,hsub⟩:=hrepr S hS
    have hinc:A.filter (fun v=>Q.Adj a v∧Q.Adj v c∧H v u) ⊆
        common (A.filter (fun v=>H v u)) S (fun v=>Q.neighborFinset v):=by
      intro v hv
      obtain ⟨hvA,hav,hvc,hvu⟩:=Finset.mem_filter.mp hv
      rw [mem_common_iff]
      refine ⟨Finset.mem_filter.mpr ⟨hvA,hvu⟩,?_⟩
      intro x hx
      have hx':x=a∨x=c:=by simpa using hsub hx
      simp only [SimpleGraph.mem_neighborFinset]
      rcases hx' with rfl|rfl
      · exact hav
      · exact (Q.adj_comm _ _).mpr hvc
    have hc:((A.filter (fun v=>Q.Adj a v∧Q.Adj v c∧H v u)).card:ℝ)≤
      ((common (A.filter (fun v=>H v u)) S (fun v=>Q.neighborFinset v)).card:ℝ):=by
      exact_mod_cast Finset.card_le_card hinc
    exact (hpair a c u).trans hc
  constructor
  · intro j₀
    have hh:=hbound j₀.val ∅ (by simp)
    simpa [ordinaryBoundaryHubSet,common] using hκscale.trans hh
  · intro j₀ S hST hS
    have hSA:S⊆A:=by
      intro v hv
      exact (Finset.mem_filter.mp (hST hv)).1
    have he:common (ordinaryBoundaryHubSet H B A j₀) S
        (fun v=>(spanningRestriction Q A).neighborFinset v)=
        common (A.filter (fun v=>H v j₀.val)) S (fun v=>Q.neighborFinset v):=by
      ext v
      simp only [ordinaryBoundaryHubSet,mem_common_iff,Finset.mem_filter,SimpleGraph.mem_neighborFinset,
        spanningRestriction_adj]
      constructor
      · rintro ⟨⟨hv,hHv⟩,hs⟩
        exact ⟨⟨hv,hHv⟩,fun x hx=>(hs x hx).1⟩
      · rintro ⟨⟨hv,hHv⟩,hs⟩
        exact ⟨⟨hv,hHv⟩,fun x hx=>⟨hs x hx,hSA hx,hv⟩⟩
    rw [he]
    exact hγscale.trans (hbound j₀.val S hS)
end Oberwolfach

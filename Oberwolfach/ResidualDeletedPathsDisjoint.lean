module

public import Oberwolfach.ResidualDeletedPathParent

@[expose] public section
/-! The final paths and all maximal selected-run subpaths are vertex-disjoint. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V I:Type} [Fintype V] [DecidableEq V] [DecidableEq I]

theorem deleted_path_family_vertex_disjoint (F:SimpleGraph V)
    (s₁ s₂:Finset I) (hs:Disjoint s₁ s₂) (u v:I→V) (P:∀i,F.Walk (u i) (v i))
    (hp:∀i∈s₁∪s₂,(P i).IsPath)
    (hP:(↑(s₁∪s₂):Set I).PairwiseDisjoint (fun i=>(P i).support.toFinset))
    (c d:ℕ) (hc:0<c) (hlen:∀i∈s₁∪s₂,(P i).length=c*d+4)
    (T:I→Finset ℕ) (hT:∀i∈s₂,T i⊆Finset.range d)
    (z w:DeletedPathIndex s₁ s₂ d T) (hne:z≠w):
    Disjoint (deletedPathWalk F s₁ s₂ u v P c d T hT z).support.toFinset
      (deletedPathWalk F s₁ s₂ u v P c d T hT w).support.toFinset := by
  by_cases hparent:deletedPathParent z=deletedPathParent w
  · cases z with
    | inl i =>
      cases w with
      | inl j =>
        have hij:i=j := Subtype.ext hparent
        subst j
        exact (hne rfl).elim
      | inr w =>
        rcases w with ⟨j,r⟩
        have hv:i.1=j.1 := hparent
        exact (Finset.disjoint_left.mp hs i.2 (hv ▸ j.2)).elim
    | inr z =>
      rcases z with ⟨i,r⟩
      cases w with
      | inl j =>
        have hv:i.1=j.1 := hparent
        exact (Finset.disjoint_left.mp hs j.2 (hv.symm ▸ i.2)).elim
      | inr w =>
        rcases w with ⟨j,r'⟩
        have hij:i=j := Subtype.ext hparent
        subst j
        have hrr:r.1≠r'.1 := by
          intro h
          have :r=r' := Subtype.ext h
          subst r'
          exact hne rfl
        rcases r with ⟨⟨a,b⟩,hr⟩
        rcases r' with ⟨⟨a',b'⟩,hr'⟩
        exact selected_run_walks_disjoint (P i.1) (hp i.1 (Finset.mem_union_right _ i.2)) c d hc
          (hlen i.1 (Finset.mem_union_right _ i.2)) (T i.1) (hT i.1 i.2) a b a' b' hr hr' hrr
  · exact (hP (deleted_path_parent_mem z) (deleted_path_parent_mem w) hparent).mono
      (deleted_path_support_subset_parent F s₁ s₂ u v P c d hlen T hT z)
      (deleted_path_support_subset_parent F s₁ s₂ u v P c d hlen T hT w)
end Oberwolfach

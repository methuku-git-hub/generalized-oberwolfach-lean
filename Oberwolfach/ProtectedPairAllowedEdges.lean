module

public import Oberwolfach.RawProtectedPairHubLoss

@[expose] public section
/-! An edge may be assigned only to outer hubs whose protected list contains
both endpoints. Such a label automatically avoids the old image. -/
set_option autoImplicit false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def protectedPairEdgeHubs {V U:Type} [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U]
    (Lists:U→Finset V) (inner:Finset U) (e:Sym2 V):Finset U:=
  Finset.univ.filter (fun u=>u∉inner ∧ ∀v∈e.toFinset,v∈Lists u)

theorem protected_pair_edge_hubs_avoid_old_images
    {V U:Type} [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U]
    (Lists Old:U→Finset V) (inner:Finset U) (hOld:∀u,Disjoint (Lists u) (Old u)):
    (∀e,Disjoint (protectedPairEdgeHubs Lists inner e) inner) ∧
    (∀u e v,v∈e.toFinset→v∈Old u→u∈protectedPairEdgeHubs Lists inner e→False):=by
  constructor
  · intro e
    apply Finset.disjoint_left.mpr
    intro u hu hi
    exact (Finset.mem_filter.mp hu).2.1 hi
  · intro u e v hv ho hu
    have hl: v∈Lists u:=(Finset.mem_filter.mp hu).2.2 v hv
    exact Finset.disjoint_left.mp (hOld u) hl ho

theorem protected_pair_edge_hubs_card_lower
    {V U:Type} [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U]
    (Lists:U→Finset V) (inner:Finset U) (x y:V):
    (Finset.univ.filter (fun u=>x∈Lists u ∧ y∈Lists u)).card≤
      (protectedPairEdgeHubs Lists inner s(x,y)).card+inner.card:=by
  let A:=Finset.univ.filter (fun u=>x∈Lists u ∧ y∈Lists u)
  let B:=protectedPairEdgeHubs Lists inner s(x,y)
  have hsub:A⊆B∪inner:=by
    intro u hu
    have hu':=(Finset.mem_filter.mp hu).2
    by_cases hi:u∈inner
    · exact Finset.mem_union_right _ hi
    · apply Finset.mem_union_left
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,hi,?_⟩
      intro v hv
      simp only [Sym2.toFinset_mk_eq,Finset.mem_insert,Finset.mem_singleton] at hv
      rcases hv with rfl|rfl
      · exact hu'.1
      · exact hu'.2
  have hc:=Finset.card_le_card hsub
  have hu:=Finset.card_union_le B inner
  change A.card≤B.card+inner.card
  omega
end Oberwolfach

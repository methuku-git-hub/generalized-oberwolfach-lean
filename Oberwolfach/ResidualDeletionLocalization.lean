module

public import Mathlib.Data.Finset.Union

@[expose] public section
/-! A deletion supported on one member of a disjoint family cannot remove
a vertex from another member. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V I:Type} [DecidableEq V] [DecidableEq I]

theorem disjoint_family_deletion_localization
    (s:Finset I) (S D:I→Finset V) (C:Finset V)
    (hS:(↑s:Set I).PairwiseDisjoint S) (hD:∀i∈s,D i⊆S i)
    (hC:∀i∈s,Disjoint (S i) C) (i:I) (hi:i∈s) (x:V) (hx:x∈S i):
    x∉C ∪ s.biUnion D ↔ x∉D i := by
  constructor
  · intro h hxi
    exact h (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i,hi,hxi⟩))
  · intro h hbad
    rcases Finset.mem_union.mp hbad with hc|hd
    · exact Finset.disjoint_left.mp (hC i hi) hx hc
    · obtain ⟨j,hj,hxj⟩:=Finset.mem_biUnion.mp hd
      by_cases hij:i=j
      · subst j;exact h hxj
      · exact Finset.disjoint_left.mp (hS hi hj hij) hx (hD j hj hxj)
end Oberwolfach

module

public import Oberwolfach.OrdinaryUnreservedWalkFamilies

@[expose] public section
/-! Lifting walks to an induced unreserved factor preserves all pairwise
source-support disjointness needed by the buffered embedding. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_unreserved_support_disjoint
    {V:Type} [DecidableEq V] (S:Set V) (a b:List S) (x y:List V)
    (ha:a.map Subtype.val=x) (hb:b.map Subtype.val=y)
    (h:Disjoint x.toFinset y.toFinset):Disjoint a.toFinset b.toFinset:=by
  classical
  apply Finset.disjoint_left.mpr
  intro z hza hzb
  have hax:(z:V)∈x:=by
    rw [←ha]
    exact List.mem_map.mpr ⟨z,List.mem_toFinset.mp hza,rfl⟩
  have hby:(z:V)∈y:=by
    rw [←hb]
    exact List.mem_map.mpr ⟨z,List.mem_toFinset.mp hzb,rfl⟩
  exact Finset.disjoint_left.mp h (List.mem_toFinset.mpr hax) (List.mem_toFinset.mpr hby)

theorem ordinary_unreserved_walk_disjointness
    {V T J:Type} [DecidableEq V] (F:SimpleGraph V) (S:Set V)
    (u v:T→V) (P:∀i,F.Walk (u i) (v i)) (root:J→V) (C:∀j,F.Walk (root j) (root j))
    (u' v':T→S) (P':∀i,(F.induce S).Walk (u' i) (v' i))
    (root':J→S) (C':∀j,(F.induce S).Walk (root' j) (root' j))
    (hPsupp:∀i,(P' i).support.map Subtype.val=(P i).support)
    (hCsupp:∀j,(C' j).support.map Subtype.val=(C j).support)
    (hP:∀i j,i≠j→Disjoint (P i).support.toFinset (P j).support.toFinset)
    (hC:∀i j,i≠j→Disjoint (C i).support.toFinset (C j).support.toFinset)
    (hcross:∀i j,Disjoint (P i).support.toFinset (C j).support.toFinset):
    (∀i j,i≠j→Disjoint (P' i).support.toFinset (P' j).support.toFinset) ∧
    (∀i j,i≠j→Disjoint (C' i).support.toFinset (C' j).support.toFinset) ∧
    (∀i j,Disjoint (P' i).support.toFinset (C' j).support.toFinset):=by
  exact ⟨fun i j hij=>ordinary_unreserved_support_disjoint S _ _ _ _ (hPsupp i) (hPsupp j) (hP i j hij),
    fun i j hij=>ordinary_unreserved_support_disjoint S _ _ _ _ (hCsupp i) (hCsupp j) (hC i j hij),
    fun i j=>ordinary_unreserved_support_disjoint S _ _ _ _ (hPsupp i) (hCsupp j) (hcross i j)⟩
end Oberwolfach

module

public import Oberwolfach.MarkedRowCoverUnionBounds
public import Oberwolfach.MarkedPackingUnions
public import Oberwolfach.MarkedInnerResources

@[expose] public section

/-! Exact protected-inner-set avoidance and cumulative free-degree bounds
for the constructed hub and row stages. Hubs outside the selected hub set
receive only the explicit cumulative row-stage loss. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E T:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
  {tail head:E→V} {ktail khead:T→V} {m b n h K:ℕ} {π:Equiv.Perm V} {H₀ HK:V→U→Prop}

theorem marked_wheel_avoids_inner_of_rows
    (I:Finset V) (J:Finset U) (W:MarkedWheel tail head ktail khead m π b H₀ HK)
    (hrows:∀ x∈markedWheelRows W,x∉I):
    (markedWheelPhysicalResources W).filter (markedInnerResource I J)=∅:=by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro e he
  obtain ⟨he,hi⟩:=Finset.mem_filter.mp he
  cases e with
  | inl e=>
    obtain ⟨i,_,hi'⟩:=Finset.mem_image.mp ((markedWheelPhysicalResources_rim W e).mp he)
    simp only [Function.comp_apply] at hi'
    have hp:=markedCycle_physical_pair tail head ktail khead π b W.1 i
    have hsub:({W.1.val i,twistedTupleHead π W.1.val i}:Finset V)⊆I:=by
      rw [←hp,hi'];exact hi
    exact hrows _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩) (hsub (Finset.mem_insert_self _ _))
  | inr z=>
    exact hrows z.1 ((markedWheelPhysicalResources_spoke W _ _).mp he).2 hi.1

theorem marked_wheel_avoids_inner_of_single_root (hm:0<m)
    (I:Finset V) (J:Finset U) (hI:∀ v,π v∈I↔v∈I)
    (W:MarkedWheel tail head ktail khead m π b H₀ HK) (v:V)
    (hrows:∀ x∈markedWheelRows W,x∈I→x=v) (hhub:W.2.val∉J):
    (markedWheelPhysicalResources W).filter (markedInnerResource I J)=∅:=by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro e he
  obtain ⟨he,hi⟩:=Finset.mem_filter.mp he
  cases e with
  | inl e=>
    obtain ⟨i,_,hi'⟩:=Finset.mem_image.mp ((markedWheelPhysicalResources_rim W e).mp he)
    simp only [Function.comp_apply] at hi'
    have hinside:markedPhysicalEdge tail head ktail khead π
      (markedCycleTypedEdge tail head ktail khead m π b W.1 i)⊆I:=by rw [hi'];exact hi
    obtain ⟨hx,hy⟩:=(marked_cycle_edge_inside_iff I hI W.1 i).mp hinside
    have heq:W.1.val i=W.1.val (finRotate (m+1) i):=
      (hrows _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩) hx).trans
        (hrows _ (Finset.mem_image.mpr ⟨_,Finset.mem_univ _,rfl⟩) hy).symm
    exact finRotate_ne_self_of_pos hm i (permutationSeparated_injective π b W.1.val W.1.property.1 heq)
  | inr z=>exact hhub (((markedWheelPhysicalResources_spoke W _ _).mp he).1 ▸ hi.2)

theorem marked_hub_row_avoids_inner (hm:0<m)
    (M:Finset (MarkedWheel tail head ktail khead m π b H₀ HK))
    (C:Fin n→Finset (MarkedWheel tail head ktail khead m π b H₀ HK))
    (v:Fin n→V) (F I:Finset V) (J:Finset U)
    (required:Fin n→Finset (Finset V⊕(V×U))) (Y:Fin n→Finset U)
    (hC:∀ i,MarkedRowCover (C i) (v i) F (required i) (Y i) K)
    (hMrows:∀ W∈M,markedWheelRows W⊆F)
    (hFI:Disjoint F I) (hI:∀ x,π x∈I↔x∈I) (hYJ:∀ i,Disjoint (Y i) J):
    ((M∪Finset.univ.biUnion C).biUnion markedWheelPhysicalResources).filter (markedInnerResource I J)=∅:=by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro e he
  obtain ⟨he,hinner⟩:=Finset.mem_filter.mp he
  obtain ⟨W,hW,he⟩:=Finset.mem_biUnion.mp he
  have hnone:(markedWheelPhysicalResources W).filter (markedInnerResource I J)=∅:=by
    rcases Finset.mem_union.mp hW with hW|hW
    · exact marked_wheel_avoids_inner_of_rows I J W (fun x hx=>Finset.disjoint_left.mp hFI (hMrows W hW hx))
    · obtain ⟨i,_,hW⟩:=Finset.mem_biUnion.mp hW
      apply marked_wheel_avoids_inner_of_single_root hm I J hI W (v i)
      · intro x hx hxi
        rcases Finset.mem_insert.mp ((hC i).rows W hW hx) with hx|hx
        · exact hx
        · exact (Finset.disjoint_left.mp hFI hx hxi).elim
      · exact Finset.disjoint_left.mp (hYJ i) ((hC i).hubs W hW)
  have hh:=Finset.mem_filter.mpr ⟨he,hinner⟩
  rw [hnone] at hh
  exact Finset.notMem_empty e hh

theorem marked_hub_row_free_degree_bounds
    (M:Finset (MarkedWheel tail head ktail khead m π b H₀ HK)) (u:Fin h→U)
    (hMhubs:∀ W∈M,W.2.val∈Finset.univ.image u)
    (hMdeg:∀ x,(markedPackingRimGraph M).degree x≤2*h)
    (C:Fin n→Finset (MarkedWheel tail head ktail khead m π b H₀ HK))
    (v:Fin n→V) (F:Finset V) (required:Fin n→Finset (Finset V⊕(V×U))) (Y:Fin n→Finset U)
    (hC:∀ i,MarkedRowCover (C i) (v i) F (required i) (Y i) K):
    let N:=M∪Finset.univ.biUnion C
    (∀ x,(spanningRestriction (markedPackingRimGraph N) F).degree x≤2*h+n*(4*(K+4)))∧
    (∀ x∈F,(Finset.univ.filter (markedPackingSpokes N x)).card≤h+n*(K+4))∧
    (∀ z∉Finset.univ.image u,(Finset.univ.filter (fun x=>markedPackingSpokes N x z)).card≤n*(m+1)):=by
  let D:=Finset.univ.biUnion C
  obtain ⟨hDr,hDs,hDc⟩:=marked_row_cover_union_bounds C v F required Y hC
  have hrow (x:V):(Finset.univ.filter (markedPackingSpokes M x)).card≤h:=by
    apply le_trans (Finset.card_le_card (t:=Finset.univ.image u) ?_)
    · exact (Finset.card_image_le).trans_eq (by simp)
    · intro z hz
      obtain ⟨W,hW,hw,_⟩:=(Finset.mem_filter.mp hz).2
      exact hw ▸ hMhubs W hW
  refine ⟨?_,?_,?_⟩
  · intro x
    have hle:spanningRestriction (markedPackingRimGraph (M∪D)) F≤
        markedPackingRimGraph M⊔spanningRestriction (markedPackingRimGraph D) F:=by
      rw [markedPackingRimGraph_union]
      intro a z haz
      obtain ⟨hg,ha,hz⟩:=(spanningRestriction_adj _ _ _ _).mp haz
      exact hg.elim Or.inl (fun h=>Or.inr ((spanningRestriction_adj _ _ _ _).mpr ⟨h,ha,hz⟩))
    exact ((SimpleGraph.degree_le_of_le hle).trans
      (graph_degree_sup_le (markedPackingRimGraph M) (spanningRestriction (markedPackingRimGraph D) F) x)).trans
      (Nat.add_le_add (hMdeg x) (hDr x))
  · intro x hx
    have he:Finset.univ.filter (markedPackingSpokes (M∪D) x)=
        Finset.univ.filter (markedPackingSpokes M x)∪Finset.univ.filter (markedPackingSpokes D x):=by
      ext z
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_union,markedPackingSpokes_union]
    rw [he]
    exact (Finset.card_union_le _ _).trans (Nat.add_le_add (hrow x) (hDs x hx))
  · intro z hz
    apply le_trans (Finset.card_le_card ?_) (hDc z)
    intro x hx
    obtain ⟨_,h⟩:=Finset.mem_filter.mp hx
    rcases (markedPackingSpokes_union M D x z).mp h with h|h
    · obtain ⟨W,hW,hw,_⟩:=h
      exact (hz (hw ▸ hMhubs W hW)).elim
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩

end Oberwolfach

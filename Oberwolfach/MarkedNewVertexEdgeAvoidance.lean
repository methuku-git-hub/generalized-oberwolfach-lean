module

public import Oberwolfach.MarkedResourceSupport
public import Oberwolfach.MarkedArcPairs

@[expose] public section

/-! Physical forbidden-edge avoidance in the hub-switch factors. New
auxiliary heads must avoid inverse images of forbidden physical vertices,
not only the forbidden physical vertices themselves. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V E K:Type} [DecidableEq V]
    {tail head:E→V} {ktail khead:K→V} {π:Equiv.Perm V}

 theorem marked_rim_edge_avoids_forbidden (F:Finset (Finset V)) (Y:Finset V)
    (hY:Disjoint Y ((F.biUnion id)∪(F.biUnion id).image π.symm))
    (a:E⊕K) (hnew:Sum.elim tail ktail a∈Y∨Sum.elim head khead a∈Y):
    markedPhysicalEdge tail head ktail khead π a∉F:=by
  intro ha
  have hmem:∀ v∈markedPhysicalEdge tail head ktail khead π a,v∈F.biUnion id:=
    fun v hv=>Finset.mem_biUnion.mpr ⟨_,ha,hv⟩
  have htail:Sum.elim tail ktail a∈F.biUnion id:=by
    apply hmem
    cases a <;> simp [markedPhysicalEdge]
  rcases hnew with hnew|hnew
  · exact Finset.disjoint_left.mp hY hnew (Finset.mem_union_left _ htail)
  · cases a with
    | inl a=>
      have hh:head a∈F.biUnion id:=hmem _ (by simp [markedPhysicalEdge])
      exact Finset.disjoint_left.mp hY hnew (Finset.mem_union_left _ hh)
    | inr a=>
      have hh:π (khead a)∈F.biUnion id:=hmem _ (by simp [markedPhysicalEdge])
      have hi:khead a∈(F.biUnion id).image π.symm:=Finset.mem_image.mpr ⟨π (khead a),hh,π.symm_apply_apply _⟩
      exact Finset.disjoint_left.mp hY hnew (Finset.mem_union_right _ hi)

 theorem marked_cycle_arc_has_new_endpoint {m b:ℕ} (hm:1≤m)
    (C:MarkedCycleTuple tail head ktail khead m π b) (Y Z:Finset V)
    (hs:Finset.univ.image C.val⊆Y∪Z)
    (hz:((Finset.univ.image C.val)∩Z).card≤1):
    ∀ i,C.val i∈Y∨C.val (finRotate (m+1) i)∈Y:=by
  intro i
  by_contra hn
  have hi:C.val i∈Z:=(Finset.mem_union.mp (hs (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩))).resolve_left
    (fun h=>hn (Or.inl h))
  have hj:C.val (finRotate (m+1) i)∈Z:=
    (Finset.mem_union.mp (hs (Finset.mem_image.mpr ⟨finRotate (m+1) i,Finset.mem_univ _,rfl⟩))).resolve_left
      (fun h=>hn (Or.inr h))
  have he:C.val i=C.val (finRotate (m+1) i):=Finset.card_le_one.mp hz _
    (Finset.mem_inter.mpr ⟨Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩,hi⟩) _
    (Finset.mem_inter.mpr ⟨Finset.mem_image.mpr ⟨finRotate (m+1) i,Finset.mem_univ _,rfl⟩,hj⟩)
  exact marked_cycle_auxiliary_arc_nonloop hm C i he

 theorem marked_cycle_avoids_forbidden_rims {m b:ℕ} (hm:1≤m)
    (C:MarkedCycleTuple tail head ktail khead m π b) (Y Z:Finset V) (F:Finset (Finset V))
    (hs:Finset.univ.image C.val⊆Y∪Z)
    (hz:((Finset.univ.image C.val)∩Z).card≤1)
    (hY:Disjoint Y ((F.biUnion id)∪(F.biUnion id).image π.symm)):
    Disjoint (markedCyclePhysicalEdges tail head ktail khead m π b C) F:=by
  apply Finset.disjoint_left.mpr
  intro e he
  obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp he
  apply marked_rim_edge_avoids_forbidden F Y hY
  have hh:=markedCycleTypedEdge_endpoints tail head ktail khead m π b C i
  rw [hh.1,hh.2]
  exact marked_cycle_arc_has_new_endpoint hm C Y Z hs hz i

end Oberwolfach

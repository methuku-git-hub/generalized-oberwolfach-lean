module

public import Oberwolfach.MarkedHubSwitchResources

@[expose] public section

/-! Exact row exclusions sufficient for avoiding a finite set of physical
resources. The inverse permutation is applied only to physical rim vertices;
spoke exclusions retain their actual row coordinate. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [DecidableEq V] [DecidableEq U]
    {tail head:E→V} {ktail khead:K→V} {π:Equiv.Perm V}

 def physicalResourceForbiddenRows (π:Equiv.Perm V):Finset V⊕(V×U)→Finset V
  | .inl e=>e∪e.image π.symm
  | .inr vu=>{vu.1}

 def markedForbiddenResourceRows (π:Equiv.Perm V) (F:Finset (Finset V⊕(V×U))):Finset V:=
    F.biUnion (physicalResourceForbiddenRows π)

 theorem marked_forbidden_rim_endpoints (F:Finset (Finset V⊕(V×U))) (a:E⊕K)
    (ha:(Sum.inl (markedPhysicalEdge tail head ktail khead π a):Finset V⊕(V×U))∈F):
    Sum.elim tail ktail a∈markedForbiddenResourceRows π F∧
      Sum.elim head khead a∈markedForbiddenResourceRows π F:=by
  have hin:physicalResourceForbiddenRows (U:=U) π (Sum.inl (markedPhysicalEdge tail head ktail khead π a))⊆
      markedForbiddenResourceRows π F:=by
    intro v hv
    exact Finset.mem_biUnion.mpr ⟨_,ha,hv⟩
  cases a with
  | inl a=>
    constructor <;> apply hin <;> simp [physicalResourceForbiddenRows,markedPhysicalEdge]
  | inr a=>
    constructor
    · apply hin;simp [physicalResourceForbiddenRows,markedPhysicalEdge]
    · apply hin
      apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨π (khead a),by simp [markedPhysicalEdge],π.symm_apply_apply _⟩

 theorem marked_switch_avoids_forbidden_resources (Y Z:Finset V) (u u':U)
    (F P:Finset (Finset V⊕(V×U)))
    (hY:Disjoint Y (markedForbiddenResourceRows π F))
    (hZ:∀ v∈Z,(Sum.inr (v,u):Finset V⊕(V×U))∉F∧(Sum.inr (v,u'):Finset V⊕(V×U))∉F)
    (hP:∀ e∈P,MarkedSwitchResource tail head ktail khead π Y Z u u' e):Disjoint P F:=by
  apply Finset.disjoint_left.mpr
  intro e he hf
  cases e with
  | inl e=>
    obtain ⟨a,ha,_,_,hnew⟩:=hP _ he
    have he':(Sum.inl (markedPhysicalEdge tail head ktail khead π a):Finset V⊕(V×U))∈F:=ha.symm ▸ hf
    have hh:=marked_forbidden_rim_endpoints F a he'
    rcases hnew with hv|hv
    · exact Finset.disjoint_left.mp hY hv hh.1
    · exact Finset.disjoint_left.mp hY hv hh.2
  | inr vu=>
    obtain ⟨hv,hu⟩:=hP _ he
    rcases Finset.mem_union.mp hv with hv|hv
    · exact Finset.disjoint_left.mp hY hv (Finset.mem_biUnion.mpr ⟨Sum.inr vu,hf,by simp [physicalResourceForbiddenRows]⟩)
    · rcases hu with hu|hu
      · exact (hZ vu.1 hv).1 (hu ▸ hf)
      · exact (hZ vu.1 hv).2 (hu ▸ hf)

 theorem marked_forbidden_resource_rows_card (F:Finset (Finset V⊕(V×U)))
    (hF:∀ e:Finset V,Sum.inl e∈F→e.card≤2):
    (markedForbiddenResourceRows π F).card≤4*F.card:=by
  have hlocal:∀ e∈F,(physicalResourceForbiddenRows π e).card≤4:=by
    intro e he
    cases e with
    | inl e=>
      have hc:=hF e he
      have hh:=(Finset.card_union_le e (e.image π.symm)).trans
        (Nat.add_le_add_left (Finset.card_image_le) e.card)
      dsimp only [physicalResourceForbiddenRows]
      omega
    | inr vu=>simp [physicalResourceForbiddenRows]
  calc
    _ ≤ ∑ e∈F,(physicalResourceForbiddenRows π e).card:=Finset.card_biUnion_le
    _ ≤ ∑ _e∈F,4:=Finset.sum_le_sum (fun e he=>hlocal e he)
    _ = 4*F.card:=by simp [Nat.mul_comm]

end Oberwolfach

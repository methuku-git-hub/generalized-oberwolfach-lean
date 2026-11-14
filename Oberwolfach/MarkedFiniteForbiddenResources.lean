module

public import Oberwolfach.MarkedForbiddenResourceRows
public import Oberwolfach.MarkedResourceExclusions

@[expose] public section

/-! Finite physical edge exclusions are converted into bounded auxiliary
row and hub exclusions. A marked physical head is pulled back by the
permutation; no physical and auxiliary vertex domains are identified. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [DecidableEq V] [DecidableEq U]
    {tail head:E→V} {ktail khead:K→V} {π:Equiv.Perm V}

def physicalResourceForbiddenHubs : Finset V⊕(V×U)→Finset U
  | .inl _=>∅
  | .inr vu=>{vu.2}

def markedForbiddenResourceHubs (F:Finset (Finset V⊕(V×U))):Finset U:=
  F.biUnion physicalResourceForbiddenHubs

theorem marked_forbidden_resource_hubs_card (F:Finset (Finset V⊕(V×U))):
    (markedForbiddenResourceHubs F).card≤F.card:=by
  have hh:∀ e∈F,(physicalResourceForbiddenHubs e).card≤1:=by
    intro e he
    cases e <;> simp [physicalResourceForbiddenHubs]
  calc
    _ ≤ ∑ e∈F,(physicalResourceForbiddenHubs e).card:=Finset.card_biUnion_le
    _ ≤ ∑ _e∈F,1:=Finset.sum_le_sum hh
    _ = F.card:=by simp

theorem marked_forbidden_resource_old (F:Finset (Finset V⊕(V×U)))
    (e:Finset V⊕(V×U)) (he:e∈F)
    (hs:match e with | .inl v=>∃ a:E⊕K,markedPhysicalEdge tail head ktail khead π a=v | .inr _=>True):
    MarkedOldResource tail head ktail khead π (markedForbiddenResourceRows π F) (markedForbiddenResourceHubs F) e:=by
  cases e with
  | inl e=>
    obtain ⟨a,rfl⟩:=hs
    have hh:=marked_forbidden_rim_endpoints F a he
    exact ⟨a,rfl,hh.1,hh.2⟩
  | inr vu=>
    constructor
    · exact Finset.mem_biUnion.mpr ⟨Sum.inr vu,he,by simp [physicalResourceForbiddenRows]⟩
    · exact Finset.mem_biUnion.mpr ⟨Sum.inr vu,he,by simp [physicalResourceForbiddenHubs]⟩

theorem marked_no_old_resources_disjoint_finite
    (F C:Finset (Finset V⊕(V×U))) (Z:Finset V) (B:Finset U)
    (hZ:markedForbiddenResourceRows π F⊆Z) (hB:markedForbiddenResourceHubs F⊆B)
    (hC:∀ e∈C,¬MarkedOldResource tail head ktail khead π Z B e)
    (hs:∀ e∈C,match e with | .inl v=>∃ a:E⊕K,markedPhysicalEdge tail head ktail khead π a=v | .inr _=>True):
    Disjoint C F:=by
  apply Finset.disjoint_left.mpr
  intro e he hf
  exact hC e he (marked_old_resource_mono hZ hB e (marked_forbidden_resource_old F e hf (by cases e <;> exact hs _ he)))

end Oberwolfach

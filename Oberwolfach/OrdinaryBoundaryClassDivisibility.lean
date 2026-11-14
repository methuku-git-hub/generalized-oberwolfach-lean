module

public import Oberwolfach.OrdinaryBoundarySupportGeometry

@[expose] public section
/-! Exact balance and divisibility on the host give the local factor
class sizes once outside-outside edges have been covered. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U]

theorem ordinary_boundary_local_class_divisibility
    (Q:SimpleGraph V) (H:V→U→Prop) (X:Finset V) (Z:Finset U)
    (hNoR:∀v∉X,∀w∉X,¬Q.Adj v w)
    (hNoS:∀v∉X,∀u∉Z,¬H v u)
    (hbal:∀v,Q.degree v=2*(Finset.univ.filter (H v)).card)
    (hdiv:∀u,3∣(Finset.univ.filter (fun v=>H v u)).card):
    (∀i,(ordinaryBoundaryRimSet Q X i).card=2*(ordinaryBoundaryRowSet H X Z i).card) ∧
    (∀j,3∣(ordinaryBoundaryHubSet H Z X j).card):=by
  have hR (i:{v:V // v∉X}):ordinaryBoundaryRimSet Q X i=Q.neighborFinset i.val:=by
    ext v
    simp only [ordinaryBoundaryRimSet,Finset.mem_inter,SimpleGraph.mem_neighborFinset]
    constructor
    · exact And.left
    · intro hv
      exact ⟨hv,by by_contra hx;exact hNoR i.val i.property v hx hv⟩
  have hB (i:{v:V // v∉X}):ordinaryBoundaryRowSet H X Z i=Finset.univ.filter (H i.val):=by
    ext u
    simp only [ordinaryBoundaryRowSet,Finset.mem_filter,Finset.mem_univ,true_and]
    constructor
    · exact And.right
    · intro hu
      exact ⟨by by_contra hz;exact hNoS i.val i.property u hz hu,hu⟩
  have hY (j:{u:U // u∉Z}):ordinaryBoundaryHubSet H Z X j=Finset.univ.filter (fun v=>H v j.val):=by
    ext v
    simp only [ordinaryBoundaryHubSet,Finset.mem_filter,Finset.mem_univ,true_and]
    constructor
    · exact And.right
    · intro hv
      exact ⟨by by_contra hx;exact hNoS v hx j.val j.property hv,hv⟩
  refine ⟨?_,?_⟩
  · intro i;rw [hR,hB,SimpleGraph.card_neighborFinset_eq_degree];exact hbal i.val
  · intro j;rw [hY];exact hdiv j.val

theorem endpoint_image_union_ratio_of_classes (A:Finset V) (B:Finset U) (S T:Finset (V⊕U))
    (hST:Disjoint S T) (hA:A.image Sum.inl⊆S) (hB:B.image Sum.inr⊆T)
    (hcard:A.card=2*B.card):
    ((A.image Sum.inl∪B.image Sum.inr)∩S).card=
      2*((A.image Sum.inl∪B.image Sum.inr)∩T).card:=by
  have hs:(A.image Sum.inl∪B.image Sum.inr)∩S=A.image Sum.inl:=by
    ext w
    simp only [Finset.mem_inter,Finset.mem_union]
    have hdis:=Finset.disjoint_left.mp hST
    constructor
    · rintro ⟨ha|hb,hw⟩
      · exact ha
      · exact (hdis hw (hB hb)).elim
    · intro ha;exact ⟨Or.inl ha,hA ha⟩
  have ht:(A.image Sum.inl∪B.image Sum.inr)∩T=B.image Sum.inr:=by
    ext w
    simp only [Finset.mem_inter,Finset.mem_union]
    have hdis:=Finset.disjoint_left.mp hST
    constructor
    · rintro ⟨ha|hb,hw⟩
      · exact (hdis (hA ha) hw).elim
      · exact hb
    · intro hb;exact ⟨Or.inr hb,hB hb⟩
  rw [hs,ht,Finset.card_image_of_injective _ Sum.inl_injective,Finset.card_image_of_injective _ Sum.inr_injective]
  exact hcard
end Oberwolfach

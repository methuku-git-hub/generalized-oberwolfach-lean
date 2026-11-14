module

public import Oberwolfach.EndpointRootWheelPacking
public import Oberwolfach.InjectiveHubWheelDegrees

@[expose] public section

/-! Physical completion at a triangle endpoint: exact root-edge coverage,
row degree at most two away from the root, spoke row degree at most one
there, and spoke column degree at most three. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 512
set_option maxHeartbeats 2200000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem endpoint_factor_completed_wheels (Q H F : SimpleGraph V) (A B S T : Finset V)
    (hAB : Disjoint A B) (hSA : S⊆A) (hTB : T⊆B) (x : V)
    (hS : ∀ v∈S,Q.Adj x v ∧ ¬F.Adj x v) (hT : ∀ u∈T,H.Adj x u)
    (hfactor : HasResourceDecomposition
      (endpointTriangleVertices (Q:=endpointHostGraph Q H A B) (F:=F) (S:=S) (T:=T)) (S∪T)) :
    ∃ (M : Finset (EndpointTriangle (endpointHostGraph Q H A B) F S T))
      (W : M→OrdinaryWheel Q F H.Adj 3),
      (∀ C,ordinaryWheelHub (W C)=endpointTriangleIndex C.val ∧
        (ordinaryWheelRim (W C)).support.toFinset=insert x (C.val.val∩S)) ∧
      (∀ C D,C≠D → Disjoint (ordinaryWheelResources (W C)) (ordinaryWheelResources (W D))) ∧
      (∀ v∈S,∃! C,Sum.inl s(x,v)∈ordinaryWheelResources (W C)) ∧
      (∀ u∈T,∃! C,Sum.inr (x,u)∈ordinaryWheelResources (W C)) ∧
      (∀ v,v≠x → (wheelFamilyRim W).degree v≤2) ∧
      (∀ v,v≠x → (Finset.univ.filter (fun u=>wheelFamilySpokes W v u)).card≤1) ∧
      (∀ u,(Finset.univ.filter (fun v=>wheelFamilySpokes W v u)).card≤3) := by
  obtain ⟨M,hM,hcover⟩:=hfactor
  obtain ⟨W,hW,hdisj,hrim,hspoke,hdegree⟩:=endpoint_factor_root_wheel_packing Q H F A B S T hAB hSA hTB x hS hT M hM hcover
  have hinj : Function.Injective (fun C:M=>ordinaryWheelHub (W C)) := by
    intro C D he
    by_contra hne
    have hidx : endpointTriangleIndex C.val=endpointTriangleIndex D.val:=
      (hW C).1.symm.trans (he.trans (hW D).1)
    exact Finset.disjoint_left.mp
      (hM C.val C.property D.val D.property (fun h=>hne (Subtype.ext h)))
      (endpointTriangleIndex_mem C.val).1 (hidx.symm ▸ (endpointTriangleIndex_mem D.val).1)
  refine ⟨M,W,hW,hdisj,hrim,hspoke,hdegree,?_,?_⟩
  · intro v hvx
    have hbal:=wheelFamily_rim_degree_spoke_degree W hdisj v
    have hdeg:=hdegree v hvx
    omega
  · exact wheelFamily_injective_hub_degree W hinj

end Oberwolfach

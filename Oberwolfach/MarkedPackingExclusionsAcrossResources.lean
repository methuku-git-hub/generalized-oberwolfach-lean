module

public import Oberwolfach.MarkedFiniteResourceOperations
public import Oberwolfach.MarkedFiniteRemainderTransfer

@[expose] public section
/-! Physical resource equality transfers prescribed arc and spoke exclusions
between typed hosts, using injectivity of the original physical arc map. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K E' K':Type} [Fintype V] [Fintype U] [Fintype E] [Fintype K] [Fintype E'] [Fintype K']
  [DecidableEq V] [DecidableEq U] [DecidableEq E] [DecidableEq K] [DecidableEq E'] [DecidableEq K']
  {tail head:E→V} {ktail khead:K→V} {tail' head':E'→V} {ktail' khead':K'→V}
  {π:Equiv.Perm V} {m b:ℕ} {H₀ HK H₀' HK':V→U→Prop}

theorem marked_packing_exclusions_transfer_on_resources
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (f:E'⊕K'→E⊕K)
    (hs:∀ a,Sum.elim tail ktail (f a)=Sum.elim tail' ktail' a)
    (hd:∀ a,Sum.elim head khead (f a)=Sum.elim head' khead' a)
    (ht:∀ a,markedArcType (f a)=markedArcType a)
    (M:Finset (MarkedWheel tail head ktail khead m π b H₀ HK))
    (N:Finset (MarkedWheel tail' head' ktail' khead' m π b H₀' HK'))
    (A:Finset (E⊕K)) (A':Finset (E'⊕K')) (S:Finset (V×U))
    (hf:∀ a∈A',f a∈A)
    (hres:N.biUnion markedWheelPhysicalResources=M.biUnion markedWheelPhysicalResources)
    (hA:Disjoint A (M.biUnion markedWheelArcs))
    (hS:Disjoint S (M.biUnion markedWheelSpokePairs)):
    Disjoint A' (N.biUnion markedWheelArcs) ∧ Disjoint S (N.biUnion markedWheelSpokePairs):=by
  constructor
  · apply Finset.disjoint_left.mpr
    intro a ha hN
    obtain ⟨W,hW,haW⟩:=Finset.mem_biUnion.mp hN
    have hr:Sum.inl (markedPhysicalEdge tail' head' ktail' khead' π a)∈N.biUnion markedWheelPhysicalResources:=
      Finset.mem_biUnion.mpr ⟨W,hW,markedWheel_arc_resource W a haW⟩
    rw [hres,←markedPackingResources_eq_finite tail head ktail khead π M] at hr
    have heq:markedPhysicalEdge tail head ktail khead π (f a)=markedPhysicalEdge tail' head' ktail' khead' π a:=
      marked_physical_edge_eq_of_endpoints_and_type π a (f a) (hs a) (hd a) (ht a)
    rw [←heq] at hr
    have haM: f a∈M.biUnion markedWheelArcs:=
      (markedFiniteResources_rim tail head ktail khead π hp _ _ (f a)).mp hr
    exact Finset.disjoint_left.mp hA (hf a ha) haM
  · apply Finset.disjoint_left.mpr
    intro z hz hN
    have hr:Sum.inr z∈N.biUnion markedWheelPhysicalResources:=by
      rw [←markedPackingResources_eq_finite tail' head' ktail' khead' π N]
      simp only [markedFiniteResources,Finset.mem_union,Finset.mem_image,Sum.inr.injEq]
      exact Or.inr ⟨z,hN,rfl⟩
    rw [hres,←markedPackingResources_eq_finite tail head ktail khead π M] at hr
    simp only [markedFiniteResources,Finset.mem_union,Finset.mem_image,Sum.inl_ne_inr,Sum.inr.injEq,exists_eq_right] at hr
    rcases hr with hfalse|hr
    · obtain ⟨_,_,hf⟩:=hfalse
      exact hf.elim
    · exact Finset.disjoint_left.mp hS hz hr
end Oberwolfach

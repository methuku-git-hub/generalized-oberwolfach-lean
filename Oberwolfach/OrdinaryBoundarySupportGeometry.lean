module

public import Oberwolfach.BoundarySupportFromPhysicalGraph

@[expose] public section
/-! Actual ordinary hub and rim boundary classes are neighborhoods of
distinct physical outside roots. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U]

def ordinaryBoundaryPhysicalRoot (X:Finset V) (Z:Finset U):
    ({u:U // u∉Z}⊕{v:V // v∉X})↪(V⊕U) where
  toFun:=Sum.elim (fun u=>Sum.inr u.val) (fun v=>Sum.inl v.val)
  inj':=by
    intro a b h
    cases a with
    | inl u =>
      cases b with
      | inl v =>
        simp only [Sum.elim_inl,Sum.inr.injEq] at h
        exact congrArg Sum.inl (Subtype.ext h)
      | inr v => exact (Sum.inr_ne_inl h).elim
    | inr u =>
      cases b with
      | inl v => exact (Sum.inl_ne_inr h).elim
      | inr v =>
        simp only [Sum.elim_inr,Sum.inl.injEq] at h
        exact congrArg Sum.inr (Subtype.ext h)

def ordinaryBoundaryPhysicalSupports (Q:SimpleGraph V) (H:V→U→Prop) (X:Finset V) (Z:Finset U):
    ({u:U // u∉Z}⊕{v:V // v∉X})→Finset (V⊕U):=
  Sum.elim (fun j=>(ordinaryBoundaryHubSet H Z X j).image Sum.inl)
    (fun i=>(ordinaryBoundaryRimSet Q X i).image Sum.inl∪(ordinaryBoundaryRowSet H X Z i).image Sum.inr)

theorem ordinary_boundary_physical_supports_neighbor (Q:SimpleGraph V) (H:V→U→Prop) (X:Finset V) (Z:Finset U):
    ∀i,ordinaryBoundaryPhysicalSupports Q H X Z i⊆
      (ordinaryBoundaryGraph Q H X Z).neighborFinset (ordinaryBoundaryPhysicalRoot X Z i):=by
  intro i w hw
  cases i with
  | inl j =>
    obtain ⟨v,hv,rfl⟩:=Finset.mem_image.mp hw
    have hv':v∈X∧H v j.val:=Finset.mem_filter.mp hv
    apply (SimpleGraph.mem_neighborFinset _ _ _).mpr
    apply (ordinaryBoundaryGraph_adj Q H X Z _ _).mpr
    refine ⟨hv'.2,Or.inl ⟨?_,?_⟩⟩
    · simpa [ordinaryBoundaryPhysicalRoot,ordinaryInnerVertices_right] using j.property
    · simpa [ordinaryInnerVertices_left] using hv'.1
  | inr i =>
    rcases Finset.mem_union.mp hw with hw|hw
    · obtain ⟨v,hv,rfl⟩:=Finset.mem_image.mp hw
      have hv':Q.Adj i.val v∧v∈X:=by
        simpa [ordinaryBoundaryRimSet,SimpleGraph.mem_neighborFinset] using hv
      apply (SimpleGraph.mem_neighborFinset _ _ _).mpr
      apply (ordinaryBoundaryGraph_adj Q H X Z _ _).mpr
      refine ⟨hv'.1,Or.inl ⟨?_,?_⟩⟩
      · simpa [ordinaryBoundaryPhysicalRoot,ordinaryInnerVertices_left] using i.property
      · simpa [ordinaryInnerVertices_left] using hv'.2
    · obtain ⟨u,hu,rfl⟩:=Finset.mem_image.mp hw
      have hu':u∈Z∧H i.val u:=Finset.mem_filter.mp hu
      apply (SimpleGraph.mem_neighborFinset _ _ _).mpr
      apply (ordinaryBoundaryGraph_adj Q H X Z _ _).mpr
      refine ⟨hu'.2,Or.inl ⟨?_,?_⟩⟩
      · simpa [ordinaryBoundaryPhysicalRoot,ordinaryInnerVertices_left] using i.property
      · simpa [ordinaryInnerVertices_right] using hu'.1
end Oberwolfach

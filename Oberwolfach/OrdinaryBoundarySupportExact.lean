module

public import Oberwolfach.OrdinaryBoundarySupportGeometry

@[expose] public section
/-! Every physical boundary neighbor belongs to the corresponding exact
ordinary hub or endpoint support. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U]

theorem ordinary_boundary_supports_eq_neighbors (Q:SimpleGraph V) (H:V→U→Prop) (X:Finset V) (Z:Finset U):
    ∀i,ordinaryBoundaryPhysicalSupports Q H X Z i=
      (ordinaryBoundaryGraph Q H X Z).neighborFinset (ordinaryBoundaryPhysicalRoot X Z i):=by
  intro i
  apply Finset.Subset.antisymm (ordinary_boundary_physical_supports_neighbor Q H X Z i)
  intro w hw
  have hh:=(ordinaryBoundaryGraph_adj Q H X Z _ _).mp ((SimpleGraph.mem_neighborFinset _ _ _).mp hw)
  cases i with
  | inl j =>
    cases w with
    | inl v =>
      simp only [ordinaryBoundaryPhysicalRoot,Sum.elim_inl,ordinaryPhysicalGraph,
        ordinaryInnerVertices_left,ordinaryInnerVertices_right] at hh
      have hv:v∈X:=by
        rcases hh.2 with ⟨_,hv⟩|⟨_,hj⟩
        · exact hv
        · exact (j.property (by simpa [ordinaryBoundaryPhysicalRoot,ordinaryInnerVertices_right] using hj)).elim
      change Sum.inl v∈(ordinaryBoundaryHubSet H Z X j).image Sum.inl
      exact Finset.mem_image.mpr ⟨v,Finset.mem_filter.mpr ⟨hv,hh.1⟩,rfl⟩
    | inr u =>
      simp [ordinaryBoundaryPhysicalRoot,ordinaryPhysicalGraph] at hh
  | inr i =>
    cases w with
    | inl v =>
      simp only [ordinaryBoundaryPhysicalRoot,Sum.elim_inr,ordinaryPhysicalGraph,
        ordinaryInnerVertices_left,ordinaryInnerVertices_right] at hh
      have hv:v∈X:=by
        rcases hh.2 with ⟨_,hv⟩|⟨_,hi⟩
        · exact hv
        · exact (i.property (by simpa [ordinaryBoundaryPhysicalRoot,ordinaryInnerVertices_left] using hi)).elim
      change Sum.inl v∈(ordinaryBoundaryRimSet Q X i).image Sum.inl∪(ordinaryBoundaryRowSet H X Z i).image Sum.inr
      apply Finset.mem_union_left
      exact Finset.mem_image.mpr ⟨v,Finset.mem_inter.mpr ⟨(Q.mem_neighborFinset _ _).mpr hh.1,hv⟩,rfl⟩
    | inr u =>
      simp only [ordinaryBoundaryPhysicalRoot,Sum.elim_inr,ordinaryPhysicalGraph,
        ordinaryInnerVertices_left,ordinaryInnerVertices_right] at hh
      have hu:u∈Z:=by
        rcases hh.2 with ⟨_,hu⟩|⟨_,hi⟩
        · exact hu
        · exact (i.property (by simpa [ordinaryBoundaryPhysicalRoot,ordinaryInnerVertices_left] using hi)).elim
      change Sum.inr u∈(ordinaryBoundaryRimSet Q X i).image Sum.inl∪(ordinaryBoundaryRowSet H X Z i).image Sum.inr
      apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨u,Finset.mem_filter.mpr ⟨hu,hh.1⟩,rfl⟩
end Oberwolfach

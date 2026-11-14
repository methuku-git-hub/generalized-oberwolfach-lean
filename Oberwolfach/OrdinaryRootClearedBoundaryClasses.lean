module

public import Oberwolfach.OrdinaryBoundaryRootSets

@[expose] public section
/-! Once all boundary resources touching the deeper roots have been covered,
all actual outer boundary classes avoid those roots. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_root_cleared_boundary_classes (Q:SimpleGraph V) (H:V→U→Prop)
    (X T:Finset V) (Z W:Finset U)
    (hrim:∀v∈T,∀w∉X,¬Q.Adj v w)
    (hrow:∀v∈T,∀u∉Z,¬H v u)
    (hcol:∀u∈W,∀v∉X,¬H v u):
    (∀i,ordinaryBoundaryRimSet Q X i⊆X\T) ∧
    (∀i,ordinaryBoundaryRowSet H X Z i⊆Z\W) ∧
    (∀j,ordinaryBoundaryHubSet H Z X j⊆X\T):=by
  refine ⟨?_,?_,?_⟩
  · intro i v hv
    have hh:Q.Adj i.val v ∧ v∈X:=by
      simpa only [ordinaryBoundaryRimSet,Finset.mem_inter,SimpleGraph.mem_neighborFinset] using hv
    exact Finset.mem_sdiff.mpr ⟨hh.2,fun hvT=>hrim v hvT i.val i.property hh.1.symm⟩
  · intro i u hu
    have hh:u∈Z ∧ H i.val u:=by simpa only [ordinaryBoundaryRowSet,Finset.mem_filter] using hu
    exact Finset.mem_sdiff.mpr ⟨hh.1,fun huW=>hcol u huW i.val i.property hh.2⟩
  · intro j v hv
    have hh:v∈X ∧ H v j.val:=by simpa only [ordinaryBoundaryHubSet,Finset.mem_filter] using hv
    exact Finset.mem_sdiff.mpr ⟨hh.1,fun hvT=>hrow v hvT j.val j.property hh.2⟩
end Oberwolfach

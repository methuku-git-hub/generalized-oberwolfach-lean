module

public import Oberwolfach.OrdinaryBoundaryRootSets

@[expose] public section
/-! Once the deep-to-outside resources have been covered, the remaining
    boundary classes contain no deeper vertices or hubs. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_boundary_classes_avoid_deep
    (Q:SimpleGraph V) (H:V→U→Prop) (X T:Finset V) (Z W:Finset U)
    (hRim:∀v∈T,∀w∉X,¬Q.Adj v w)
    (hSpokeT:∀v∈T,∀u∉Z,¬H v u)
    (hSpokeW:∀u∈W,∀v∉X,¬H v u):
    (∀j:{u:U // u∉Z},Disjoint (ordinaryBoundaryHubSet H Z X j) T) ∧
    (∀i:{v:V // v∉X},Disjoint (ordinaryBoundaryRimSet Q X i) T) ∧
    (∀i:{v:V // v∉X},Disjoint (ordinaryBoundaryRowSet H X Z i) W) :=by
  constructor
  · intro j
    apply Finset.disjoint_left.mpr
    intro v hv hT
    have hHv:H v j.val:=(Finset.mem_filter.mp hv).2
    exact hSpokeT v hT j.val j.property hHv
  constructor
  · intro i
    apply Finset.disjoint_left.mpr
    intro v hv hT
    have hAdj:Q.Adj i.val v:=(Q.mem_neighborFinset i.val v).mp (Finset.mem_inter.mp hv).1
    exact hRim v hT i.val i.property hAdj.symm
  · intro i
    apply Finset.disjoint_left.mpr
    intro u hu hW
    have hHu:H i.val u:=(Finset.mem_filter.mp hu).2
    exact hSpokeW u hW i.val i.property hHu
end Oberwolfach

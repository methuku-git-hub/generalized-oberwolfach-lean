module

public import Oberwolfach.PhysicalWheelFamilies
public import Oberwolfach.OrdinaryCorrectedInnerStarBalance

@[expose] public section
/-! An indexed family with no deep rim vertices and no deep hubs avoids the
entire physical star of the deeper pair, not only its induced edges. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U I:Type} [Fintype V] [Fintype U] [Fintype I] [DecidableEq V] [DecidableEq U]

def ordinaryDeepRootStar (T:Finset V) (W:Finset U):SimpleGraph (V⊕U):=
  ordinaryPhysicalGraph (ordinaryRimRootStar ⊤ T) (ordinarySpokeRootStar (fun _ _=>True) T W)

theorem ordinary_root_free_wheel_family (Q F:SimpleGraph V) (H:V→U→Prop) (r:ℕ)
    (T:Finset V) (W:Finset U) (C:I→OrdinaryWheel Q F H r)
    (hrim:∀i v,v∈(ordinaryWheelRim (C i)).support→v∉T)
    (hhub:∀i,ordinaryWheelHub (C i)∉W):
    Disjoint (ordinaryPhysicalGraph (wheelFamilyRim C) (wheelFamilySpokes C)) (ordinaryDeepRootStar T W):=by
  apply (ordinaryPhysicalGraph_disjoint _ _ _ _).mpr
  constructor
  · apply disjoint_iff_inf_le.mpr
    intro v w hvw
    obtain ⟨i,hi⟩:=SimpleGraph.iSup_adj.mp hvw.1
    rcases hvw.2.2 with hv|hw
    · exact (hrim i v ⟨w,hi⟩) hv
    · exact (hrim i w ⟨v,hi.symm⟩) hw
  · intro v u h
    obtain ⟨i,hi,hv⟩:=h.1
    rcases h.2.2 with hvT|huW
    · exact hrim i v hv hvT
    · exact hhub i (hi ▸ huW)
end Oberwolfach

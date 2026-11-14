module

public import Oberwolfach.OrdinaryMappedCorrection
public import Oberwolfach.InducedFractionalCycles

@[expose] public section
/-! The embedded induced pair is exactly the ambient graph induced by the
    same finite row and hub sets. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 3000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_induced_rim_map (Q:SimpleGraph V) (I:Finset V):
    (Q.induce (I:Set V)).map (⟨Subtype.val,Subtype.val_injective⟩:I↪V)=spanningRestriction Q I:=by
  ext v w
  constructor
  · intro h
    obtain ⟨a,b,hab,rfl,rfl⟩:=(SimpleGraph.map_adj (⟨Subtype.val,Subtype.val_injective⟩:I↪V) _ v w).mp h
    exact (spanningRestriction_adj Q I a.val b.val).mpr ⟨hab,a.property,b.property⟩
  · intro h
    obtain ⟨hQ,hv,hw⟩:=(spanningRestriction_adj Q I v w).mp h
    exact SimpleGraph.map_adj_apply.mpr (show (Q.induce (I:Set V)).Adj ⟨v,hv⟩ ⟨w,hw⟩ from hQ)

theorem ordinary_induced_spokes_map (H:V→U→Prop) (I:Finset V) (B:Finset U):
    ordinaryMappedSpokes (fun v:I=>fun u:B=>H v.val u.val)
      (⟨Subtype.val,Subtype.val_injective⟩:I↪V) (⟨Subtype.val,Subtype.val_injective⟩:B↪U)=
      (fun v u=>H v u∧v∈I∧u∈B):=by
  funext v u
  apply propext
  constructor
  · rintro ⟨a,b,h,rfl,rfl⟩
    exact ⟨h,a.property,b.property⟩
  · rintro ⟨h,hv,hu⟩
    exact ⟨⟨v,hv⟩,⟨u,hu⟩,h,rfl,rfl⟩
end Oberwolfach

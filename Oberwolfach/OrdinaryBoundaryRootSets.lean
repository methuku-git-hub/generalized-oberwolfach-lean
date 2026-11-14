module

public import Oberwolfach.OrdinaryTriangleSelectedRemainder

@[expose] public section
/-! Canonical outer-root enumeration and actual boundary neighbourhoods. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

def ordinaryOuterRimEmbedding (X:Finset V):{v:V // v∉X}↪V:=⟨Subtype.val,Subtype.val_injective⟩
def ordinaryOuterHubEmbedding (Z:Finset U):{u:U // u∉Z}↪U:=⟨Subtype.val,Subtype.val_injective⟩
def ordinaryBoundaryRimSet (Q:SimpleGraph V) (X:Finset V) (i:{v:V // v∉X}):Finset V:=Q.neighborFinset i.val∩X
def ordinaryBoundaryRowSet (H:V→U→Prop) (X:Finset V) (Z:Finset U) (i:{v:V // v∉X}):Finset U:=Z.filter (H i.val)
def ordinaryBoundaryHubSet (H:V→U→Prop) (Z:Finset U) (X:Finset V) (j:{u:U // u∉Z}):Finset V:=X.filter (fun v=>H v j.val)

theorem ordinary_boundary_root_domains_disjoint (Q:SimpleGraph V) (H:V→U→Prop) (X:Finset V) (Z:Finset U)
    (i:{v:V // v∉X}):
    Disjoint ((ordinaryBoundaryRimSet Q X i).image Sum.inl) ((ordinaryBoundaryRowSet H X Z i).image Sum.inr):=by
  apply Finset.disjoint_left.mpr
  intro a ha hb
  obtain ⟨v,_,rfl⟩:=Finset.mem_image.mp ha
  obtain ⟨u,_,hu⟩:=Finset.mem_image.mp hb
  exact Sum.inr_ne_inl hu

end Oberwolfach

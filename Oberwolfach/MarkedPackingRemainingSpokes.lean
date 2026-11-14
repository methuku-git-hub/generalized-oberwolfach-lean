module

public import Oberwolfach.MarkedPackingResourceDetermination
public import Oberwolfach.MarkedNeighbourhoodPhysicalDeletion
public import Oberwolfach.OrdinaryBoundaryGraph

@[expose] public section

/-! Outside coverage forces every remaining root spoke into the fixed
inner pair. The classes retain precisely the unused physical spokes. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
    {tail head:E→V} {ktail khead:K→V} {m b:ℕ} {π:Equiv.Perm V}
    (H:Bool→V→U→Prop)

theorem marked_packing_spoke_adj_iff
    (M:Finset (MarkedWheel tail head ktail khead m π b (H false) (H true))) (x:V) (u:U):
    (ordinaryPhysicalGraph (markedPackingRimGraph M) (markedPackingSpokes M)).Adj (Sum.inl x) (Sum.inr u)↔
      Sum.inr (x,u)∈M.biUnion markedWheelPhysicalResources:=
  (markedPackingResources_spoke M x u).symm

theorem marked_remaining_spokes_exact
    (M:Finset (MarkedWheel tail head ktail khead m π b (H false) (H true))) (X:Finset V) (Z:Finset U)
    (hcover:∀ x u,x∉X→u∉Z→H false x u∨H true x u→Sum.inr (x,u)∈M.biUnion markedWheelPhysicalResources):
    let C:=ordinaryPhysicalGraph (markedPackingRimGraph M) (markedPackingSpokes M);
    (∀ x,x∉X→∀ u,
      u∈Z.filter (markedDeletePhysicalSpokes H C false x)∪Z.filter (markedDeletePhysicalSpokes H C true x)↔
        (H false x u∨H true x u)∧Sum.inr (x,u)∉M.biUnion markedWheelPhysicalResources)∧
    (∀ u,u∉Z→∀ x,
      x∈X.filter (fun x=>(H false x u∨H true x u)∧¬C.Adj (Sum.inl x) (Sum.inr u))↔
        (H false x u∨H true x u)∧Sum.inr (x,u)∉M.biUnion markedWheelPhysicalResources):=by
  intro C
  constructor
  · intro x hx u
    have he:C.Adj (Sum.inl x) (Sum.inr u)↔Sum.inr (x,u)∈M.biUnion markedWheelPhysicalResources:=
      marked_packing_spoke_adj_iff H M x u
    have hu:(H false x u∨H true x u)→Sum.inr (x,u)∉M.biUnion markedWheelPhysicalResources→u∈Z:=by
      intro hH hn
      by_contra hz
      exact hn (hcover x u hx hz hH)
    simp only [Finset.mem_union,Finset.mem_filter,markedDeletePhysicalSpokes,he]
    tauto
  · intro u hu x
    have he:C.Adj (Sum.inl x) (Sum.inr u)↔Sum.inr (x,u)∈M.biUnion markedWheelPhysicalResources:=
      marked_packing_spoke_adj_iff H M x u
    have hx:(H false x u∨H true x u)→Sum.inr (x,u)∉M.biUnion markedWheelPhysicalResources→x∈X:=by
      intro hH hn
      by_contra hz
      exact hn (hcover x u hz hu hH)
    simp only [Finset.mem_filter,he]
    tauto
end Oberwolfach

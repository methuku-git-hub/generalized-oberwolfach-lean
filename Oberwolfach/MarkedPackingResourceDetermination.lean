module

public import Oberwolfach.MarkedSamplePhysicalDeletionLift

@[expose] public section

/-! Physical resource equality determines the rim graph and the spoke
relation, so changing the host representation preserves all degree bounds. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
  {tail head:E→V} {ktail khead:K→V} {m b:ℕ} {π:Equiv.Perm V} {H₀ HK:V→U→Prop}

theorem markedPackingResources_rim (M:Finset (MarkedWheel tail head ktail khead m π b H₀ HK))
    (e:Finset V):Sum.inl e∈M.biUnion markedWheelPhysicalResources↔e∈markedPackingRims M:=by
  simp only [markedPackingRims,Finset.mem_biUnion,markedWheelPhysicalResources_rim]

theorem markedPackingResources_spoke (M:Finset (MarkedWheel tail head ktail khead m π b H₀ HK))
    (x:V) (u:U):Sum.inr (x,u)∈M.biUnion markedWheelPhysicalResources↔markedPackingSpokes M x u:=by
  simp only [Finset.mem_biUnion,markedWheelPhysicalResources_spoke,markedPackingSpokes,markedWheelRows]

variable {E' K':Type} {tail' head':E'→V} {ktail' khead':K'→V}
  {m' b':ℕ} {π':Equiv.Perm V} {H₀' HK':V→U→Prop}

theorem markedPackingResourceEquality_graphs
    (M:Finset (MarkedWheel tail head ktail khead m π b H₀ HK))
    (N:Finset (MarkedWheel tail' head' ktail' khead' m' π' b' H₀' HK'))
    (he:M.biUnion markedWheelPhysicalResources=N.biUnion markedWheelPhysicalResources):
    markedPackingRimGraph M=markedPackingRimGraph N ∧
    (∀ x u,markedPackingSpokes M x u↔markedPackingSpokes N x u):=by
  have hr:markedPackingRims M=markedPackingRims N:=by
    ext e
    rw [←markedPackingResources_rim,←markedPackingResources_rim,he]
  refine ⟨?_,?_⟩
  · unfold markedPackingRimGraph
    rw [hr]
  · intro x u
    rw [←markedPackingResources_spoke,←markedPackingResources_spoke,he]

end Oberwolfach

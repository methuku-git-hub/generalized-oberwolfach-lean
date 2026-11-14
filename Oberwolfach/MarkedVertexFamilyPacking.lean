module

public import Oberwolfach.DirectedIncidenceHubAssignments
public import Oberwolfach.MarkedActualWheelPacking

@[expose] public section

/-! Actual vertex-wheel packing after a possibly noninjective row map.
The two ends of each mapped original arc are distinct; together with the
incidence permutations, this proves injectivity of the root--hub pairs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 9000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K X A:Type} [Fintype V] [DecidableEq V] [DecidableEq U]
    {tail head:E→V} {ktail khead:K→V} {π:Equiv.Perm V} {b:ℕ} {H₀ HK:V→U→Prop}

 theorem marked_vertex_wheel_family_packing (n:ℕ) (src dst:A→X)
    (f:X→V) (hub:A→U) (hhub:Function.Injective hub)
    (hloop:∀ e,f (dst e)≠f (src e))
    (σ:∀ v,Equiv.Perm (DirectedIncidence src dst v))
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (p:(Σ v,DirectedIncidence src dst v)→(Fin (n+1)→V))
    (j:(Σ v,DirectedIncidence src dst v)→Bool) (R:Finset V)
    (W:(Σ v,DirectedIncidence src dst v)→MarkedWheel tail head ktail khead (n+1) π b H₀ HK)
    (hW:∀ i a,(W i).1.val a=rootedCycleOrder (markedRootOrder (n+1) (j i)) (f i.1) (p i) a)
    (hWu:∀ i,(W i).2.val=hub (directedIncidenceEdge (σ i.1 i.2)))
    (hroot:∀ i:Σ v,DirectedIncidence src dst v,f i.1∈R)
    (hfree:∀ i a,p i a∉R)
    (hdis:∀ i k,i≠k→Disjoint (Finset.univ.image (p i)) (Finset.univ.image (p k))):
    ∀ i k,i≠k→Disjoint (markedWheelPhysicalResources (W i)) (markedWheelPhysicalResources (W k)):=by
  apply marked_actual_spoke_wheel_packing n hp p (fun i=>f i.1) j R W hW hroot hfree hdis
  intro i k he
  apply directed_incidence_assigned_hubs_injective f hub hhub hloop σ
  simpa only [hWu] using he

end Oberwolfach

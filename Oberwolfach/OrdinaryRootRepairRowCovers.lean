module

public import Oberwolfach.OrdinaryRootColumnRepair
public import Oberwolfach.OrdinaryRowCoverSpokeTransfer
public import Oberwolfach.RootedRowCover

@[expose] public section
/-! Discard non-rooted wheels, then transfer the repaired spoke relation
back to the actual relation. Root stars and physical disjointness survive. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_root_repair_row_covers (Q F:SimpleGraph V) (H J:V→U→Prop)
    (T:Finset V) (B:Finset U) (n r K:ℕ) (x:Fin n→V) (A:Finset V)
    (hxT:∀i,x i∈T) (hxB:∀i u,J (x i) u→u∈B):
    let J':=ordinaryRootColumnRepair H J T B;
    ∀ M:Fin n→Finset (OrdinaryWheel Q F J' r),
      (∀i,OrdinaryRowCover (M i) (x i) A K) →
      (∀i k,i≠k→Disjoint ((M i).biUnion ordinaryWheelResources) ((M k).biUnion ordinaryWheelResources)) →
    ∃ N:Fin n→Finset (OrdinaryWheel Q F J r),
      (∀i,OrdinaryRowCover (N i) (x i) A K) ∧
      (∀i k,i≠k→Disjoint ((N i).biUnion ordinaryWheelResources) ((N k).biUnion ordinaryWheelResources)):=by
  intro J' M hM hcross
  let P:=fun i=>(M i).filter (fun W=>x i∈(ordinaryWheelRim W).support)
  have hPM:∀i,P i⊆M i:=fun _=>Finset.filter_subset _ _
  have hP:∀i,OrdinaryRowCover (P i) (x i) A K:=fun i=>(hM i).filter_root
  have hcrossP:∀i k,i≠k→Disjoint ((P i).biUnion ordinaryWheelResources) ((P k).biUnion ordinaryWheelResources):=by
    intro i k hik
    apply (hcross i k hik).mono
    · intro e he
      obtain ⟨W,hW,he⟩:=Finset.mem_biUnion.mp he
      exact Finset.mem_biUnion.mpr ⟨W,hPM i hW,he⟩
    · intro e he
      obtain ⟨W,hW,he⟩:=Finset.mem_biUnion.mp he
      exact Finset.mem_biUnion.mpr ⟨W,hPM k hW,he⟩
  have hroot:∀i u,J' (x i) u↔J (x i) u:=by
    intro i u;simp [J',ordinaryRootColumnRepair,hxT i]
  have hkeep:∀i,∀W∈P i,∀v∈(ordinaryWheelRim W).support,J v (ordinaryWheelHub W):=by
    intro i W hW v hv
    have hx:(x i)∈(ordinaryWheelRim W).support:=(Finset.mem_filter.mp hW).2
    have hstar:J' (x i) (ordinaryWheelHub W):=W.property.1 (x i) hx
    have hb:ordinaryWheelHub W∈B:=hxB i _ ((hroot i _).mp hstar)
    have hw:=W.property.1 v hv
    change J' v (ordinaryWheelHub W) at hw
    simpa [J',ordinaryRootColumnRepair,hb] using hw
  let N:=fun i=>ordinarySpokeTransferPacking (P i) (hkeep i)
  refine ⟨N,?_,?_⟩
  · intro i
    exact ordinary_spoke_transfer_row_cover (P i) (hkeep i) (x i) A K (hroot i) (hP i)
  · intro i k hik
    change Disjoint ((ordinarySpokeTransferPacking (P i) (hkeep i)).biUnion ordinaryWheelResources)
      ((ordinarySpokeTransferPacking (P k) (hkeep k)).biUnion ordinaryWheelResources)
    rw [ordinary_spoke_transfer_resources,ordinary_spoke_transfer_resources]
    exact hcrossP i k hik
end Oberwolfach

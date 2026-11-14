module

public import Oberwolfach.OrderedOrdinaryUniversalWheel
public import Oberwolfach.OrdinaryUnshiftedPhysicalCandidateInjection
public import Oberwolfach.CycleEdgeEnumeration

@[expose] public section
/-! The physical resources tested by the matching are exactly the rim and
spokes of the actual ordinary wheel represented by its cyclic tuple. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordered_ordinary_physical_wheel_resources {n r b:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (π:Equiv.Perm (Fin n)) (hr:3≤r) (W:OrderedOrdinaryWheel (U:=U) π b r):
    ordinaryWheelResources (orderedOrdinaryUniversalWheel hr W)=
      ((orderedOrdinaryResources W).map ordinaryMarkedResourceEmbedding).image (ordinaryMixedPhysicalResource π) :=by
  let f:Fin r↪Fin n:=⟨W.1.val,permutationSeparated_injective π b W.1.val W.1.property⟩
  have hf:∀u v,(ordinaryWheelRim (orderedOrdinaryUniversalWheel hr W)).Adj u v ↔
      ∃ i j:Fin r,f i=u ∧ f j=v ∧
        ((i.val+1)%r=j.val ∨ (j.val+1)%r=i.val):=by
    intro u v
    change ((SimpleGraph.cycleGraph r).map f).Adj u v ↔ _
    rw [SimpleGraph.map_adj]
    constructor
    · rintro ⟨i,j,hij,hi,hj⟩
      exact ⟨i,j,hi,hj,(cycleGraph_modular_adj (by omega) i j).mp hij⟩
    · rintro ⟨i,j,hi,hj,hij⟩
      exact ⟨i,j,(cycleGraph_modular_adj (by omega) i j).mpr hij,hi,hj⟩
  have he: (ordinaryWheelRim (orderedOrdinaryUniversalWheel hr W)).edgeFinset=
      Finset.univ.image (fun i:Fin r=>s(W.1.val i,W.1.val (cycleNext i))):=by
    exact cycle_copy_edgeFinset hr f hf
  have hs:(ordinaryWheelRim (orderedOrdinaryUniversalWheel hr W)).support.toFinset=
      Finset.univ.image W.1.val:=by
    ext v
    rw [Set.mem_toFinset,ordered_ordinary_universal_support]
    simp
  unfold ordinaryWheelResources
  rw [he,hs]
  simp only [ordered_ordinary_universal_hub,orderedOrdinaryResources,Finset.map_union,Finset.image_union,
    Finset.map_eq_image,Finset.image_image]
  congr 1 <;> apply Finset.image_congr <;> intro i _ <;>
    simp [ordinaryMixedPhysicalResource,ordinaryMarkedResourceEmbedding,orderedOrdinaryResourceEmbedding,markedPairPhysical]
end Oberwolfach

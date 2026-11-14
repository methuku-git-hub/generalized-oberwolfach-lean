module

public import Oberwolfach.MarkedPackingIntervalReconstruction
public import Oberwolfach.ResourceDecompositions

@[expose] public section
/-! Unpack an exact physical resource decomposition into the packing and
spoke-cover conditions used by marked interval reconstruction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type*} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
  {tail head:E→V} {ktail khead:K→V} {m b:ℕ} {π:Equiv.Perm V} {H₀ Hₖ:V→U→Prop}

def markedDecompositionTarget (Rim:Finset (Finset V)) (H₀ Hₖ:V→U→Prop):Finset (Finset V⊕(V×U)) :=
  Rim.image Sum.inl ∪ (Finset.univ.filter (fun vu:V×U=>H₀ vu.1 vu.2∨Hₖ vu.1 vu.2)).image Sum.inr

theorem marked_decomposition_packing_bridge
    (Rim:Finset (Finset V))
    (hdec:HasResourceDecomposition (markedWheelPhysicalResources (tail:=tail) (head:=head) (ktail:=ktail) (khead:=khead)
      (m:=m) (π:=π) (b:=b) (H₀:=H₀) (Hₖ:=Hₖ)) (markedDecompositionTarget Rim H₀ Hₖ)):
    ∃P:Finset (MarkedWheel tail head ktail khead m π b H₀ Hₖ),
      (∀W∈P,∀Z∈P,W≠Z→Disjoint (markedWheelPhysicalResources W) (markedWheelPhysicalResources Z)) ∧
      (∀v u,Sum.inr (v,u)∈P.biUnion markedWheelPhysicalResources ↔ H₀ v u∨Hₖ v u) ∧
      P.biUnion (fun W=>markedCyclePhysicalEdges tail head ktail khead m π b W.1)=Rim := by
  obtain ⟨P,hP,hcover⟩:=hdec
  refine ⟨P,hP,?_,?_⟩
  · intro v u
    rw [hcover]
    simp [markedDecompositionTarget]
  · ext e
    have hh:=congrArg (fun S:Finset (Finset V⊕(V×U))=>Sum.inl e∈S) hcover
    simpa only [Finset.mem_biUnion,markedWheelPhysicalResources_rim,markedDecompositionTarget,
      Finset.mem_union,Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and,
      Sum.inl.injEq,Sum.inr_ne_inl,and_false,exists_false,or_false,exists_eq_right] using Iff.of_eq hh
end Oberwolfach

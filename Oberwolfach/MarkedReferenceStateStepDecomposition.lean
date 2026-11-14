module

public import Oberwolfach.MarkedReferenceStateRemainder

@[expose] public section

/-! The exact resources covered in one reference-state step. The packing
must avoid the recorded deletion; the remaining resource identity is then
proved by finite set subtraction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [LinearOrder V] [DecidableEq U]

theorem marked_reference_state_step_decomposition
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ) (σ:RawMarkedOutcome V U Γ Color)
    (H:Bool → V → U → Prop) (D:MarkedReferenceDeletion P π d σ) :
    let E:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let K:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    let S:=Finset.univ.filter (fun z:V×U=>H false z.1 z.2∨H true z.1 z.2);
    ∀ M:Finset (MarkedWheel (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) m π (3*d) (H false) (H true)),
    (∀ Y∈M,∀ Z∈M,Y≠Z → Disjoint (markedWheelPhysicalResources Y) (markedWheelPhysicalResources Z)) →
    M.biUnion markedWheelArcs⊆Finset.univ\D.arcs → M.biUnion markedWheelSpokePairs⊆S\D.spokes →
    let L:=markedFiniteResources (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) π
      (Finset.univ\(D.arcs∪M.biUnion markedWheelArcs)) (S\(D.spokes∪M.biUnion markedWheelSpokePairs));
    L=D.remaining H\M.biUnion markedWheelPhysicalResources ∧ L⊆D.remaining H ∧
    HasResourceDecomposition
      (fun W:MarkedWheel (fun e:E=>e.val.1) (fun e=>e.val.2)
        (fun e:K=>e.val.1) (fun e=>e.val.2) m π (3*d) (H false) (H true)=>markedWheelPhysicalResources W)
      (D.remaining H\L) := by
  intro E K S M hM hA hS L
  have hres:M.biUnion markedWheelPhysicalResources⊆D.remaining H:=by
    rw [←markedPackingResources_eq_finite,D.remaining_eq]
    exact markedFiniteResources_mono hA hS
  have hL:L=D.remaining H\M.biUnion markedWheelPhysicalResources:=by
    rw [D.remaining_eq]
    rw [←markedPackingResources_eq_finite,←markedFiniteResources_sdiff _ _ _ _ π
      (markedSampleArc_physical_injective P π (3*d) _)]
    have hAA : Finset.univ \ (D.arcs ∪ M.biUnion markedWheelArcs) =
        (Finset.univ \ D.arcs) \ M.biUnion markedWheelArcs := by
      ext a
      simp only [Finset.mem_sdiff, Finset.mem_union]
      tauto
    have hSS : S \ (D.spokes ∪ M.biUnion markedWheelSpokePairs) =
        (S \ D.spokes) \ M.biUnion markedWheelSpokePairs := by
      ext a
      simp only [Finset.mem_sdiff, Finset.mem_union]
      tauto
    exact congrArg₂ (markedFiniteResources (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) π) hAA hSS
  refine ⟨hL,by rw [hL];exact Finset.sdiff_subset,?_⟩
  have heq:D.remaining H\L=M.biUnion markedWheelPhysicalResources:=by
    rw [hL]
    ext a
    have hh:=fun ha=>hres (x:=a) ha
    simp only [Finset.mem_sdiff]
    tauto
  rw [heq]
  exact ⟨M,hM,rfl⟩

end Oberwolfach

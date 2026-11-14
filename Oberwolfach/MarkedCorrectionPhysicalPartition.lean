module

public import Oberwolfach.MarkedDeletedSampleResources

@[expose] public section
/-! The original physical sample is partitioned exactly into the correction
and the physically deleted remainder. This does not assert a decomposition
of the correction into wheels. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_correction_physical_partition
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (σ:RawMarkedOutcome V U Γ Color)
    (H:Bool→V→U→Prop):
    let E:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let K:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    let tail:=fun e:E=>e.val.1
    let head:=fun e:E=>e.val.2
    let ktail:=fun e:K=>e.val.1
    let khead:=fun e:K=>e.val.2
    let S:=Finset.univ.filter (fun z:V×U=>H false z.1 z.2∨H true z.1 z.2);
    ∀ (DA:Finset (E⊕K)) (DS:Finset (V×U)),DS⊆S →
    let C:=markedFiniteResources tail head ktail khead π DA DS
    let Full:=markedFiniteResources tail head ktail khead π Finset.univ S
    let σ':=rawMarkedDeleteRims σ (markedSampleArcSetGraph P π d σ DA).edgeFinset
    let H':=markedDeletePhysicalSpokes H (markedFiniteSpokeGraph DS)
    let E':=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) false
    let K':=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) true
    let Rest:=markedFiniteResources (fun e:E'=>e.val.1) (fun e=>e.val.2)
      (fun e:K'=>e.val.1) (fun e=>e.val.2) π Finset.univ
      (Finset.univ.filter (fun z:V×U=>H' false z.1 z.2∨H' true z.1 z.2));
    C⊆Full ∧ Disjoint C Rest ∧ C∪Rest=Full := by
  intro E K tail head ktail khead S DA DS hDS C Full σ' H' E' K' Rest
  have hsub:C⊆Full:=by
    dsimp only [C,Full,markedFiniteResources]
    exact Finset.union_subset_union (Finset.image_mono _ (Finset.subset_univ DA)) (Finset.image_mono _ hDS)
  have heq:Rest=Full\C:=marked_deleted_sample_resources P π d σ H DA DS
  refine ⟨hsub,?_,?_⟩
  · rw [heq]
    apply Finset.disjoint_left.mpr
    intro x hx hy
    exact (Finset.mem_sdiff.mp hy).2 hx
  · rw [heq]
    exact Finset.union_sdiff_of_subset hsub
end Oberwolfach

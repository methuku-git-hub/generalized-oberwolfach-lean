module

public import Oberwolfach.MarkedFinitePhysicalDeletion
public import Oberwolfach.MarkedFiniteResourceOperations

@[expose] public section

/-! The actual sample after canonical physical deletions contains exactly
the original resources minus the specified finite arc and spoke resources.
Physical injectivity makes this an equality, rather than an inclusion. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_deleted_sample_resources
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (σ:RawMarkedOutcome V U Γ Color)
    (H:Bool→V→U→Prop):
    let E₀:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let E₁:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    let tail:=fun e:E₀=>e.val.1
    let head:=fun e:E₀=>e.val.2
    let ktail:=fun e:E₁=>e.val.1
    let khead:=fun e:E₁=>e.val.2
    ∀ (KA:Finset (E₀⊕E₁)) (KS:Finset (V×U)),
    let DR:=markedSampleArcSetGraph P π d σ KA
    let DS:=markedFiniteSpokeGraph KS
    let σ':=rawMarkedDeleteRims σ DR.edgeFinset
    let H':=markedDeletePhysicalSpokes H DS
    let E₀':=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) false
    let E₁':=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) true
    markedFiniteResources (fun e:E₀'=>e.val.1) (fun e=>e.val.2)
      (fun e:E₁'=>e.val.1) (fun e=>e.val.2) π Finset.univ
      (Finset.univ.filter (fun z:V×U=>H' false z.1 z.2∨H' true z.1 z.2))=
    markedFiniteResources tail head ktail khead π Finset.univ
      (Finset.univ.filter (fun z:V×U=>H false z.1 z.2∨H true z.1 z.2))\
        markedFiniteResources tail head ktail khead π KA KS:=by
  intro E₀ E₁ tail head ktail khead KA KS DR DS σ' H' E₀' E₁'
  have hr:Finset.univ.image (markedSampleDeletedArcsEmbedding P π d σ DR.edgeFinset)=Finset.univ\KA:=by
    rw [markedSampleDeletedArcsEmbedding_range]
    exact markedSampleArcSetGraph_remaining P π d σ KA
  have hs:Finset.univ.filter (fun z:V×U=>H' false z.1 z.2∨H' true z.1 z.2)=
      (Finset.univ.filter (fun z:V×U=>H false z.1 z.2∨H true z.1 z.2))\KS:=by
    ext z
    simp only [H',DS,markedDeletePhysicalSpokes,markedFiniteSpokeGraph_adj,
      Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_sdiff]
    tauto
  rw [←markedFiniteResources_sdiff tail head ktail khead π
    (markedSampleArc_physical_injective P π (3*d) _) Finset.univ KA _ KS]
  unfold markedFiniteResources
  rw [hs,←hr,Finset.image_image]
  congr 1
  apply Finset.image_congr
  intro a _
  cases a <;> rfl

end Oberwolfach

module

public import Oberwolfach.MarkedReservedResourceDeletionProtection
public import Oberwolfach.MarkedFiniteResourceOperations

@[expose] public section
/-! The first deletion consists of prescribed resources within the inner
pair and a packing disjoint from the reserved absorber. It therefore leaves
every reserved typed rim and spoke unchanged. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_first_deletion_preserves_reserved_resources
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ) (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (C:Finset (Finset V⊕(V×U))) (I:Finset V) (J:Finset U)
    (hI:∀ x,π x∈I↔x∈I) (hC:∀ e∈C,¬markedInnerResource I J e):
    let E:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let K:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    let tail:=fun e:E=>e.val.1
    let head:=fun e:E=>e.val.2
    let ktail:=fun e:K=>e.val.1
    let khead:=fun e:K=>e.val.2;
    ∀ (A:Finset (E⊕K)) (S:Finset (V×U))
      (M:Finset (MarkedWheel tail head ktail khead m π (3*d) (H false) (H true))),
    (∀ a∈A,Sum.elim tail ktail a∈I∧Sum.elim head khead a∈I)→
    (∀ z∈S,z.1∈I∧z.2∈J)→Disjoint C (M.biUnion markedWheelPhysicalResources)→
    let DR:=markedSampleArcSetGraph P π d σ (A∪M.biUnion markedWheelArcs)
    let DS:=markedFiniteSpokeGraph (S∪M.biUnion markedWheelSpokePairs)
    let σ':=rawMarkedDeleteRims σ DR.edgeFinset
    let H':=markedDeletePhysicalSpokes H DS
    let E':=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) false
    let K':=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) true;
    (∀ x y,Sum.inl ({x,y}:Finset V)∈C→¬DR.Adj x y) ∧
    (∀ v u,Sum.inr (v,u)∈C→¬DS.Adj (Sum.inl v) (Sum.inr u)) ∧
    (∀ e:E,Sum.inl ({e.val.1,e.val.2}:Finset V)∈C→∃ e':E',e'.val=e.val) ∧
    (∀ e:K,Sum.inl ({e.val.1,π e.val.2}:Finset V)∈C→∃ e':K',e'.val=e.val) ∧
    (∀ b v u,Sum.inr (v,u)∈C→H b v u→H' b v u) :=by
  intro E K tail head ktail khead A S M hA hS hM DR DS σ' H' E' K'
  have hR:∀ x y,Sum.inl ({x,y}:Finset V)∈C→¬DR.Adj x y:=by
    intro x y hc hxy
    obtain ⟨a,ha,he⟩:=Finset.mem_image.mp hxy.2
    rcases Finset.mem_union.mp ha with ha|ha
    · have hi:=hA a ha
      have hs:markedPhysicalEdge tail head ktail khead π a⊆I:=by
        cases a with
        | inl e=>
          simpa only [markedPhysicalEdge,Sum.elim_inl,Finset.insert_subset_iff,Finset.singleton_subset_iff] using hi
        | inr e=>
          simpa only [markedPhysicalEdge,Sum.elim_inr,Finset.insert_subset_iff,Finset.singleton_subset_iff,hI] using hi
      apply hC _ hc
      change ({x,y}:Finset V)⊆I
      rw [←he]
      exact hs
    · obtain ⟨W,hW,hWa⟩:=Finset.mem_biUnion.mp ha
      have hw:Sum.inl (markedPhysicalEdge tail head ktail khead π a)∈M.biUnion markedWheelPhysicalResources:=
        Finset.mem_biUnion.mpr ⟨W,hW,markedWheel_arc_resource W a hWa⟩
      rw [he] at hw
      exact Finset.disjoint_left.mp hM hc hw
  have hSp:∀ v u,Sum.inr (v,u)∈C→¬DS.Adj (Sum.inl v) (Sum.inr u):=by
    intro v u hc huv
    have hm: (v,u)∈S∪M.biUnion markedWheelSpokePairs:=(markedFiniteSpokeGraph_adj _ v u).mp huv
    rcases Finset.mem_union.mp hm with hs|hs
    · exact hC _ hc (hS (v,u) hs)
    · have hw:Sum.inr (v,u)∈M.biUnion markedWheelPhysicalResources:=by
        rw [←markedPackingResources_eq_finite tail head ktail khead π M]
        simp only [markedFiniteResources,Finset.mem_union,Finset.mem_image,Sum.inr.injEq]
        exact Or.inr ⟨(v,u),hs,rfl⟩
      exact Finset.disjoint_left.mp hM hc hw
  exact ⟨hR,hSp,marked_reserved_resources_survive_physical_deletion P π d σ H C DR DS hR hSp⟩

/-- The same absorber survives both the prescribed deletion and a later
packing disjoint from its physical resources. -/
theorem marked_two_stage_deletions_preserve_reserved_resources
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ) (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (C:Finset (Finset V⊕(V×U))) (I:Finset V) (J:Finset U)
    (hI:∀ x,π x∈I↔x∈I) (hC:∀ e∈C,¬markedInnerResource I J e):
    let E:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let K:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    let tail:=fun e:E=>e.val.1
    let head:=fun e:E=>e.val.2
    let ktail:=fun e:K=>e.val.1
    let khead:=fun e:K=>e.val.2;
    ∀ (A:Finset (E⊕K)) (S:Finset (V×U))
      (M:Finset (MarkedWheel tail head ktail khead m π (3*d) (H false) (H true))),
    (∀ a∈A,Sum.elim tail ktail a∈I∧Sum.elim head khead a∈I)→
    (∀ z∈S,z.1∈I∧z.2∈J)→Disjoint C (M.biUnion markedWheelPhysicalResources)→
    let DR₁:=markedSampleArcSetGraph P π d σ (A∪M.biUnion markedWheelArcs)
    let DS₁:=markedFiniteSpokeGraph (S∪M.biUnion markedWheelSpokePairs)
    let σ₁:=rawMarkedDeleteRims σ DR₁.edgeFinset
    let H₁:=markedDeletePhysicalSpokes H DS₁
    let E₁:=MarkedSampleArc P π (3*d) (fun e=>σ₁ (Sum.inl e)) false
    let K₁:=MarkedSampleArc P π (3*d) (fun e=>σ₁ (Sum.inl e)) true
    let tail₁:=fun e:E₁=>e.val.1
    let head₁:=fun e:E₁=>e.val.2
    let ktail₁:=fun e:K₁=>e.val.1
    let khead₁:=fun e:K₁=>e.val.2;
    ∀ MD:Finset (MarkedWheel tail₁ head₁ ktail₁ khead₁ m π (3*d) (H₁ false) (H₁ true)),
    Disjoint C (MD.biUnion markedWheelPhysicalResources)→
    let DR₂:=markedPackingRimGraph MD
    let DS₂:=markedFiniteSpokeGraph (MD.biUnion markedWheelSpokePairs)
    let σ₂:=rawMarkedDeleteRims σ₁ DR₂.edgeFinset
    let H₂:=markedDeletePhysicalSpokes H₁ DS₂
    let E₂:=MarkedSampleArc P π (3*d) (fun e=>σ₂ (Sum.inl e)) false
    let K₂:=MarkedSampleArc P π (3*d) (fun e=>σ₂ (Sum.inl e)) true;
    (∀ e:E,Sum.inl ({e.val.1,e.val.2}:Finset V)∈C→∃ e':E₂,e'.val=e.val) ∧
    (∀ e:K,Sum.inl ({e.val.1,π e.val.2}:Finset V)∈C→∃ e':K₂,e'.val=e.val) ∧
    (∀ b v u,Sum.inr (v,u)∈C→H b v u→H₂ b v u) :=by
  intro E K tail head ktail khead A S M hA hS hM DR₁ DS₁ σ₁ H₁ E₁ K₁ tail₁ head₁ ktail₁ khead₁ MD hMD DR₂ DS₂ σ₂ H₂ E₂ K₂
  have hfirst:=marked_first_deletion_preserves_reserved_resources P π d m σ H C I J hI hC A S M hA hS hM
  have hR₂:∀ x y,Sum.inl ({x,y}:Finset V)∈C→¬DR₂.Adj x y:=by
    intro x y hc hxy
    have hw:Sum.inl ({x,y}:Finset V)∈MD.biUnion markedWheelPhysicalResources:=
      (markedPackingResources_rim MD _).mpr hxy.2
    exact Finset.disjoint_left.mp hMD hc hw
  have hS₂:∀ v u,Sum.inr (v,u)∈C→¬DS₂.Adj (Sum.inl v) (Sum.inr u):=by
    intro v u hc huv
    have hs:(v,u)∈MD.biUnion markedWheelSpokePairs:=(markedFiniteSpokeGraph_adj _ v u).mp huv
    have hw:Sum.inr (v,u)∈MD.biUnion markedWheelPhysicalResources:=by
      rw [←markedPackingResources_eq_finite tail₁ head₁ ktail₁ khead₁ π MD]
      simp only [markedFiniteResources,Finset.mem_union,Finset.mem_image,Sum.inr.injEq]
      exact Or.inr ⟨(v,u),hs,rfl⟩
    exact Finset.disjoint_left.mp hMD hc hw
  exact marked_reserved_resources_survive_two_deletions P π d σ H C DR₁ DR₂ DS₁ DS₂
    hfirst.1 hR₂ hfirst.2.1 hS₂
end Oberwolfach

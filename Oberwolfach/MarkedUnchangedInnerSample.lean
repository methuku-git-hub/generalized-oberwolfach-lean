module

public import Oberwolfach.MarkedDeletedSampleResources
public import Oberwolfach.MarkedPhysicalDeletionRestriction
public import Oberwolfach.MarkedEmptyPhysicalDeletion

@[expose] public section

/-! If the actual removed physical resources are empty on an inner pair,
the restricted raw sample and both restricted spoke relations are exactly
unchanged. This is an equality of the objects, not an error estimate. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color : Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [LinearOrder V] [DecidableEq U]

theorem marked_removed_resources_empty_inner
    (P : SimpleGraph V) (π : Equiv.Perm V) (d : ℕ) (σ : RawMarkedOutcome V U Γ Color) :
    let E := MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let K := MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true;
    ∀ (A : Finset (E⊕K)) (S : Finset (V×U)) (I : Finset V) (J : Finset U),
    (markedFiniteResources (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) π A S).filter (markedInnerResource I J)=∅→
    (∀ x∈I,∀ y∈I,¬(markedSampleArcSetGraph P π d σ A).Adj x y) ∧
    (∀ x∈I,∀ u∈J,¬(markedFiniteSpokeGraph S).Adj (Sum.inl x) (Sum.inr u)) := by
  intro E K A S I J hEmpty
  let R := markedFiniteResources (fun e:E=>e.val.1) (fun e=>e.val.2)
    (fun e:K=>e.val.1) (fun e=>e.val.2) π A S
  have hNot (e : Finset V⊕(V×U)) (he : e∈R) : ¬markedInnerResource I J e := by
    intro hi
    have hh : e∈R.filter (markedInnerResource I J) := Finset.mem_filter.mpr ⟨he,hi⟩
    rw [hEmpty] at hh
    exact Finset.notMem_empty _ hh
  constructor
  · intro x hx y hy hxy
    obtain ⟨a,ha,he⟩ := Finset.mem_image.mp hxy.2
    have hr : Sum.inl ({x,y}:Finset V)∈R := by
      apply Finset.mem_union_left
      exact Finset.mem_image.mpr ⟨a,ha,congrArg Sum.inl he⟩
    apply hNot _ hr
    change ∀ z∈({x,y}:Finset V),z∈I
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl|hz
    · exact hx
    · exact Finset.mem_singleton.mp hz ▸ hy
  · intro x hx u hu hxu
    have hs : (x,u)∈S := (markedFiniteSpokeGraph_adj S x u).mp hxu
    have hr : Sum.inr (x,u)∈R := Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(x,u),hs,rfl⟩)
    exact hNot _ hr ⟨hx,hu⟩

theorem marked_raw_pair_unchanged_on_inner
    {W Z : Type} [Fintype W] [Fintype Z] [LinearOrder W] [DecidableEq Z]
    (P : SimpleGraph V) (π : Equiv.Perm V) (d : ℕ) (σ : RawMarkedOutcome V U Γ Color)
    (H : Bool→V→U→Prop) :
    let E := MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let K := MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true;
    ∀ (A : Finset (E⊕K)) (S : Finset (V×U)) (I : Finset V) (J : Finset U),
    (markedFiniteResources (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) π A S).filter (markedInnerResource I J)=∅→
    ∀ (f : W→V) (g : Z→U),(∀ x,f x∈I)→(∀ u,g u∈J)→
    rawMarkedRestrictPair f g (rawMarkedDeleteRims σ (markedSampleArcSetGraph P π d σ A).edgeFinset)=
      rawMarkedRestrictPair f g σ ∧
    (fun b x u=>markedDeletePhysicalSpokes H (markedFiniteSpokeGraph S) b (f x) (g u))=
      (fun b x u=>H b (f x) (g u)) := by
  intro E K A S I J hEmpty f g hf hg
  obtain ⟨hR,hS⟩ := marked_removed_resources_empty_inner P π d σ A S I J hEmpty
  have hr : (markedSampleArcSetGraph P π d σ A).comap f=⊥ := by
    ext x y
    exact iff_false_intro (hR (f x) (hf x) (f y) (hf y))
  constructor
  · rw [rawMarkedRestrictPair_deleteRims,SimpleGraph.edgeFinset_eq_empty.mpr hr,rawMarkedDeleteRims_empty]
  · funext b x u
    simp only [markedDeletePhysicalSpokes,hS (f x) (hf x) (g u) (hg u),not_false_eq_true,and_true]

end Oberwolfach

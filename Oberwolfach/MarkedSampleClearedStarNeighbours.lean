module

public import Oberwolfach.MarkedFiniteResourceOperations
public import Oberwolfach.MarkedSampleDeletionIncidences
public import Oberwolfach.MarkedReservedStarClearing

@[expose] public section

/-! The exact cleared finite resource star supplies the actual neighbour
support conditions in the raw sample after physical deletion. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 24000000
set_option maxRecDepth 4096
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_sample_cleared_star_neighbours
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (σ:RawMarkedOutcome V U Γ Color)
    (H:Bool→V→U→Prop) (DR:SimpleGraph V) (DS:SimpleGraph (V⊕U))
    (I T:Finset V) (J W:Finset U) (hTI:T⊆I) (hWJ:W⊆J)
    (hI:∀ x,π x∈I↔x∈I) (hT:∀ x,π x∈T↔x∈T):
    let E₀:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let E₁:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    let A:=Finset.univ.filter (fun a:E₀⊕E₁=>
      Sum.elim (fun e=>s(e.val.1,e.val.2)) (fun e=>s(e.val.1,π e.val.2)) a∉DR.edgeFinset)
    let S:=Finset.univ.filter (fun z:V×U=>(H false z.1 z.2∨H true z.1 z.2)∧¬DS.Adj (Sum.inl z.1) (Sum.inr z.2))
    let R:=markedFiniteResources (fun e:E₀=>e.val.1) (fun e=>e.val.2)
      (fun e:E₁=>e.val.1) (fun e=>e.val.2) π A S
    (R.filter (markedInnerResource I J)).filter (markedStarResource T W)=∅→
    let σ':=rawMarkedDeleteRims σ DR.edgeFinset
    let H':=markedDeletePhysicalSpokes H DS
    let E₀':=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) false
    let E₁':=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) true
    let src':=Sum.elim (fun e:E₀'=>e.val.1) (fun e:E₁'=>e.val.1)
    let dst':=Sum.elim (fun e:E₀'=>e.val.2) (fun e:E₁'=>e.val.2)
    (∀ a:E₀'⊕E₁',dst' a∈T→src' a∉I) ∧
    (∀ a:E₀'⊕E₁',src' a∈T→dst' a∉I) ∧
    (∀ x∈T,∀ u,H' false x u∨H' true x u→u∉J) ∧
    (∀ u∈W,∀ x,H' false x u∨H' true x u→x∉I):=by
  intro E₀ E₁ A S R hclear
  dsimp only
  apply marked_cleared_star_neighbours
    (fun e:MarkedSampleArc P π (3*d) (fun e=>rawMarkedDeleteRims σ DR.edgeFinset (Sum.inl e)) false=>e.val.1)
    (fun e=>e.val.2)
    (fun e:MarkedSampleArc P π (3*d) (fun e=>rawMarkedDeleteRims σ DR.edgeFinset (Sum.inl e)) true=>e.val.1)
    (fun e=>e.val.2) π (markedDeletePhysicalSpokes H DS false) (markedDeletePhysicalSpokes H DS true)
    R I T J W hTI hWJ hI hT ?_ ?_ hclear
  · intro a
    let a':E₀⊕E₁:=markedSampleDeletedArcsEmbedding P π d σ DR.edgeFinset a
    have ha:a'∈A:=by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,?_⟩
      cases a with
      | inl a=>exact ((markedPhysicalRim_delete_iff P π d σ DR.edgeFinset false _ _).mp a.property).2
      | inr a=>exact ((markedPhysicalRim_delete_iff P π d σ DR.edgeFinset true _ _).mp a.property).2
    have hh:Sum.inl (markedPhysicalEdge (fun e:E₀=>e.val.1) (fun e=>e.val.2)
        (fun e:E₁=>e.val.1) (fun e=>e.val.2) π a')∈R:=
      (markedFiniteResources_rim _ _ _ _ π (markedSampleArc_physical_injective P π (3*d) _) A S a').mpr ha
    cases a <;> exact hh
  · intro x u hu
    apply (markedFiniteResources_spoke _ _ _ _ π A S (x,u)).mpr
    simp only [S,Finset.mem_filter,Finset.mem_univ,true_and]
    rcases hu with hu|hu
    · exact ⟨Or.inl hu.1,hu.2⟩
    · exact ⟨Or.inr hu.1,hu.2⟩

end Oberwolfach

module

public import Oberwolfach.MarkedReservedInnerArcSetLift
public import Oberwolfach.MarkedFiniteResourceOperations

@[expose] public section
/-! Lift arbitrary inner prescribed arcs without changing their exact
physical resources; the same spoke set is retained. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]
theorem marked_reserved_inner_resources_lift
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (σ:RawMarkedOutcome V U Γ Color)
    (C:Finset (Finset V⊕(V×U))) (I:Finset V) (J:Finset U)
    (hI:∀ x,π x∈I↔x∈I) (hC:∀ e∈C,¬markedInnerResource I J e):
    let E:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let K:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    let tail:=fun e:E=>e.val.1
    let head:=fun e:E=>e.val.2
    let ktail:=fun e:K=>e.val.1
    let khead:=fun e:K=>e.val.2
    let DR:=physicalEdgeGraph (markedReservedRimPairs C)
    let σ':=rawMarkedDeleteRims σ DR.edgeFinset
    let E':=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) false
    let K':=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) true
    let emb:=markedSampleDeletedArcsEmbedding P π d σ DR.edgeFinset;
    ∀ (A:Finset (E⊕K)) (S:Finset (V×U)),
    (∀ a∈A,Sum.elim tail ktail a∈I∧Sum.elim head khead a∈I)→
    let A':=Finset.univ.filter (fun a:E'⊕K'=>emb a∈A);
    A'.image emb=A ∧ A'.card=A.card ∧
    markedFiniteResources (fun e:E'=>e.val.1) (fun e=>e.val.2)
      (fun e:K'=>e.val.1) (fun e=>e.val.2) π A' S =
      markedFiniteResources tail head ktail khead π A S :=by
  intro E K tail head ktail khead DR σ' E' K' emb A S hA A'
  have hlift:=marked_reserved_inner_arc_set_lift P π d σ C I J hI hC A hA
  refine ⟨hlift.1,hlift.2,?_⟩
  unfold markedFiniteResources
  congr 1
  rw [←hlift.1,Finset.image_image]
  apply Finset.image_congr
  intro a _
  cases a <;> rfl
end Oberwolfach

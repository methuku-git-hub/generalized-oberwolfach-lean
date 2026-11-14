module

public import Oberwolfach.MarkedOutsideBalanceArcPullback
public import Oberwolfach.MarkedOutsideBalanceSpokeTypes
public import Oberwolfach.MarkedSampleDeletionIncidences

@[expose] public section

/-! The exact outside balances on surviving original occurrences give the
outside balances of the actual physically deleted sample. The spoke type
is changed only by intersecting it with the same undeleted edge set. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_deleted_sample_outside_balance
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ) (σ:RawMarkedOutcome V U Γ Color)
    (H:Bool→V→U→Prop) (DR:SimpleGraph V) (DS:SimpleGraph (V⊕U))
    (X:Finset V) (Z:Finset U):
    let E₀:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let E₁:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    let A:=Finset.univ.filter (fun a:E₀⊕E₁=>
      Sum.elim (fun e=>s(e.val.1,e.val.2)) (fun e=>s(e.val.1,π e.val.2)) a∉DR.edgeFinset)
    let S:=Finset.univ.filter (fun z:V×U=>(H false z.1 z.2∨H true z.1 z.2)∧¬DS.Adj (Sum.inl z.1) (Sum.inr z.2))
    MarkedOutsideBalance (fun e:E₀=>e.val.1) (fun e=>e.val.2)
      (fun e:E₁=>e.val.1) (fun e=>e.val.2) (H true) A S m X Z→
    let σ':=rawMarkedDeleteRims σ DR.edgeFinset
    let H':=markedDeletePhysicalSpokes H DS
    let E₀':=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) false
    let E₁':=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) true
    MarkedOutsideBalance (fun e:E₀'=>e.val.1) (fun e=>e.val.2)
      (fun e:E₁'=>e.val.1) (fun e=>e.val.2) (H' true) Finset.univ
      (Finset.univ.filter (fun z:V×U=>H' false z.1 z.2∨H' true z.1 z.2)) m X Z:=by
  intro E₀ E₁ A S h
  let e:=(markedSampleDeletedArcEquiv P π d σ DR.edgeFinset false).toEmbedding.trans (Function.Embedding.subtype _)
  let k:=(markedSampleDeletedArcEquiv P π d σ DR.edgeFinset true).toEmbedding.trans (Function.Embedding.subtype _)
  have hr:Finset.univ.image (e.sumMap k)=A:=markedSampleDeletedArcsEmbedding_range P π d σ DR.edgeFinset
  have h':MarkedOutsideBalance
      (fun a:MarkedSampleArc P π (3*d) (fun e=>rawMarkedDeleteRims σ DR.edgeFinset (Sum.inl e)) false=>a.val.1) (fun a=>a.val.2)
      (fun a:MarkedSampleArc P π (3*d) (fun e=>rawMarkedDeleteRims σ DR.edgeFinset (Sum.inl e)) true=>a.val.1) (fun a=>a.val.2) (H true) Finset.univ S m X Z:=
    marked_outside_balance_arc_pullback _ _ _ _ _ _ _ _ _ e k
      (fun _=>rfl) (fun _=>rfl) (fun _=>rfl) (fun _=>rfl)
      Finset.univ S m X Z (by rw [hr];exact h)
  have ht:∀ z∈S,H true z.1 z.2↔markedDeletePhysicalSpokes H DS true z.1 z.2:=by
    intro z hz
    have hn:¬DS.Adj (Sum.inl z.1) (Sum.inr z.2):=(Finset.mem_filter.mp hz).2.2
    simp only [markedDeletePhysicalSpokes,hn,not_false_eq_true,and_true]
  have hs:Finset.univ.filter (fun z:V×U=>markedDeletePhysicalSpokes H DS false z.1 z.2∨
      markedDeletePhysicalSpokes H DS true z.1 z.2)=S:=by
    ext z
    simp only [S,markedDeletePhysicalSpokes,Finset.mem_filter,Finset.mem_univ,true_and]
    tauto
  dsimp only
  rw [hs]
  exact h'.congr_spoke_types Finset.univ S X Z ht

end Oberwolfach

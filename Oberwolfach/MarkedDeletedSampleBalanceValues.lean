module

public import Oberwolfach.MarkedFiniteDomainBalanceEmbedding
public import Oberwolfach.MarkedSampleDeletionIncidences

@[expose] public section

/-! Full and restricted balance values of an actual physically deleted
sample. The source occurrences are precisely the surviving original
occurrences, and the spoke type is unchanged on every surviving spoke. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_deleted_sample_balance_values
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ) (σ:RawMarkedOutcome V U Γ Color)
    (H:Bool→V→U→Prop) (DR:SimpleGraph V) (DS:SimpleGraph (V⊕U))
    (X:Finset V) (Z:Finset U):
    let E₀:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let E₁:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    let A:=Finset.univ.filter (fun a:E₀⊕E₁=>
      Sum.elim (fun e=>s(e.val.1,e.val.2)) (fun e=>s(e.val.1,π e.val.2)) a∉DR.edgeFinset)
    let S:=Finset.univ.filter (fun z:V×U=>(H false z.1 z.2∨H true z.1 z.2)∧¬DS.Adj (Sum.inl z.1) (Sum.inr z.2))
    let σ':=rawMarkedDeleteRims σ DR.edgeFinset
    let H':=markedDeletePhysicalSpokes H DS
    let E₀':=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) false
    let E₁':=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) true
    let S':=Finset.univ.filter (fun z:V×U=>H' false z.1 z.2∨H' true z.1 z.2)
    ∀ (z:V⊕U) (i:Fin 4),
    markedFiniteBalance (fun e:E₀'=>e.val.1) (fun e=>e.val.2)
      (fun e:E₁'=>e.val.1) (fun e=>e.val.2) (H' true) Finset.univ S' m z i=
    markedFiniteBalance (fun e:E₀=>e.val.1) (fun e=>e.val.2)
      (fun e:E₁=>e.val.1) (fun e=>e.val.2) (H true) A S m z i∧
    markedFiniteDomainBalance (fun e:E₀'=>e.val.1) (fun e=>e.val.2)
      (fun e:E₁'=>e.val.1) (fun e=>e.val.2) (H' true) Finset.univ S' m X Z z i=
    markedFiniteDomainBalance (fun e:E₀=>e.val.1) (fun e=>e.val.2)
      (fun e:E₁=>e.val.1) (fun e=>e.val.2) (H true) A S m X Z z i:=by
  intro E₀ E₁ A S σ' H' E₀' E₁' S' z i
  let e:=(markedSampleDeletedArcEquiv P π d σ DR.edgeFinset false).toEmbedding.trans (Function.Embedding.subtype _)
  let k:=(markedSampleDeletedArcEquiv P π d σ DR.edgeFinset true).toEmbedding.trans (Function.Embedding.subtype _)
  have hr:Finset.univ.image (e.sumMap k)=A:=markedSampleDeletedArcsEmbedding_range P π d σ DR.edgeFinset
  have ht:∀ s∈S',H true s.1 s.2↔H' true s.1 s.2:=by
    intro s hs
    have hn:¬DS.Adj (Sum.inl s.1) (Sum.inr s.2):=
      ((Finset.mem_filter.mp hs).2).elim And.right And.right
    simp only [H',markedDeletePhysicalSpokes,hn,not_false_eq_true,and_true]
  have hs:S'.image (Prod.map (Function.Embedding.refl V) (Function.Embedding.refl U))=S:=by
    have hh:Prod.map (Function.Embedding.refl V) (Function.Embedding.refl U)=id:=rfl
    rw [hh,Finset.image_id]
    ext s
    simp only [S',H',S,markedDeletePhysicalSpokes,Finset.mem_filter,Finset.mem_univ,true_and]
    tauto
  have hz:Sum.map (Function.Embedding.refl V) (Function.Embedding.refl U) z=z:=by cases z <;> rfl
  constructor
  · have hh:=markedFiniteBalance_embedding
      (fun a:E₀'=>a.val.1) (fun a=>a.val.2) (fun a:E₁'=>a.val.1) (fun a=>a.val.2)
      (fun a:E₀=>a.val.1) (fun a=>a.val.2) (fun a:E₁=>a.val.1) (fun a=>a.val.2)
      (H' true) (H true) (Function.Embedding.refl V) (Function.Embedding.refl U) e k
      (fun _=>rfl) (fun _=>rfl) (fun _=>rfl) (fun _=>rfl) Finset.univ S' m ht z i
    rw [hr,hs,hz] at hh
    exact hh.symm
  · have hh:=markedFiniteDomainBalance_embedding
      (fun a:E₀'=>a.val.1) (fun a=>a.val.2) (fun a:E₁'=>a.val.1) (fun a=>a.val.2)
      (fun a:E₀=>a.val.1) (fun a=>a.val.2) (fun a:E₁=>a.val.1) (fun a=>a.val.2)
      (H' true) (H true) (Function.Embedding.refl V) (Function.Embedding.refl U) e k
      (fun _=>rfl) (fun _=>rfl) (fun _=>rfl) (fun _=>rfl) Finset.univ S' m ht X Z X Z
      (fun _=>Iff.rfl) (fun _=>Iff.rfl) z i
    rw [hr,hs,hz] at hh
    exact hh.symm

end Oberwolfach

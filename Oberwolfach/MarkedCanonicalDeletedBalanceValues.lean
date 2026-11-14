module

public import Oberwolfach.MarkedDeletedSampleBalanceValues
public import Oberwolfach.MarkedFiniteDeletionDegrees

@[expose] public section

/-! The balance values in the actual canonical deleted sample equal those
of the exact original occurrence and spoke complements. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_canonical_deleted_balance_values
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ) (σ:RawMarkedOutcome V U Γ Color)
    (H:Bool→V→U→Prop):
    let E₀:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let E₁:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    let S:=Finset.univ.filter (fun s:V×U=>H false s.1 s.2∨H true s.1 s.2);
    ∀ (A:Finset (E₀⊕E₁)) (B:Finset (V×U)) (I:Finset V) (J:Finset U),
    let σ':=rawMarkedDeleteRims σ (markedSampleArcSetGraph P π d σ A).edgeFinset
    let H':=markedDeletePhysicalSpokes H (markedFiniteSpokeGraph B)
    let E₀':=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) false
    let E₁':=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) true
    let S':=Finset.univ.filter (fun s:V×U=>H' false s.1 s.2∨H' true s.1 s.2);
    ∀ (z:V⊕U) (i:Fin 4),
    markedFiniteBalance (fun e:E₀'=>e.val.1) (fun e=>e.val.2)
      (fun e:E₁'=>e.val.1) (fun e=>e.val.2) (H' true) Finset.univ S' m z i=
    markedFiniteBalance (fun e:E₀=>e.val.1) (fun e=>e.val.2)
      (fun e:E₁=>e.val.1) (fun e=>e.val.2) (H true) (Finset.univ\A) (S\B) m z i∧
    markedFiniteDomainBalance (fun e:E₀'=>e.val.1) (fun e=>e.val.2)
      (fun e:E₁'=>e.val.1) (fun e=>e.val.2) (H' true) Finset.univ S' m I J z i=
    markedFiniteDomainBalance (fun e:E₀=>e.val.1) (fun e=>e.val.2)
      (fun e:E₁=>e.val.1) (fun e=>e.val.2) (H true) (Finset.univ\A) (S\B) m I J z i:=by
  intro E₀ E₁ S A B I J σ' H' E₀' E₁' S' z i
  have hh:=marked_deleted_sample_balance_values P π d m σ H
    (markedSampleArcSetGraph P π d σ A) (markedFiniteSpokeGraph B) I J z i
  have hs:Finset.univ.filter (fun s:V×U=>(H false s.1 s.2∨H true s.1 s.2)∧
      ¬(markedFiniteSpokeGraph B).Adj (Sum.inl s.1) (Sum.inr s.2))=S\B:=by
    ext s
    simp only [S,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_sdiff,markedFiniteSpokeGraph_adj]
  rw [markedSampleArcSetGraph_remaining,hs] at hh
  exact hh

end Oberwolfach

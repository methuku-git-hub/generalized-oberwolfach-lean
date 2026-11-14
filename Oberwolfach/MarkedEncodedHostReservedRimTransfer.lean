module

public import Oberwolfach.MarkedRawHostArcEquivalences

@[expose] public section

/-! Typed inclusion of a fixed reservoir in a later explicit host yields
exactly the arc-transfer inputs for the encoded-host completion. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K E₀ K₀ Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_encoded_host_preserves_reserved_rims
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ)
    (tail head:E→V) (ktail khead:K→V)
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (hE:∀ e,¬PermutationClose π (3*d) (tail e) (head e)∧P.Adj (tail e) (head e))
    (hK:∀ e,¬PermutationClose π (3*d) (ktail e) (khead e)∧P.Adj (ktail e) (π (khead e)))
    (σ:RawMarkedOutcome V U Γ Color) (I:Finset V) (hI:∀ v,π v∈I↔v∈I)
    (hAgree:∀ mark x y,x∈I→y∈I→
      (markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) mark x y=1 ↔
        (if mark then ∃ e:K,ktail e=x∧khead e=y else ∃ e:E,tail e=x∧head e=y)))
    (tail₀ head₀:E₀→V) (ktail₀ khead₀:K₀→V) (C:Finset (Finset V⊕(V×U)))
    (hOrd:∀ e:E₀,Sum.inl ({tail₀ e,head₀ e}:Finset V)∈C→∃ a:E,tail a=tail₀ e∧head a=head₀ e)
    (hMark:∀ e:K₀,Sum.inl ({ktail₀ e,π (khead₀ e)}:Finset V)∈C→∃ a:K,ktail a=ktail₀ e∧khead a=khead₀ e):
    let τ:=rawMarkedEncodeHost tail head ktail khead π σ I;
    (∀ e:E₀,Sum.inl ({tail₀ e,head₀ e}:Finset V)∈C→
      ∃ a:MarkedSampleArc P π (3*d) (fun f=>τ (Sum.inl f)) false,a.val.1=tail₀ e∧a.val.2=head₀ e) ∧
    (∀ e:K₀,Sum.inl ({ktail₀ e,π (khead₀ e)}:Finset V)∈C→
      ∃ a:MarkedSampleArc P π (3*d) (fun f=>τ (Sum.inl f)) true,a.val.1=ktail₀ e∧a.val.2=khead₀ e) := by
  intro τ
  constructor
  · intro e he
    obtain ⟨a,ht,hh⟩:=hOrd e he
    let a':=markedRawHostOrdinaryArcEquiv P π d tail head ktail khead hp hE hK σ I hI hAgree a
    exact ⟨a',ht,hh⟩
  · intro e he
    obtain ⟨a,ht,hh⟩:=hMark e he
    let a':=markedRawHostMarkedArcEquiv P π d tail head ktail khead hp hE hK σ I hI hAgree a
    exact ⟨a',ht,hh⟩
end Oberwolfach

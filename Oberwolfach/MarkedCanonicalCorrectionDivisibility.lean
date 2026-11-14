module

public import Oberwolfach.MarkedCanonicalDeletedBalanceValues

@[expose] public section
/-! Divisibility of a physically deleted sample transfers back to the
complement of the correction in the original typed occurrence sets. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_canonical_correction_original_divisible
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ) (σ:RawMarkedOutcome V U Γ Color)
    (H:Bool→V→U→Prop):
    let E:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let K:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    let S:=Finset.univ.filter (fun z:V×U=>H false z.1 z.2∨H true z.1 z.2);
    ∀ (FA:Finset (E⊕K)) (FS:Finset (V×U)),
    let σ':=rawMarkedDeleteRims σ (markedSampleArcSetGraph P π d σ FA).edgeFinset
    let H':=markedDeletePhysicalSpokes H (markedFiniteSpokeGraph FS)
    let E':=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) false
    let K':=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) true;
    MarkedRemainderDivisible (fun e:E'=>e.val.1) (fun e=>e.val.2) (fun e:K'=>e.val.1) (fun e=>e.val.2)
      (H' true) Finset.univ (Finset.univ.filter (fun z:V×U=>H' false z.1 z.2∨H' true z.1 z.2)) m →
    MarkedRemainderDivisible (fun e:E=>e.val.1) (fun e=>e.val.2) (fun e:K=>e.val.1) (fun e=>e.val.2)
      (H true) (Finset.univ\FA) (S\FS) m := by
  intro E K S FA FS σ' H' E' K' hdiv
  apply (markedFiniteBalance_eq_zero_iff _ _ _ _ _ _ _ _).mp
  intro z i
  rw [←(marked_canonical_deleted_balance_values P π d m σ H FA FS Finset.univ Finset.univ z i).1]
  exact (markedFiniteBalance_eq_zero_iff _ _ _ _ _ _ _ _).mpr hdiv z i
end Oberwolfach

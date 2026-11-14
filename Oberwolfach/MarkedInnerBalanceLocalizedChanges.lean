module

public import Oberwolfach.MarkedRestrictedBalanceArbitraryChanges
public import Oberwolfach.MarkedRestrictedBalanceOfFinite
public import Oberwolfach.MarkedRestrictedSampleBalance

@[expose] public section
/-! Transfer the finite inner balance using changes restricted to the actual
opposite domains, rather than ambient change-graph degrees. The three local
change bounds remain explicit and must be proved for the selected correction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_inner_balance_with_localized_changes
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ) (A:Finset V) (B:Finset U)
    (η δR δS:ℝ) (hη:0≤η) (hR0:0≤δR) (hS0:0≤δS)
    (σ τ:RawMarkedOutcome V U Γ Color) (H H':Bool→V→U→Prop)
    (hTypes:∀v u,¬(H false v u∧H true v u))
    (hTypes':∀v u,¬(H' false v u∧H' true v u))
    (hR:∀mark incoming v,
      |(markedRestrictedDegree P π (3*d) (fun e=>τ (Sum.inl e)) mark incoming v A:ℝ)-
        (markedRestrictedDegree P π (3*d) (fun e=>σ (Sum.inl e)) mark incoming v A:ℝ)|≤δR)
    (hrow:∀b v,(∑u∈B,if ¬(H b v u↔H' b v u) then (1:ℝ) else 0)≤δS)
    (hcol:∀b u,(∑v∈A,if ¬(H b v u↔H' b v u) then (1:ℝ) else 0)≤δS):
    let E:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let K:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    let S:=Finset.univ.filter (fun s:V×U=>H false s.1 s.2∨H true s.1 s.2)
    let E':=MarkedSampleArc P π (3*d) (fun e=>τ (Sum.inl e)) false
    let K':=MarkedSampleArc P π (3*d) (fun e=>τ (Sum.inl e)) true
    let S':=Finset.univ.filter (fun s:V×U=>H' false s.1 s.2∨H' true s.1 s.2);
    (∀z i,|markedFiniteDomainBalance (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) (H true) Finset.univ S m A B z i|≤η)→
    ∀z i,|markedFiniteDomainBalance (fun e:E'=>e.val.1) (fun e=>e.val.2)
      (fun e:K'=>e.val.1) (fun e=>e.val.2) (H' true) Finset.univ S' m A B z i|≤η+2*δR+(m+2:ℕ)*δS :=by
  intro E K S E' K' S' hfinite
  have hbal:=marked_restricted_balance_of_finite_balance P π d m σ H hTypes A B η hfinite
  have hnew:=marked_restricted_balance_after_arbitrary_changes P π d m A B η δR δS hR0 hS0 σ τ H H' hbal hR hrow hcol
  exact marked_restricted_sample_balance P π d m τ H' hTypes' A B _ (by positivity) hnew
end Oberwolfach

module

public import Oberwolfach.MarkedRestrictedBalancePhysicalChanges
public import Oberwolfach.MarkedRestrictedSampleBalance

@[expose] public section
/-! Convert the stability estimate to the finite balance values used by
cover-down, for every root including those outside the restricted sets. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_finite_balance_after_physical_changes
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ) (A:Finset V) (B:Finset U)
    (η δR δS:ℝ) (hη:0≤η) (hR0:0≤δR) (hS0:0≤δS)
    (σ τ:RawMarkedOutcome V U Γ Color) (H H':Bool→V→U→Prop)
    (FR:SimpleGraph V) (FS:SimpleGraph (V⊕U))
    (hbal:MarkedRestrictedBalanceWithSpokes P π d m A B η σ H)
    (htypes:∀ v u,¬(H' false v u∧H' true v u))
    (hR:∀ a,¬(rawMarkedPairRims P π d σ a↔rawMarkedPairRims P π d τ a)→markedPairPhysical π a∈FR.edgeFinset)
    (hS:∀ b v u,¬(H b v u↔H' b v u)→FS.Adj (Sum.inl v) (Sum.inr u))
    (hFR:∀ v,(FR.degree v:ℝ)≤δR) (hFS:∀ z,(FS.degree z:ℝ)≤δS):
    let E:=MarkedSampleArc P π (3*d) (fun e=>τ (Sum.inl e)) false
    let K:=MarkedSampleArc P π (3*d) (fun e=>τ (Sum.inl e)) true
    let S:=Finset.univ.filter (fun s:V×U=>H' false s.1 s.2∨H' true s.1 s.2);
    ∀ z i,|markedFiniteDomainBalance (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) (H' true) Finset.univ S m A B z i|≤η+2*δR+(m+2:ℕ)*δS := by
  have hb:=marked_restricted_balance_after_physical_changes P π d m A B η δR δS hR0 hS0 σ τ H H' FR FS hbal hR hS hFR hFS
  have he:0≤η+2*δR+(m+2:ℕ)*δS:=by positivity
  exact marked_restricted_sample_balance P π d m τ H' htypes A B _ he hb
end Oberwolfach

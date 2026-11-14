module

public import Oberwolfach.MarkedFiniteBalanceUniformPerturbation
public import Oberwolfach.MarkedSampleBalanceErrorBudgets

@[expose] public section
/-! Apply the physical-change balance transfer directly to the sampled
fixed-domain balance error, without changing its normalization. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_sample_balance_uniform_physical_changes
    (m:ℕ) (etaBal x iota:ℝ) (hη:0<etaBal) (hx:0<x) (hi:0 < iota):
    ∃ ζcap:ℝ,0<ζcap ∧ ∀ ζ:ℝ,0≤ζ→ζ≤ζcap→
    ∀ (V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [DecidableEq U],
    ∀ (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (A:Finset V) (B:Finset U)
      (epsBal ζBal:ℝ) (σ τ:RawMarkedOutcome V U Γ Color) (H H':Bool→V→U→Prop)
      (FR:SimpleGraph V) (FS:SimpleGraph (V⊕U)),
    0≤epsBal → 0≤ζBal →
    epsBal+(m+2:ℕ)*ζBal≤etaBal/2 → epsBal+(m+2:ℕ)*ζBal≤x/4 →
    iota*Fintype.card V≤(A.card:ℝ) →
    (∀ v u,¬(H false v u∧H true v u)) →
    (∀ v u,¬(H' false v u∧H' true v u)) →
    (∀ a,¬(rawMarkedPairRims P π d σ a↔rawMarkedPairRims P π d τ a)→markedPairPhysical π a∈FR.edgeFinset) →
    (∀ b v u,¬(H b v u↔H' b v u)→FS.Adj (Sum.inl v) (Sum.inr u)) →
    (∀ v,(FR.degree v:ℝ)≤ζ*Fintype.card V) →
    (∀ z,(FS.degree z:ℝ)≤ζ*Fintype.card V) →
    let E:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let K:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    let S:=Finset.univ.filter (fun s:V×U=>H false s.1 s.2∨H true s.1 s.2)
    let E':=MarkedSampleArc P π (3*d) (fun e=>τ (Sum.inl e)) false
    let K':=MarkedSampleArc P π (3*d) (fun e=>τ (Sum.inl e)) true
    let S':=Finset.univ.filter (fun s:V×U=>H' false s.1 s.2∨H' true s.1 s.2)
    let initialErr:=(epsBal+(m+2:ℕ)*ζBal)*A.card
    let err:=initialErr+(m+4:ℕ)*ζ*Fintype.card V;
    (∀ z i,|markedFiniteDomainBalance (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) (H true) Finset.univ S m A B z i| ≤ initialErr) →
    0≤err ∧ err≤etaBal*A.card ∧ err≤(x/2)*Fintype.card V ∧
    ∀ z i,|markedFiniteDomainBalance (fun e:E'=>e.val.1) (fun e=>e.val.2)
      (fun e:K'=>e.val.1) (fun e=>e.val.2) (H' true) Finset.univ S' m A B z i|≤err := by
  obtain ⟨ζcap,hcap,hcover⟩:=marked_finite_balance_uniform_perturbation m etaBal x iota hη hx hi
  refine ⟨ζcap,hcap,?_⟩
  intro ζ hζ hζcap V U Γ Color _ _ _ _ _ _ P π d A B epsBal ζBal σ τ H H' FR FS
    he hz hlocal hambient hA hH hH' hR hS hFR hFS E K S E' K' S' initialErr err hfinite
  have hM:(0:ℝ)≤A.card:=Nat.cast_nonneg _
  have hMn:(A.card:ℝ)≤Fintype.card V:=by exact_mod_cast Finset.card_le_univ A
  obtain ⟨hzero,hb1,hb2⟩:=marked_sample_balance_error_budgets m epsBal ζBal etaBal x (Fintype.card V) A.card
    he hz hM hMn hlocal hambient
  exact hcover ζ hζ hζcap V U Γ Color P π d A B initialErr σ τ H H' FR FS
    hzero hA hb1 hb2 hH hH' hR hS hFR hFS hfinite
end Oberwolfach

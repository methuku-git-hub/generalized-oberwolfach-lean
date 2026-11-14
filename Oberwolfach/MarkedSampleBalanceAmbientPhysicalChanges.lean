module

public import Oberwolfach.MarkedFiniteBalanceAmbientPerturbation
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

theorem marked_sample_balance_ambient_physical_changes
    (m:ℕ) (x:ℝ) (hx:0<x):
    ∃ ζcap:ℝ,0<ζcap ∧ ∀ ζ:ℝ,0≤ζ→ζ≤ζcap→
    ∀ (V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [DecidableEq U],
    ∀ (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (A:Finset V) (B:Finset U)
      (epsBal ζBal:ℝ) (σ τ:RawMarkedOutcome V U Γ Color) (H H':Bool→V→U→Prop)
      (FR:SimpleGraph V) (FS:SimpleGraph (V⊕U)),
    0≤epsBal → 0≤ζBal →
    epsBal+(m+2:ℕ)*ζBal≤x/4 →
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
    0≤err ∧ err≤(x/2)*Fintype.card V ∧
    ∀ z i,|markedFiniteDomainBalance (fun e:E'=>e.val.1) (fun e=>e.val.2)
      (fun e:K'=>e.val.1) (fun e=>e.val.2) (H' true) Finset.univ S' m A B z i|≤err := by
  obtain ⟨ζcap,hcap,hcover⟩:=marked_finite_balance_ambient_perturbation m x hx
  refine ⟨ζcap,hcap,?_⟩
  intro ζ hζ hζcap V U Γ Color _ _ _ _ _ _ P π d A B epsBal ζBal σ τ H H' FR FS
    he hz hambient hH hH' hR hS hFR hFS E K S E' K' S' initialErr err hfinite
  have hM:(0:ℝ)≤A.card:=Nat.cast_nonneg _
  have hMn:(A.card:ℝ)≤Fintype.card V:=by exact_mod_cast Finset.card_le_univ A
  have hcoef:0≤epsBal+(m+2:ℕ)*ζBal:=by positivity
  have hx0:0≤x/4:=by positivity
  have hzero:0 ≤ initialErr:=mul_nonneg hcoef hM
  have hb:initialErr ≤ (x/4)*Fintype.card V:=
    (mul_le_mul_of_nonneg_right hambient hM).trans (mul_le_mul_of_nonneg_left hMn hx0)
  exact hcover ζ hζ hζcap V U Γ Color P π d A B initialErr σ τ H H' FR FS
    hzero hb hH hH' hR hS hFR hFS hfinite
end Oberwolfach

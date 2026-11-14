module

public import Oberwolfach.MarkedFiniteBalanceTransferPhysicalChanges

@[expose] public section
/-! Uniform ambient-order balance control does not require a lower bound
on the size of either fixed domain. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_finite_balance_ambient_perturbation
    (m:ℕ) (x:ℝ) (hx:0<x):
    ∃ ζcap:ℝ,0<ζcap ∧ ∀ ζ:ℝ,0≤ζ→ζ≤ζcap→
    ∀ (V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [DecidableEq U],
    ∀ (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (A:Finset V) (B:Finset U)
      (η:ℝ) (σ τ:RawMarkedOutcome V U Γ Color) (H H':Bool→V→U→Prop)
      (FR:SimpleGraph V) (FS:SimpleGraph (V⊕U)),
    0≤η → η≤(x/4)*Fintype.card V →
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
    let err:=η+(m+4:ℕ)*ζ*Fintype.card V;
    (∀ z i,|markedFiniteDomainBalance (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) (H true) Finset.univ S m A B z i|≤η) →
    0≤err ∧ err≤(x/2)*Fintype.card V ∧
    ∀ z i,|markedFiniteDomainBalance (fun e:E'=>e.val.1) (fun e=>e.val.2)
      (fun e:K'=>e.val.1) (fun e=>e.val.2) (H' true) Finset.univ S' m A B z i|≤err := by
  let ζcap:=x/(4*((m:ℝ)+5))
  have hcap:0<ζcap:=by dsimp [ζcap];positivity
  refine ⟨ζcap,hcap,?_⟩
  intro ζ hζ hζcap V U Γ Color _ _ _ _ _ _ P π d A B η σ τ H H' FR FS hη0 hηN hH hH' hR hS hFR hFS
    E K S E' K' S' err hfinite
  have hn:(0:ℝ)≤Fintype.card V:=Nat.cast_nonneg _
  have hδ:0≤ζ*Fintype.card V:=mul_nonneg hζ hn
  have hcap':ζ*(4*((m:ℝ)+5))≤x:=(le_div_iff₀ (by positivity)).mp hζcap
  have hchange:=marked_finite_balance_transfer_after_physical_changes P π d m A B η
    (ζ*Fintype.card V) (ζ*Fintype.card V) hη0 hδ hδ σ τ H H' FR FS hH hH' hR hS hFR hFS hfinite
  have hbound:err≤(x/2)*Fintype.card V:=by
    dsimp [err]
    push_cast
    nlinarith [mul_le_mul_of_nonneg_right hcap' hn]
  refine ⟨by dsimp [err];positivity,hbound,?_⟩
  intro z i
  have hh:=hchange z i
  convert hh using 1 <;> dsimp [err] <;> push_cast <;> ring
end Oberwolfach

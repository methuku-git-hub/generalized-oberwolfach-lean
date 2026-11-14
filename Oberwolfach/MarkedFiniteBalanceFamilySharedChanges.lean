module

public import Oberwolfach.MarkedFiniteBalanceUniformPerturbation

@[expose] public section
/-! All original inner and deeper balance tests survive the same physical
change graphs under one uniformly chosen error allowance. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_finite_balance_family_shared_changes
    (m:ℕ) (etaBal x iota:ℝ) (hη:0<etaBal) (hx:0<x) (hi:0 < iota):
    ∃ζcap:ℝ,0<ζcap ∧ ∀ζ:ℝ,0≤ζ→ζ≤ζcap→
    ∀ (V U Γ Color I:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [DecidableEq U],
    ∀ (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ)
      (σ τ:RawMarkedOutcome V U Γ Color) (H H':Bool→V→U→Prop)
      (FR:SimpleGraph V) (FS:SimpleGraph (V⊕U)) (A:I→Finset V) (B:I→Finset U) (η:I→ℝ),
    (∀i,0≤η i)→(∀i,iota*Fintype.card V≤((A i).card:ℝ))→
    (∀i,η i≤(etaBal/2)*(A i).card)→(∀i,η i≤(x/4)*Fintype.card V)→
    (∀v u,¬(H false v u∧H true v u))→(∀v u,¬(H' false v u∧H' true v u))→
    (∀a,¬(rawMarkedPairRims P π d σ a↔rawMarkedPairRims P π d τ a)→markedPairPhysical π a∈FR.edgeFinset)→
    (∀b v u,¬(H b v u↔H' b v u)→FS.Adj (Sum.inl v) (Sum.inr u))→
    (∀v,(FR.degree v:ℝ)≤ζ*Fintype.card V)→(∀z,(FS.degree z:ℝ)≤ζ*Fintype.card V)→
    let E:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let K:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    let S:=Finset.univ.filter (fun s:V×U=>H false s.1 s.2∨H true s.1 s.2)
    let E':=MarkedSampleArc P π (3*d) (fun e=>τ (Sum.inl e)) false
    let K':=MarkedSampleArc P π (3*d) (fun e=>τ (Sum.inl e)) true
    let S':=Finset.univ.filter (fun s:V×U=>H' false s.1 s.2∨H' true s.1 s.2)
    let err:=fun i=>η i+(m+4:ℕ)*ζ*Fintype.card V;
    (∀i z k,|markedFiniteDomainBalance (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) (H true) Finset.univ S m (A i) (B i) z k|≤η i)→
    ∀i,0≤err i ∧ err i≤etaBal*(A i).card ∧ err i≤(x/2)*Fintype.card V ∧
      ∀z k,|markedFiniteDomainBalance (fun e:E'=>e.val.1) (fun e=>e.val.2)
        (fun e:K'=>e.val.1) (fun e=>e.val.2) (H' true) Finset.univ S' m (A i) (B i) z k|≤err i:=by
  obtain ⟨ζcap,hcap,htransfer⟩:=marked_finite_balance_uniform_perturbation m etaBal x iota hη hx hi
  refine ⟨ζcap,hcap,?_⟩
  intro ζ hζ hζcap V U Γ Color I _ _ _ _ _ _ P π d σ τ H H' FR FS A B η hη0 hA hηA hηN hH hH' hR hS hFR hFS E K S E' K' S' err hfinite i
  exact htransfer ζ hζ hζcap V U Γ Color P π d (A i) (B i) (η i) σ τ H H' FR FS
    (hη0 i) (hA i) (hηA i) (hηN i) hH hH' hR hS hFR hFS (hfinite i)
end Oberwolfach

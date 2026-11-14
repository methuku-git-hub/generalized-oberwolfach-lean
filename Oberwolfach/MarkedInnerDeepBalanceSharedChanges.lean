module

public import Oberwolfach.MarkedFiniteBalanceUniformPerturbation

@[expose] public section
/-! Transfer inner and deeper balance with the same physical changes. The
relative error is needed only for the inner set; the deeper set uses the
ambient error allowance and need not have a positive relative size. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_inner_deep_balance_shared_changes
    (m:ℕ) (etaBal x iota:ℝ) (hη:0<etaBal) (hx:0<x) (hi:0 < iota):
    ∃cap:ℝ,0<cap ∧ ∀ζ:ℝ,0≤ζ→ζ≤cap→
    ∀ (V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [DecidableEq U],
    ∀ (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ)
      (I T:Finset V) (J R:Finset U) (errI errT:ℝ)
      (σ τ:RawMarkedOutcome V U Γ Color) (H H':Bool→V→U→Prop)
      (FR:SimpleGraph V) (FS:SimpleGraph (V⊕U)),
    0≤errI→0≤errT→iota*Fintype.card V≤(I.card:ℝ)→
    errI≤(etaBal/2)*I.card→errI≤(x/4)*Fintype.card V→errT≤(x/4)*Fintype.card V→
    (∀v u,¬(H false v u∧H true v u))→(∀v u,¬(H' false v u∧H' true v u))→
    (∀a,¬(rawMarkedPairRims P π d σ a↔rawMarkedPairRims P π d τ a)→markedPairPhysical π a∈FR.edgeFinset)→
    (∀b v u,¬(H b v u↔H' b v u)→FS.Adj (Sum.inl v) (Sum.inr u))→
    (∀v,(FR.degree v:ℝ)≤ζ*Fintype.card V)→(∀z,(FS.degree z:ℝ)≤ζ*Fintype.card V)→
    let E:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let K:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    let S:=Finset.univ.filter (fun z:V×U=>H false z.1 z.2∨H true z.1 z.2)
    let E':=MarkedSampleArc P π (3*d) (fun e=>τ (Sum.inl e)) false
    let K':=MarkedSampleArc P π (3*d) (fun e=>τ (Sum.inl e)) true
    let S':=Finset.univ.filter (fun z:V×U=>H' false z.1 z.2∨H' true z.1 z.2);
    (∀v j,|markedFiniteDomainBalance (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) (H true) Finset.univ S m I J v j|≤errI)→
    (∀v j,|markedFiniteDomainBalance (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) (H true) Finset.univ S m T R v j|≤errT)→
    ∃eI eT:ℝ,0≤eI ∧ 0≤eT ∧ eI≤(x/2)*Fintype.card V ∧ eT≤(x/2)*Fintype.card V ∧
      eI≤etaBal*I.card ∧
      (∀v j,|markedFiniteDomainBalance (fun e:E'=>e.val.1) (fun e=>e.val.2)
        (fun e:K'=>e.val.1) (fun e=>e.val.2) (H' true) Finset.univ S' m I J v j|≤eI) ∧
      (∀v j,|markedFiniteDomainBalance (fun e:E'=>e.val.1) (fun e=>e.val.2)
        (fun e:K'=>e.val.1) (fun e=>e.val.2) (H' true) Finset.univ S' m T R v j|≤eT) := by
  obtain ⟨c,hc,hinner⟩:=marked_finite_balance_uniform_perturbation m etaBal x iota hη hx hi
  let cap:=min c (x/(4*((m:ℝ)+4)))
  have hm:0<(m:ℝ)+4:=by positivity
  have hcap:0<cap:=lt_min hc (div_pos hx (by positivity))
  refine ⟨cap,hcap,?_⟩
  intro ζ hζ hζcap V U Γ Color _ _ _ _ _ _ P π d I T J R errI errT σ τ H H' FR FS
    hI0 hT0 hsize hIrel hIambient hTambient hH hH' hR hS hFR hFS E K S E' K' S' hI hT
  have hn:0≤(Fintype.card V:ℝ):=Nat.cast_nonneg _
  have hδ:0≤ζ*Fintype.card V:=mul_nonneg hζ hn
  have hInner:=hinner ζ hζ (hζcap.trans (min_le_left _ _)) V U Γ Color P π d I J errI σ τ H H' FR FS
    hI0 hsize hIrel hIambient hH hH' hR hS hFR hFS hI
  have hDeep:=marked_finite_balance_transfer_after_physical_changes P π d m T R errT
    (ζ*Fintype.card V) (ζ*Fintype.card V) hT0 hδ hδ σ τ H H' FR FS hH hH' hR hS hFR hFS hT
  have hζbound:ζ≤x/(4*((m:ℝ)+4)):=hζcap.trans (min_le_right _ _)
  have hmul:ζ*(4*((m:ℝ)+4))≤x:=(le_div_iff₀ (by positivity)).mp hζbound
  have hmuln:=mul_le_mul_of_nonneg_right hmul hn
  let eI:=errI+(m+4:ℕ)*ζ*Fintype.card V
  let eT:=errT+(m+4:ℕ)*ζ*Fintype.card V
  have heT:eT≤(x/2)*Fintype.card V:=by
    dsimp [eT]; push_cast; nlinarith
  refine ⟨eI,eT,hInner.1,?_,hInner.2.2.1,heT,hInner.2.1,hInner.2.2.2,?_⟩
  · dsimp [eT]; positivity
  · intro v j
    have hh:=hDeep v j
    convert hh using 1 <;> dsimp [eT] <;> push_cast <;> ring
end Oberwolfach

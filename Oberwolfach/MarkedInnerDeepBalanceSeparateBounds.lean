module

public import Oberwolfach.MarkedInnerDeepBalanceSharedChanges

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

theorem marked_inner_deep_balance_from_separate_bounds
    (m:ℕ) (etaBal x iota:ℝ) (hη:0<etaBal) (hx:0<x) (hi:0 < iota):
    ∃cap:ℝ,0<cap ∧ ∀ζ:ℝ,0≤ζ→ζ≤cap→
    ∀ (V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [DecidableEq U],
    ∀ (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ)
      (I T:Finset V) (J R:Finset U)
      (σ τ:RawMarkedOutcome V U Γ Color) (H H':Bool→V→U→Prop)
      (FR:SimpleGraph V) (FS:SimpleGraph (V⊕U)),
    iota*Fintype.card V≤(I.card:ℝ)→
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
      (fun e:K=>e.val.1) (fun e=>e.val.2) (H true) Finset.univ S m I J v j|≤(x/4)*Fintype.card V)→
    (∀v j,|markedFiniteDomainBalance (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) (H true) Finset.univ S m I J v j|≤(etaBal/2)*I.card)→
    (∀v j,|markedFiniteDomainBalance (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) (H true) Finset.univ S m T R v j|≤(x/4)*Fintype.card V)→
    ∃eI eT:ℝ,0≤eI ∧ 0≤eT ∧ eI≤(x/2)*Fintype.card V ∧ eT≤(x/2)*Fintype.card V ∧
      eI≤etaBal*I.card ∧
      (∀v j,|markedFiniteDomainBalance (fun e:E'=>e.val.1) (fun e=>e.val.2)
        (fun e:K'=>e.val.1) (fun e=>e.val.2) (H' true) Finset.univ S' m I J v j|≤eI) ∧
      (∀v j,|markedFiniteDomainBalance (fun e:E'=>e.val.1) (fun e=>e.val.2)
        (fun e:K'=>e.val.1) (fun e=>e.val.2) (H' true) Finset.univ S' m T R v j|≤eT) := by
  obtain ⟨cap,hcap,htransfer⟩:=marked_inner_deep_balance_shared_changes m etaBal x iota hη hx hi
  refine ⟨cap,hcap,?_⟩
  intro ζ hζ hζcap V U Γ Color _ _ _ _ _ _ P π d I T J R σ τ H H' FR FS
    hsize hH hH' hR hS hFR hFS E K S E' K' S' hI hIrel hT
  let eI:ℝ:=min ((x/4)*Fintype.card V) ((etaBal/2)*I.card)
  let eT:ℝ:=(x/4)*Fintype.card V
  have heI:0≤eI:=by dsimp [eI]; positivity
  have heT:0≤eT:=by dsimp [eT]; positivity
  have heIrel:eI≤(etaBal/2)*I.card:=min_le_right _ _
  have heIambient:eI≤(x/4)*Fintype.card V:=min_le_left _ _
  have hboth:∀v j,|markedFiniteDomainBalance (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) (H true) Finset.univ S m I J v j|≤eI:=by
    intro v j
    exact le_min (hI v j) (hIrel v j)
  exact htransfer ζ hζ hζcap V U Γ Color P π d I T J R eI eT σ τ H H' FR FS
    heI heT hsize heIrel heIambient (le_refl _) hH hH' hR hS hFR hFS hboth hT
end Oberwolfach

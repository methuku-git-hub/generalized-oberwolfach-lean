module

public import Oberwolfach.MarkedFiniteDomainBalance
public import Oberwolfach.MarkedSamplePhysicalDeletionLift
public import Oberwolfach.MarkedOutsideBalance

@[expose] public section

/-! Equal actual outcomes and equal spoke predicates have identical finite
balance values and outside-balance conditions. No change of sampling law or
of the physical representation is made. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_sample_finite_balance_congr
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ)
    (σ τ:RawMarkedOutcome V U Γ Color) (H J:Bool→V→U→Prop)
    (hσ:σ=τ) (hH:H=J) (X:Finset V) (Z:Finset U) (z:V⊕U) (i:Fin 4):
    let E:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let K:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    let E':=MarkedSampleArc P π (3*d) (fun e=>τ (Sum.inl e)) false
    let K':=MarkedSampleArc P π (3*d) (fun e=>τ (Sum.inl e)) true
    let S:=Finset.univ.filter (fun s:V×U=>H false s.1 s.2∨H true s.1 s.2)
    let S':=Finset.univ.filter (fun s:V×U=>J false s.1 s.2∨J true s.1 s.2);
    markedFiniteBalance (fun e:E=>e.val.1) (fun e=>e.val.2) (fun e:K=>e.val.1) (fun e=>e.val.2)
      (H true) Finset.univ S m z i=
    markedFiniteBalance (fun e:E'=>e.val.1) (fun e=>e.val.2) (fun e:K'=>e.val.1) (fun e=>e.val.2)
      (J true) Finset.univ S' m z i∧
    markedFiniteDomainBalance (fun e:E=>e.val.1) (fun e=>e.val.2) (fun e:K=>e.val.1) (fun e=>e.val.2)
      (H true) Finset.univ S m X Z z i=
    markedFiniteDomainBalance (fun e:E'=>e.val.1) (fun e=>e.val.2) (fun e:K'=>e.val.1) (fun e=>e.val.2)
      (J true) Finset.univ S' m X Z z i:=by
  subst τ
  subst J
  exact ⟨rfl,rfl⟩

theorem marked_sample_outside_balance_congr
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ)
    (σ τ:RawMarkedOutcome V U Γ Color) (H J:Bool→V→U→Prop)
    (hσ:σ=τ) (hH:H=J) (X:Finset V) (Z:Finset U):
    let E:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let K:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    let E':=MarkedSampleArc P π (3*d) (fun e=>τ (Sum.inl e)) false
    let K':=MarkedSampleArc P π (3*d) (fun e=>τ (Sum.inl e)) true
    let S:=Finset.univ.filter (fun s:V×U=>H false s.1 s.2∨H true s.1 s.2)
    let S':=Finset.univ.filter (fun s:V×U=>J false s.1 s.2∨J true s.1 s.2);
    MarkedOutsideBalance (fun e:E=>e.val.1) (fun e=>e.val.2) (fun e:K=>e.val.1) (fun e=>e.val.2)
      (H true) Finset.univ S m X Z↔
    MarkedOutsideBalance (fun e:E'=>e.val.1) (fun e=>e.val.2) (fun e:K'=>e.val.1) (fun e=>e.val.2)
      (J true) Finset.univ S' m X Z:=by
  subst τ
  subst J
  exact Iff.rfl

end Oberwolfach

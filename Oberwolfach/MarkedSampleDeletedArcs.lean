module

public import Oberwolfach.RawMarkedRimDeletion
public import Oberwolfach.MarkedSampleArcs
public import Oberwolfach.MarkedWheelRestriction

@[expose] public section

/-! Deleting physical coordinates retains the original ordered typed arcs.
The equivalence records the exact surviving occurrence, without choosing a
new orientation or identifying different physical representations. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem markedPhysicalRim_delete_iff
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (σ:RawMarkedOutcome V U Γ Color)
    (D:Finset (Sym2 V)) (mark:Bool) (x y:V):
    markedPhysicalRim P π (3*d) (fun e=>rawMarkedDeleteRims σ D (Sum.inl e)) mark x y=1 ↔
      markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) mark x y=1 ∧
      s(x,if mark then π y else y)∉D:=by
  have h:=rawMarkedDeleteRims_rims P π d σ D (if mark then Sum.inr (x,y) else Sum.inl (x,y))
  cases mark <;> simpa only [rawMarkedPairRims,markedPairPhysical,Bool.false_eq_true,ite_false,ite_true,
    Sum.elim_inl,Sum.elim_inr] using h

def markedSampleDeletedArcEquiv
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (σ:RawMarkedOutcome V U Γ Color)
    (D:Finset (Sym2 V)) (mark:Bool):
    MarkedSampleArc P π (3*d) (fun e=>rawMarkedDeleteRims σ D (Sum.inl e)) mark ≃
      {e:MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) mark //
        s(e.val.1,if mark then π e.val.2 else e.val.2)∉D} where
  toFun e:=⟨⟨e.val,((markedPhysicalRim_delete_iff P π d σ D mark e.val.1 e.val.2).mp e.property).1⟩,
    ((markedPhysicalRim_delete_iff P π d σ D mark e.val.1 e.val.2).mp e.property).2⟩
  invFun e:=⟨e.val.val,(markedPhysicalRim_delete_iff P π d σ D mark e.val.val.1 e.val.val.2).mpr
    ⟨e.val.property,e.property⟩⟩
  left_inv e:=rfl
  right_inv e:=rfl

theorem markedSampleDeletedArcEquiv_endpoints
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (σ:RawMarkedOutcome V U Γ Color)
    (D:Finset (Sym2 V)) (mark:Bool)
    (e:MarkedSampleArc P π (3*d) (fun e=>rawMarkedDeleteRims σ D (Sum.inl e)) mark):
    (markedSampleDeletedArcEquiv P π d σ D mark e).val.val=e.val:=rfl

def markedSampleDeletedWheelToOriginal
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ) (σ:RawMarkedOutcome V U Γ Color)
    (D:Finset (Sym2 V)) (H₀ HK:V→U→Prop)
    (W:MarkedWheel
      (fun e:MarkedSampleArc P π (3*d) (fun e=>rawMarkedDeleteRims σ D (Sum.inl e)) false=>e.val.1) (fun e=>e.val.2)
      (fun e:MarkedSampleArc P π (3*d) (fun e=>rawMarkedDeleteRims σ D (Sum.inl e)) true=>e.val.1) (fun e=>e.val.2)
      m π (3*d) H₀ HK):
    MarkedWheel
      (fun e:MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false=>e.val.1) (fun e=>e.val.2)
      (fun e:MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true=>e.val.1) (fun e=>e.val.2)
      m π (3*d) H₀ HK:=
  ⟨⟨W.1.val,W.1.property.1,
    fun j=>by
      obtain ⟨e,ht,hh⟩:=W.1.property.2.1 j
      exact ⟨(markedSampleDeletedArcEquiv P π d σ D false e).val,ht,hh⟩,
    by
      obtain ⟨e,ht,hh⟩:=W.1.property.2.2
      exact ⟨(markedSampleDeletedArcEquiv P π d σ D true e).val,ht,hh⟩⟩,W.2⟩

theorem markedSampleDeletedWheelToOriginal_resources
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ) (σ:RawMarkedOutcome V U Γ Color)
    (D:Finset (Sym2 V)) (H₀ HK:V→U→Prop)
    (W:MarkedWheel
      (fun e:MarkedSampleArc P π (3*d) (fun e=>rawMarkedDeleteRims σ D (Sum.inl e)) false=>e.val.1) (fun e=>e.val.2)
      (fun e:MarkedSampleArc P π (3*d) (fun e=>rawMarkedDeleteRims σ D (Sum.inl e)) true=>e.val.1) (fun e=>e.val.2)
      m π (3*d) H₀ HK):
    markedWheelPhysicalResources (markedSampleDeletedWheelToOriginal P π d m σ D H₀ HK W)=
      markedWheelPhysicalResources W:=by
  have hr:markedCyclePhysicalEdges _ _ _ _ _ _ _
      (markedSampleDeletedWheelToOriginal P π d m σ D H₀ HK W).1=
      markedCyclePhysicalEdges _ _ _ _ _ _ _ W.1:=by
    apply Finset.image_congr
    intro i _
    simp only [Function.comp_apply,markedCyclePhysicalEdge_at,markedSampleDeletedWheelToOriginal]
  unfold markedWheelPhysicalResources
  rw [hr]
  rfl

end Oberwolfach

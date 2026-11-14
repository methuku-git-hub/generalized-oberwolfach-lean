module

public import Oberwolfach.MarkedProtectedInnerCutsChanges
public import Oberwolfach.MarkedProtectedPairFromChangeGraphs
public import Oberwolfach.MarkedSampleOccurrenceMatrix
public import Oberwolfach.MarkedCutFamiliesToLargeCut

@[expose] public section
/-! The inner cuts are unchanged when physical changes avoid the protected
inner pair; marked rim heads use the preserved permutation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_inner_cuts_of_exact_agreement
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ)
    (σ τ:RawMarkedOutcome V U Γ Color) (H H':Bool→V→U→Prop)
    (I:Finset V) (J:Finset U)
    (hR:∀mark x y,x∈I→y∈I→
      (markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) mark x y=1 ↔
       markedPhysicalRim P π (3*d) (fun e=>τ (Sum.inl e)) mark x y=1))
    (hS:∀b x u,x∈I→u∈J→(H b x u↔H' b x u)) (δ h:ℝ)
    (hrim:∀ mark,BipartiteLargeCut
      (fun x:I=>fun y:I=>markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) mark x.val y.val) δ h)
    (hspoke:∀ mark,BipartiteLargeCut
      (relationMultiplicity (fun x:I=>fun u:J=>H mark x.val u.val)) δ h):
    (∀ mark,BipartiteLargeCut
      (fun x:I=>fun y:I=>markedPhysicalRim P π (3*d) (fun e=>τ (Sum.inl e)) mark x.val y.val) δ h) ∧
    (∀ mark,BipartiteLargeCut
      (relationMultiplicity (fun x:I=>fun u:J=>H' mark x.val u.val)) δ h) := by
  constructor
  · intro mark
    have heq:(fun x:I=>fun y:I=>markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) mark x.val y.val)=
      (fun x:I=>fun y:I=>markedPhysicalRim P π (3*d) (fun e=>τ (Sum.inl e)) mark x.val y.val):=by
      funext x y
      have hh:=hR mark x.val y.val x.property y.property
      have h0:=markedPhysicalRim_indicator P π (3*d) (fun e=>σ (Sum.inl e)) mark x.val y.val
      have h1:=markedPhysicalRim_indicator P π (3*d) (fun e=>τ (Sum.inl e)) mark x.val y.val
      by_cases ht:markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) mark x.val y.val=1
      · have ht':=hh.mp ht
        simp [ht,ht'] at h0 h1
        omega
      · have ht':¬markedPhysicalRim P π (3*d) (fun e=>τ (Sum.inl e)) mark x.val y.val=1:=fun h=>ht (hh.mpr h)
        simp [ht,ht'] at h0 h1
        omega
    rw [←heq]
    exact hrim mark
  · intro mark
    have heq:(fun x:I=>fun u:J=>H mark x.val u.val)=(fun x:I=>fun u:J=>H' mark x.val u.val):=by
      funext x u
      exact propext (hS mark x.val u.val x.property u.property)
    rw [←heq]
    exact hspoke mark
end Oberwolfach

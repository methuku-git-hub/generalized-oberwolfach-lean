module

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

theorem marked_protected_inner_cuts_after_changes
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ)
    (σ τ:RawMarkedOutcome V U Γ Color) (H H':Bool→V→U→Prop)
    (I:Finset V) (J:Finset U) (FR:SimpleGraph V) (FS:SimpleGraph (V⊕U))
    (hI:∀ x,x∈I→π x∈I)
    (hRim:∀ a,¬(rawMarkedPairRims P π d σ a↔rawMarkedPairRims P π d τ a)→markedPairPhysical π a∈FR.edgeFinset)
    (hSpoke:∀ b v u,¬(H b v u↔H' b v u)→FS.Adj (Sum.inl v) (Sum.inr u))
    (hFR:∀ x∈I,∀ y∈I,¬FR.Adj x y)
    (hFS:∀ x∈I,∀ u∈J,¬FS.Adj (Sum.inl x) (Sum.inr u)) (δ h:ℝ)
    (hrim:∀ mark,BipartiteLargeCut
      (fun x:I=>fun y:I=>markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) mark x.val y.val) δ h)
    (hspoke:∀ mark,BipartiteLargeCut
      (relationMultiplicity (fun x:I=>fun u:J=>H mark x.val u.val)) δ h):
    (∀ mark,BipartiteLargeCut
      (fun x:I=>fun y:I=>markedPhysicalRim P π (3*d) (fun e=>τ (Sum.inl e)) mark x.val y.val) δ h) ∧
    (∀ mark,BipartiteLargeCut
      (relationMultiplicity (fun x:I=>fun u:J=>H' mark x.val u.val)) δ h) := by
  obtain ⟨hR,hS⟩:=marked_protected_pair_from_change_graphs P π d σ τ H H' I J FR FS hI hRim hSpoke hFR hFS
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

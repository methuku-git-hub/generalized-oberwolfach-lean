module

public import Oberwolfach.MarkedRestrictedDegreeCounts
public import Oberwolfach.MarkedInnerCutsOfExactAgreement

@[expose] public section
/-! Protected inner rims and spokes have zero restricted change at inner
roots. Bounds at roots outside the protected sets remain separate. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_inner_change_zero_on_protected_roots
    {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [LinearOrder V] [DecidableEq U]
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (A:Finset V) (B:Finset U)
    (σ τ:RawMarkedOutcome V U Γ Color) (H H':Bool→V→U→Prop)
    (hrim:∀mark x y,x∈A→y∈A→
      (markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) mark x y=1 ↔
       markedPhysicalRim P π (3*d) (fun e=>τ (Sum.inl e)) mark x y=1))
    (hspoke:∀b v u,v∈A→u∈B→(H b v u↔H' b v u)):
    (∀mark incoming v,v∈A→
      markedRestrictedDegree P π (3*d) (fun e=>τ (Sum.inl e)) mark incoming v A=
      markedRestrictedDegree P π (3*d) (fun e=>σ (Sum.inl e)) mark incoming v A) ∧
    (∀b v,v∈A→(∑u∈B,if ¬(H b v u↔H' b v u) then (1:ℝ) else 0)=0) ∧
    (∀b u,u∈B→(∑v∈A,if ¬(H b v u↔H' b v u) then (1:ℝ) else 0)=0) :=by
  have heq:∀mark x y,x∈A→y∈A→
      markedPhysicalRim P π (3*d) (fun e=>τ (Sum.inl e)) mark x y=
      markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) mark x y:=by
    intro mark x y hx hy
    have hh:=hrim mark x y hx hy
    have h0:=markedPhysicalRim_indicator P π (3*d) (fun e=>σ (Sum.inl e)) mark x y
    have h1:=markedPhysicalRim_indicator P π (3*d) (fun e=>τ (Sum.inl e)) mark x y
    by_cases ht:markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) mark x y=1
    · have ht':=hh.mp ht
      simp [ht,ht'] at h0 h1
      omega
    · have ht':¬markedPhysicalRim P π (3*d) (fun e=>τ (Sum.inl e)) mark x y=1:=fun h=>ht (hh.mpr h)
      simp [ht,ht'] at h0 h1
      omega
  refine ⟨?_,?_,?_⟩
  · intro mark incoming v hv
    unfold markedRestrictedDegree
    apply Finset.sum_congr rfl
    intro y hy
    cases incoming with
    | false => simpa using heq mark v y hv hy
    | true => simpa using heq mark y v hy hv
  · intro b v hv
    apply Finset.sum_eq_zero
    intro u hu
    simp [hspoke b v u hv hu]
  · intro b u hu
    apply Finset.sum_eq_zero
    intro v hv
    simp [hspoke b v u hv hu]
end Oberwolfach

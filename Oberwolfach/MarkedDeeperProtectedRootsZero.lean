module

public import Oberwolfach.MarkedInnerChangeZeroOnProtectedRoots

@[expose] public section
/-! Agreement on the whole first inner set also controls the restricted
degrees and rows of every deeper subset, at every first-inner root. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_deeper_protected_roots_zero
    {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [LinearOrder V] [DecidableEq U]
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (A T:Finset V) (B R:Finset U)
    (hTA:T⊆A) (hRB:R⊆B)
    (σ τ:RawMarkedOutcome V U Γ Color) (H H':Bool→V→U→Prop)
    (hrim:∀mark x y,x∈A→y∈A→
      (markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) mark x y=1 ↔
       markedPhysicalRim P π (3*d) (fun e=>τ (Sum.inl e)) mark x y=1))
    (hspoke:∀b v u,v∈A→u∈B→(H b v u↔H' b v u)):
    (∀mark incoming v,v∈A→
      markedRestrictedDegree P π (3*d) (fun e=>τ (Sum.inl e)) mark incoming v T=
      markedRestrictedDegree P π (3*d) (fun e=>σ (Sum.inl e)) mark incoming v T) ∧
    (∀b v,v∈A→(∑u∈R,if ¬(H b v u↔H' b v u) then (1:ℝ) else 0)=0) :=by
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
  refine ⟨?_,?_⟩
  · intro mark incoming v hv
    unfold markedRestrictedDegree
    apply Finset.sum_congr rfl
    intro y hy
    cases incoming with
    | false => simpa using heq mark v y hv (hTA hy)
    | true => simpa using heq mark y v (hTA hy) hv
  · intro b v hv
    apply Finset.sum_eq_zero
    intro u hu
    simp [hspoke b v u hv (hRB hu)]
end Oberwolfach

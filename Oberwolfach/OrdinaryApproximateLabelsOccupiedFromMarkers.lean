module

public import Oberwolfach.InnerRequiredApproximateOccupied
public import Oberwolfach.ActualResidualSumIndices

@[expose] public section
/-! Recover occupancy of every approximate label from the marker witness
retained in the actual component data. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_approximate_labels_occupied_from_markers
    {n:ℕ} {U A J X:Type} [Fintype U] [DecidableEq U] [Fintype A] [DecidableEq A] [DecidableEq J] [Fintype X] [DecidableEq X]
    (π:Equiv.Perm (Fin n)) (d:ℕ) (σ:RawIntervalFamilyOutcome (Fin n) U Bool Bool) (w:U)
    {F:SimpleGraph X}
    (data:ActualResidualData (K:=A⊕{a:Fin n // rawIntervalColouredStart π d (fun e=>σ (w,e)) a true}) (J:=J) F)
    (hs₂:data.s₂=secondSumIndices)
    (inner:Finset X) (ψ:X→Fin n)
    (root:(A⊕{a:Fin n // rawIntervalColouredStart π d (fun e=>σ (w,e)) a true})→Fin n)
    (hroot:∀b,root (.inr b)=b.val)
    (hmarkers:∀i∈data.s₂,∀j:Fin (d+1),∃x∈data.oldDomain\inner,
      ψ x=(π^j.val) (root i)):
    ∀x,rawIntervalFamilyState π d σ (x,w)=some (Sum.inl true)→x∈(data.oldDomain\inner).image ψ:=by
  intro x hx
  have hcov:rawIntervalCovered π d (fun e=>σ (w,e)) x true:=
    (rawIntervalState_interval_iff π d (fun e=>σ (w,e)) x true).mp hx
  obtain ⟨a,ha,hwin⟩:=hcov
  obtain ⟨j,hj⟩:=(permutationWindow_mem_iff π 0 (d-1) a x).mp hwin
  have hjlt:j.val<d+1:=by have hj':=j.isLt;omega
  let b:{a:Fin n // rawIntervalColouredStart π d (fun e=>σ (w,e)) a true}:=⟨a,ha⟩
  have hi:(Sum.inr b)∈data.s₂:=by rw [hs₂];simp [secondSumIndices]
  obtain ⟨y,hy,heq⟩:=hmarkers (.inr b) hi ⟨j.val,hjlt⟩
  have hj':(π^j.val) a=x:=by simpa using hj
  apply Finset.mem_image.mpr
  refine ⟨y,hy,?_⟩
  rw [hroot] at heq
  dsimp [b] at heq
  exact heq.trans hj'
end Oberwolfach

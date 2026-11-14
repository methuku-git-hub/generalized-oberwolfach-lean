module

public import Oberwolfach.PackedSelectedWheelsExhaust
public import Oberwolfach.RawMarkedResourceCoordinates
public import Oberwolfach.PermutationWindows
public import Oberwolfach.ActualResidualSumIndices

@[expose] public section
/-! Each matched marked wheel at a hub is rooted at a segment of one of the
actual approximate intervals. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance longPackedMarkedRootsFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem long_packed_marked_roots_in_approximate_intervals
    {n:ℕ} {U A J E L:Type} [Fintype U] [DecidableEq U] [Fintype A] [DecidableEq A] [DecidableEq J]
    (π:Equiv.Perm (Fin n)) (d m:ℕ) (hd:0<d) (tail head:E→Fin n) (ktail khead:L→Fin n)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (w:U) {F:SimpleGraph (Fin n)}
    (data:ActualResidualData (K:=A⊕{a:Fin n // rawIntervalColouredStart π d (fun e=>raw (Sum.inr (w,e))) a true}) (J:=J) F)
    (hs₂:data.s₂=secondSumIndices)
    (root:(A⊕{a:Fin n // rawIntervalColouredStart π d (fun e=>raw (Sum.inr (w,e))) a true})→Fin n)
    (hroot:∀b,root (.inr b)=b.val)
    (S:Finset (MarkedWheel tail head ktail khead m π (3*d)
      (rawMarkedPairSpokes π d raw true true false) (rawMarkedPairSpokes π d raw true true true)))
    (hHub:∀W∈S,W.2.val=w):
    ∀W∈S,∃i∈data.s₂,∃j<d,W.1.val 0=(π^j) (root i):=by
  intro W hW
  have hs:rawIntervalFamilyState π d (fun e=>raw (Sum.inr e)) (W.1.val 0,w)=some (Sum.inl true):=by
    have h:=W.2.property.1
    rw [hHub W hW] at h
    simp only [rawMarkedPairSpokes,rawMarkedSpokes] at h
    exact h
  have hcov:rawIntervalCovered π d (fun e=>raw (Sum.inr (w,e))) (W.1.val 0) true:=
    (rawIntervalState_interval_iff π d _ _ true).mp hs
  obtain ⟨a,ha,hwin⟩:=hcov
  obtain ⟨j,hj⟩:=(permutationWindow_mem_iff π 0 (d-1) a (W.1.val 0)).mp hwin
  have hjlt:j.val<d:=by have h:=j.isLt;omega
  let b:{a:Fin n // rawIntervalColouredStart π d (fun e=>raw (Sum.inr (w,e))) a true}:=⟨a,ha⟩
  have hi:Sum.inr b∈data.s₂:=by rw [hs₂];simp [secondSumIndices]
  refine ⟨Sum.inr b,hi,j.val,hjlt,?_⟩
  rw [hroot]
  have heq:(π^j.val) a=W.1.val 0:=by simpa using hj
  exact heq.symm
end Oberwolfach

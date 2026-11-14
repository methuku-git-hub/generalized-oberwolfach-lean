module

public import Oberwolfach.PackedPhysicalSpokePositions
public import Oberwolfach.RetainedAndRawIntervalGeometry
public import Oberwolfach.ActualResidualSumIndices
public import Oberwolfach.RawIntervalGeometry
public import Oberwolfach.RawMarkedResourceCoordinates

@[expose] public section
/-! A missing selected position on an approximate interval is a sampled true
spoke not covered by the marked wheel pack at that hub. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_missing_position_uncovered_spoke
    {n:ℕ} {U E L:Type} [Fintype U] [DecidableEq U]
    {X J:U→Type} [∀w,Fintype (X w)] [∀w,DecidableEq (X w)] [∀w,DecidableEq (J w)]
    (π:Equiv.Perm (Fin n)) (d m b:ℕ) (hd:1≤d)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (t:ℕ)
    (Jret:StartRetentionOutcome (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false) t)
    (tail head:E→Fin n) (ktail khead:L→Fin n)
    (M:U→Finset (MarkedWheel tail head ktail khead m π b
      (rawMarkedPairSpokes π d raw true true false) (rawMarkedPairSpokes π d raw true true true)))
    (F:∀w,SimpleGraph (X w))
    (data:∀w,ActualResidualData
      (K:=(retainedMarkedIndex π d (fun e=>raw (Sum.inr e)) false t Jret w) ⊕
        {a:Fin n // rawIntervalColouredStart π d (fun e=>raw (Sum.inr (w,e))) a true}) (J:=J w) (F w))
    (hs₂:∀w,(data w).s₂=secondSumIndices)
    (hT:∀w a,(data w).T (.inr a)=packedPhysicalSpokePositions tail head ktail khead m b d π
      (rawMarkedPairSpokes π d raw true true false) (rawMarkedPairSpokes π d raw true true true) (M w) w a.val):
    ∀w i,i∈(data w).s₂→∀j<d,j∉(data w).T i→
      let v:=(π^j) (retainedAndRawIntervalRoot π d (fun e=>raw (Sum.inr e)) false true t Jret w i);
      rawMarkedPairSpokes π d raw true true true v w ∧
      ¬∃Z∈M w,Sum.inr (v,w)∈markedWheelPhysicalResources Z :=by
  intro w i hi j hj hnot v
  rw [hs₂ w,secondSumIndices] at hi
  obtain ⟨a,ha,haeq⟩:=Finset.mem_image.mp hi
  subst i
  have hv:rawMarkedPairSpokes π d raw true true true v w:=by
    simp only [rawMarkedPairSpokes,rawMarkedSpokes]
    simp only [rawIntervalFamilyState]
    have hcov:rawIntervalCovered π d (fun e=>raw (Sum.inr (w,e))) v true:=by
      refine ⟨a.val,a.property,?_⟩
      apply (permutationWindow_mem_iff π 0 (d-1) a.val v).mpr
      refine ⟨⟨j,by omega⟩,?_⟩
      simp [v,retainedAndRawIntervalRoot]
    have hh:=(rawIntervalState_interval_iff π d (fun e=>raw (Sum.inr (w,e))) v true).2 hcov
    convert hh using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  refine ⟨hv,?_⟩
  intro hcover
  apply hnot
  rw [hT w a]
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_range.mpr hj,?_⟩
  simpa [v,retainedAndRawIntervalRoot] using hcover
end Oberwolfach

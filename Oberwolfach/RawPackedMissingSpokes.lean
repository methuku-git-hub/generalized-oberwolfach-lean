module

public import Oberwolfach.RawOrdinaryMissingSpokes
public import Oberwolfach.PackedPhysicalSpokePositions

@[expose] public section
/-! Specialize the missing-position bound to the actual packed physical
spokes used by the residual source construction. -/
set_option autoImplicit false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem raw_packed_missing_positions_le_uncovered
    {V U E L:Type} [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U]
    (π:Equiv.Perm V) (d:ℕ) (hd:1≤d)
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (σ:RawIntervalFamilyOutcome V U Bool Bool) (t:ℕ)
    (J:StartRetentionOutcome (rawStartHubSet π d σ false) t) (w:U)
    (s:Finset {x:V // rawIntervalColouredStart π d (fun e=>σ (w,e)) x true})
    (tail head:E→V) (ktail khead:L→V) (m b:ℕ) (H₀ Hₖ:V→U→Prop)
    (M:Finset (MarkedWheel tail head ktail khead m π b H₀ Hₖ)):
    let T:=fun i:{x:V // rawIntervalColouredStart π d (fun e=>σ (w,e)) x true}=>
      packedPhysicalSpokePositions tail head ktail khead m b d π H₀ Hₖ M w i.val
    let Covered:=Finset.univ.filter (fun v=>∃W∈M,Sum.inr (v,w)∈markedWheelPhysicalResources W)
    (∑i∈s,(d-(T i).card))≤
      ((Finset.univ.filter (fun v=>rawMarkedSpokes π d σ true true true v w))\Covered).card:=by
  intro T Covered
  have hT:∀i∈s,T i⊆Finset.range d:=by
    intro i hi j hj
    exact (Finset.mem_filter.mp hj).1
  apply raw_ordinary_missing_positions_le_uncovered π d hd hnoshort σ t J w s T hT Covered
  intro i hi j hj hc
  have hcov:∃W∈M,Sum.inr ((π^j) i.val,w)∈markedWheelPhysicalResources W:=(Finset.mem_filter.mp hc).2
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj,hcov⟩
end Oberwolfach

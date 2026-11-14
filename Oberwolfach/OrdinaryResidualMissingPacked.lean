module

public import Oberwolfach.RawPackedMissingSpokes
public import Oberwolfach.ActualResidualMissingSum

@[expose] public section
/-! For the actual split into retained and approximate intervals, missing
approximate positions are bounded by marked sampled spokes not covered by
the chosen marked wheel family. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_residual_missing_from_packed
    {n:ℕ} {U X A J E L:Type} [Fintype U] [DecidableEq U] [Fintype X] [DecidableEq X]
    [DecidableEq A] [DecidableEq J] [Fintype E] [Fintype L]
    {F:SimpleGraph X} (π:Equiv.Perm (Fin n)) (d m:ℕ) (hd:1≤d)
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (t:ℕ)
    (Jret:StartRetentionOutcome (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false) t) (u:U)
    (tail head:E→Fin n) (ktail khead:L→Fin n) (H₀ Hₖ:Fin n→U→Prop)
    (M:Finset (MarkedWheel tail head ktail khead m π (3*d) H₀ Hₖ)):
    let B:={x:Fin n // rawIntervalColouredStart π d (fun e=>raw (Sum.inr (u,e))) x true};
    ∀a:ActualResidualData (K:=A⊕B) (J:=J) F,
      a.d=d→a.s₂=secondSumIndices→
      (∀b:B,a.T (.inr b)=packedPhysicalSpokePositions tail head ktail khead m (3*d) d π H₀ Hₖ M u b.val)→
    let Covered:=Finset.univ.filter (fun v=>∃W∈M,Sum.inr (v,u)∈markedWheelPhysicalResources W);
      (∑i∈a.s₂,(a.d-(a.T i).card))≤
        ((Finset.univ.filter (fun v=>rawMarkedSpokes π d (fun e=>raw (Sum.inr e)) true true true v u))\Covered).card:=by
  intro B a hd' hs hpositions Covered
  have h₁:=raw_packed_missing_positions_le_uncovered π d hd hnoshort (fun e=>raw (Sum.inr e)) t Jret u
    (Finset.univ:Finset B) tail head ktail khead m (3*d) H₀ Hₖ M
  have hsum:=actual_residual_missing_sum_second_indices a hs
  rw [hsum]
  simp only [hd',hpositions]
  simpa only [Finset.sum_const_zero] using h₁
end Oberwolfach

module

public import Oberwolfach.OrdinaryZeroWeightNoStarts
public import Oberwolfach.OrdinaryAssignedClassRecipe

@[expose] public section
/-! At an inactive ordinary hub, both marked colours have zero weight, so
there are no raw or retained intervals to reserve paths for. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_inactive_hub_no_intervals {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (θ c:ℝ) (π:Equiv.Perm (Fin n)) (d:ℕ) (raw:RawMarkedOutcome (Fin n) U Bool Bool)
    (t:ℕ) (J:StartRetentionOutcome (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false) t) (u:U)
    (hinactive:ordinaryAssignedFraction F hF K u none<θ/100)
    (hsupport:∀g v,rawMarkedPairSpokes π d raw g true true v u→
      ordinaryAssignedMarkedProbability F hF K θ c u g≠0):
    Fintype.card (retainedAndRawIntervalIndex π d (fun e=>raw (Sum.inr e)) false true t J u)=0 :=by
  let q:=ordinaryAssignedMarkedProbability F hF K θ c
  have hzero:∀g,q u g=0:=by
    intro g
    cases g <;> simp [q,ordinaryAssignedMarkedProbability,ordinaryAssignedLongWeight,hinactive]
  have hnone:∀g a,¬rawIntervalColouredStart π d (fun e=>raw (Sum.inr (u,e))) a g:=by
    intro g a
    have hh:=ordinary_zero_weight_no_starts π d raw q g true u (hzero g) (hsupport g) a
    convert hh using 1 <;> congr! 5
  have hcard:∀g,Fintype.card {a:Fin n // rawIntervalColouredStart π d (fun e=>raw (Sum.inr (u,e))) a g}=0:=by
    intro g
    apply Fintype.card_eq_zero_iff.mpr
    exact ⟨fun a=>hnone g a.val a.property⟩
  have hh:=retained_raw_interval_count_le_raw_counts π d (fun e=>raw (Sum.inr e)) false true t J u
  rw [raw_interval_hub_count_eq_card,raw_interval_hub_count_eq_card,hcard false,hcard true] at hh
  simp only [Nat.cast_zero,add_zero] at hh
  have hz:(Fintype.card (retainedAndRawIntervalIndex π d (fun e=>raw (Sum.inr e)) false true t J u):ℝ)=0:=
    le_antisymm hh (Nat.cast_nonneg _)
  exact_mod_cast hz
end Oberwolfach

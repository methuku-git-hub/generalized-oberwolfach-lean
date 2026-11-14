module

public import Oberwolfach.LongRetainedAbsorberRowBound
public import Oberwolfach.ReservedSpokeTrimmedLists

@[expose] public section
/-! Trim reserved lists using the actual retained absorber row estimate. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem reserved_lists_from_retained_absorber_rows
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (F:U→SimpleGraph (Fin n)) (hF:∀w,(F w).IsRegularOfDegree 2)
    (π:Equiv.Perm (Fin n)) (d m:ℕ) (hd:0<d) (hm:0<m) (θ:ℝ)
    (σ:RawIntervalFamilyOutcome (Fin n) U Bool Bool)
    (t:ℕ) (J:StartRetentionOutcome (rawStartHubSet π d σ false) t)
    (hstarts:∀w,|rawIntervalHubStartCount π d false σ w-
      (n:ℝ)*longAssignedIntervalProbability F hF K m θ w false/d|<(n:ℝ)^(3/4:ℝ)/d)
    (D:Fin n→Fin n→Prop) (Inner:Finset (Fin n)) (Old:U→Finset (Fin n))
    (β lam ε η:ℝ) (hlam:0≤lam)
    (hInner:(Inner.card:ℝ)≤ε*n) (hsub:(n:ℝ)^(3/4:ℝ)≤η*n)
    (hcoeff:lam+ε+1/(100*(m:ℝ))+η≤β)
    (hext:∀w,IsExtendingList D (rawReservedSpokeList π d σ w) β)
    (hOld:∀w,Disjoint (rawReservedSpokeList π d σ w) (Old w)):
    (∀w,IsExtendingList D (rawReservedSpokeList π d σ w\(Inner∪retainedFinalMarkedAt π d σ t J w)) lam) ∧
    (∀w,Disjoint (rawReservedSpokeList π d σ w\(Inner∪retainedFinalMarkedAt π d σ t J w)) (Old w)):=by
  have hbudget:∀w,lam*Fintype.card (Fin n)+Inner.card+
      (retainedFinalMarkedAt π d σ t J w).card≤β*Fintype.card (Fin n):=by
    intro w
    have hAbs:=long_retained_absorber_row_from_starts F hF π d m hd hm θ σ t J hstarts w
    have hAbs':((retainedFinalMarkedAt π d σ t J w).card:ℝ)≤(1/(100*(m:ℝ))+η)*n:=by
      have hh:((retainedFinalMarkedAt π d σ t J w).card:ℝ)≤(n:ℝ)/(100*(m:ℝ))+η*n:=by linarith
      convert hh using 1 <;> ring
    have hcoeff':=(mul_le_mul_of_nonneg_right hcoeff (Nat.cast_nonneg n))
    simp only [Fintype.card_fin]
    nlinarith
  exact reserved_spoke_trimmed_lists π d σ D Inner (retainedFinalMarkedAt π d σ t J) Old β lam hlam hbudget hext hOld
end Oberwolfach

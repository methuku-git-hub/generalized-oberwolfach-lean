module

public import Oberwolfach.LongSelectedMarkedStartBalance
public import Oberwolfach.MarkedExpandedPhysicalLaw

@[expose] public section
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance selectedMarkedSampleBalanceFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem long_sample_marked_retained_indegree_balance
    {n d D m:ℕ} {U:Type} [Fintype U] [DecidableEq U] [Nonempty (Fin n)]
    (P:SimpleGraph (Fin n)) (hreg:P.IsRegularOfDegree D) (hD:0<D) (hd:0<d) (hm:0<m)
    (π:Equiv.Perm (Fin n)) (σ:RawIntervalFamilyOutcome (Fin n) U Bool Bool)
    (ω:Sym2 (Fin n)→Fin 6×Bool) (q:U→Bool→ℝ) (s p p₂ k₂ u err:ℝ) (herr:0≤err)
    (hq:∀w,q w false=s/(m:ℝ))
    (hstarts:∀v,|((rawStartHubSet π d σ false v).card:ℝ)-(∑w,q w false/(d:ℝ))|≤err)
    (hheads:∀v,|((∑x,sampledColourOrientation P ω 1 x v:ℕ):ℝ)-
      markedExpandedPhysicalProbability p (initialIndexDensity U D*(s/(m:ℝ))/2) p₂ k₂ u 1/2*P.degree v|≤err):
    ∀v,|((∑x,sampledColourOrientation P ω 1 x v:ℕ):ℝ)-
      (d:ℝ)*(startRetentionMinimum (rawStartHubSet π d σ false):ℝ)|≤err+(d:ℝ)*err :=by
  apply long_selected_marked_indegree_retained_start_balance P D d m hD hd hm π σ false ω s err herr
  · intro v
    simpa only [hq] using hstarts v
  · intro v
    have hh:=hheads v
    simp only [markedExpandedPhysicalProbability,Matrix.cons_val_one,Matrix.cons_val_zero,hreg v] at hh
    have heq:2*(initialIndexDensity U D*(s/(m:ℝ))/2)/2*(D:ℝ)=initialIndexDensity U D*(s/(m:ℝ))/2*(D:ℝ):=by ring
    rw [heq] at hh
    exact hh
end Oberwolfach

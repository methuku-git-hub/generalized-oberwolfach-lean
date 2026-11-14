module

public import Oberwolfach.OrdinaryAssignedRetainedMassUpper
public import Oberwolfach.OrdinaryAssignedCoefficientBalance
public import Oberwolfach.OrdinaryAssignedRootCountUpper
public import Oberwolfach.OrdinaryAssignedMarkedProbabilityUpper
public import Oberwolfach.OrdinaryAssignedFrequencyCoefficient
public import Oberwolfach.OrdinaryAssignedRetainedMass
public import Oberwolfach.OrdinaryAssignedKeptMassBound
public import Oberwolfach.OrdinaryAssignedMarkedProbabilityUpperGeneral
public import Oberwolfach.OrdinaryAbundanceReservation

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_assigned_retained_mass_upper_of_reserve
    {n:ℕ} (hn:0<n) {U:Type} [Fintype U]
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (S:Set ℕ) (hS:∀u,AllowedCycleLengths (F u) S)
    (K:ℕ) (hK:0<K) (i₀:Fin K) (rsv θ c:ℝ)
    (hs0:0≤rsv) (hs1:rsv≤1/100) (hθ:0<θ) (hθ1:θ≤1/100) (hc:8≤c)
    (hreserve:∀w,rsv≤((Finset.univ.filter (fun v=>longPreparationCycleClass (F w) (hF w) K v=some i₀)).card:ℝ)/n) (u:U):
    (1-θ)*(∑i:Fin K,ordinaryAssignedKeptFraction F hF K i₀ rsv θ u i)+
      c*ordinaryAssignedLongWeight F hF K θ c u ≤ 1-rsv-θ/2 :=by
  have hh:=ordinary_factor_actual_marginals hn (F u) (hF u) K hK i₀ rsv θ c hs0 hs1 hθ.le hθ1 hc (hreserve u)
  have hu:θ/2≤1-rsv-ordinaryAssignedLongWeight F hF K θ c u-
      ordinaryAssignedShortWeight F hF K i₀ rsv θ c u:=by
    simpa only [ordinaryAssignedShortWeight,ordinaryAssignedLongWeight,ordinaryAssignedFraction] using hh.2.2.2.1
  have hb:ordinaryAssignedShortWeight F hF K i₀ rsv θ c u=
      (c-1)*ordinaryAssignedLongWeight F hF K θ c u+
      (1-θ)*(∑i:Fin K,ordinaryAssignedKeptFraction F hF K i₀ rsv θ u i):=by
    rfl
  nlinarith [hu,hb]

theorem ordinary_assigned_coefficient_balance_of_reserve
    {n:ℕ} (hn:0<n) {U:Type} [Fintype U]
    (F:U→SimpleGraph (Fin n)) (hF:∀w,(F w).IsRegularOfDegree 2)
    (K:ℕ) (hK:0<K) (i₀:Fin K) (rsv θ c:ℝ)
    (hs0:0≤rsv) (hs1:rsv≤1/100) (hθ:0<θ) (hθ1:θ≤1/100) (hc:8≤c)
    (S:Set ℕ) (hS:∀w,AllowedCycleLengths (F w) S)
    (hreserve:∀w,rsv≤((Finset.univ.filter (fun v=>longPreparationCycleClass (F w) (hF w) K v=some i₀)).card:ℝ)/n):
    ∀u,(∑i,ordinaryAssignedFrequencyCoefficient F hF K i₀ rsv θ c u i)*
      ordinaryAssignedShortWeight F hF K i₀ rsv θ c u+
      (c-1)*ordinaryAssignedLongWeight F hF K θ c u=
      ordinaryAssignedShortWeight F hF K i₀ rsv θ c u :=by
  intro u
  have hh:=ordinary_factor_frequency_weight_allocation hn (F u) (hF u) K hK i₀ rsv θ c
    hs0 hs1 hθ.le hθ1 hc (hreserve u)
  simpa only [ordinaryAssignedFrequencyCoefficient,ordinaryAssignedKeptFraction,
      ordinaryAssignedShortWeight,ordinaryAssignedLongWeight,ordinaryAssignedFraction] using hh.2.2


theorem ordinary_assigned_root_count_upper_of_reserve
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (hn:0<n) (hK:0<K) (m d:ℕ) (hm:7≤m) (hd:0<d)
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (Allowed:Set ℕ) (hAllowed:∀u,AllowedCycleLengths (F u) Allowed)
    (i₀:Fin K) (rsv θ:ℝ) (hrs0:0≤rsv) (hrs1:rsv≤1/100) (hθ:0<θ) (hθ1:θ≤1/100)
    (hreserve:∀w,rsv≤((Finset.univ.filter (fun v=>longPreparationCycleClass (F w) (hF w) K v=some i₀)).card:ℝ)/n)
    (π:Equiv.Perm (Fin n)) (σ:RawIntervalFamilyOutcome (Fin n) U Bool Bool)
    (r:ℕ) (Jret:StartRetentionOutcome (rawStartHubSet π d σ false) r) (u:U)
    (hcounts:∀g,|rawIntervalHubStartCount π d g σ u-
      (n:ℝ)*ordinaryAssignedMarkedProbability F hF K θ ((m:ℝ)+1) u g/d|<(n:ℝ)^(3/4:ℝ)/d):
    (Fintype.card (retainedAndRawIntervalIndex π d σ false true r Jret u):ℝ)≤
      ((n:ℝ)+2*(n:ℝ)^(3/4:ℝ))/d:=by
  have hm8:8≤(m:ℝ)+1:=by
    have hh:8≤m+1:=by omega
    exact_mod_cast hh
  have hc0:0<(m:ℝ)+1:=by linarith
  have hh:=ordinary_factor_actual_marginals hn (F u) (hF u) K hK i₀ rsv θ ((m:ℝ)+1)
    hrs0 hrs1 hθ.le hθ1 hm8 (hreserve u)
  have ha:ordinaryAssignedLongWeight F hF K θ ((m:ℝ)+1) u≤1/((m:ℝ)+1):=by
    simpa only [ordinaryAssignedLongWeight,ordinaryAssignedFraction] using hh.2.2.2.2.2.2.1
  have hone:1/((m:ℝ)+1)≤1:=(div_le_one₀ hc0).2 (by linarith)
  have hq:ordinaryAssignedMarkedProbability F hF K θ ((m:ℝ)+1) u false+
      ordinaryAssignedMarkedProbability F hF K θ ((m:ℝ)+1) u true≤1:=by
    simp only [ordinaryAssignedMarkedProbability,Bool.false_eq_true,ite_false,ite_true,zero_add]
    exact ha.trans hone
  have hroot:=retained_raw_interval_root_upper_general π d 1 hd (by omega) σ r Jret u
    (ordinaryAssignedMarkedProbability F hF K θ ((m:ℝ)+1) u) ((n:ℝ)^(3/4:ℝ)) hcounts
  simp only [Nat.cast_one,one_mul] at hroot
  have hqN:=mul_le_mul_of_nonneg_left hq (show (0:ℝ)≤n by positivity)
  have hd0:0<(d:ℝ):=by exact_mod_cast hd
  apply (le_div_iff₀ hd0).2
  nlinarith

theorem ordinary_assigned_marked_probability_upper_of_reserve
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (hn:0<n) (hK:0<K) (m:ℕ) (hm:7≤m)
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (Allowed:Set ℕ) (hAllowed:∀u,AllowedCycleLengths (F u) Allowed)
    (i₀:Fin K) (rsv θ:ℝ) (hrs0:0≤rsv) (hrs1:rsv≤1/100) (hθ:0<θ) (hθ1:θ≤1/100)
    (hreserve:∀w,rsv≤((Finset.univ.filter (fun v=>longPreparationCycleClass (F w) (hF w) K v=some i₀)).card:ℝ)/n):
    ∀u g,ordinaryAssignedMarkedProbability F hF K θ ((m:ℝ)+1) u g≤1/((m:ℝ)+1):=by
  have hm8:8≤(m:ℝ)+1:=by
    have hh:8≤m+1:=by omega
    exact_mod_cast hh
  intro u g
  have hh:=ordinary_factor_actual_marginals hn (F u) (hF u) K hK i₀ rsv θ ((m:ℝ)+1)
    hrs0 hrs1 hθ.le hθ1 hm8 (hreserve u)
  have ha:ordinaryAssignedLongWeight F hF K θ ((m:ℝ)+1) u≤1/((m:ℝ)+1):=by
    simpa only [ordinaryAssignedLongWeight,ordinaryAssignedFraction] using hh.2.2.2.2.2.2.1
  cases g <;> simp only [ordinaryAssignedMarkedProbability,Bool.false_eq_true,ite_false,ite_true]
  · positivity
  · exact ha

theorem ordinary_assigned_frequency_coefficient_of_reserve
    {n:ℕ} (hn:0<n) {U:Type} [Fintype U]
    (F:U→SimpleGraph (Fin n)) (hF:∀w,(F w).IsRegularOfDegree 2)
    (S:Set ℕ) (hS:∀w,AllowedCycleLengths (F w) S)
    (K:ℕ) (hK:0<K) (i₀:Fin K) (s θ c:ℝ)
    (hs0:0≤s) (hs1:s≤1/100) (hθ:0<θ) (hθ1:θ≤1/100) (hc:8≤c)
    (hreserve:∀w,s≤((Finset.univ.filter (fun v=>longPreparationCycleClass (F w) (hF w) K v=some i₀)).card:ℝ)/n):
    ∀w,0<ordinaryAssignedShortWeight F hF K i₀ s θ c w ∧
      (∀i,0≤ordinaryAssignedFrequencyCoefficient F hF K i₀ s θ c w i ∧
        ordinaryAssignedFrequencyCoefficient F hF K i₀ s θ c w i≤1/ordinaryAssignedShortWeight F hF K i₀ s θ c w) ∧
      (∀i,ordinaryAssignedFrequencyCoefficient F hF K i₀ s θ c w i*
        ordinaryAssignedShortWeight F hF K i₀ s θ c w=(1-θ)*ordinaryAssignedKeptFraction F hF K i₀ s θ w i) :=by
  intro w
  have hh:=ordinary_factor_frequency_weight_allocation hn (F w) (hF w) K hK i₀ s θ c hs0 hs1 hθ.le hθ1 hc (hreserve w)
  have hb:0<ordinaryAssignedShortWeight F hF K i₀ s θ c w:=by
    convert hh.1 using 1 <;>
      simp only [ordinaryAssignedShortWeight,ordinaryAssignedLongWeight,ordinaryAssignedFraction]
  have hη:∀i,0≤ordinaryAssignedFrequencyCoefficient F hF K i₀ s θ c w i ∧
      ordinaryAssignedFrequencyCoefficient F hF K i₀ s θ c w i≤1/ordinaryAssignedShortWeight F hF K i₀ s θ c w:=by
    intro i
    convert hh.2.1 i using 1 <;>
      simp only [ordinaryAssignedFrequencyCoefficient,ordinaryAssignedKeptFraction,ordinaryAssignedShortWeight,ordinaryAssignedLongWeight,ordinaryAssignedFraction]
  refine ⟨hb,hη,?_⟩
  intro i
  unfold ordinaryAssignedFrequencyCoefficient
  exact div_mul_cancel₀ _ (ne_of_gt hb)

theorem ordinary_assigned_retained_mass_of_reserve
    {n:ℕ} (hn:0<n) {U:Type} [Fintype U]
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (S:Set ℕ) (hS:∀u,AllowedCycleLengths (F u) S)
    (K:ℕ) (hK:0<K) (i₀:Fin K) (rsv θ c:ℝ)
    (hs0:0≤rsv) (hs1:rsv≤1/100) (hθ:0<θ) (hθ1:θ≤1/100) (hc:8≤c)
    (hreserve:∀w,rsv≤((Finset.univ.filter (fun v=>longPreparationCycleClass (F w) (hF w) K v=some i₀)).card:ℝ)/n) (u:U):
    1-rsv-2*θ ≤ (1-θ)*(∑i:Fin K,ordinaryAssignedKeptFraction F hF K i₀ rsv θ u i)+
      c*ordinaryAssignedLongWeight F hF K θ c u :=by
  have hh:=ordinary_factor_actual_marginals hn (F u) (hF u) K hK i₀ rsv θ c hs0 hs1 hθ.le hθ1 hc (hreserve u)
  have hu:1-rsv-ordinaryAssignedLongWeight F hF K θ c u-
      ordinaryAssignedShortWeight F hF K i₀ rsv θ c u≤2*θ:=by
    simpa only [ordinaryAssignedShortWeight,ordinaryAssignedLongWeight,ordinaryAssignedFraction] using hh.2.2.2.2.1
  have hb:ordinaryAssignedShortWeight F hF K i₀ rsv θ c u=
      (c-1)*ordinaryAssignedLongWeight F hF K θ c u+
      (1-θ)*(∑i:Fin K,ordinaryAssignedKeptFraction F hF K i₀ rsv θ u i):=by
    rfl
  nlinarith [hu,hb]

theorem ordinary_assigned_kept_mass_le_unreserved_of_reserve
    {n:ℕ} (hn:0<n) {U:Type} [Fintype U]
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (Allowed:Set ℕ) (hAllowed:∀u,AllowedCycleLengths (F u) Allowed)
    (K:ℕ) (hK:0<K) (i₀:Fin K) (rsv θ:ℝ) (hrs:0≤rsv)
    (hreserve:∀w,rsv≤((Finset.univ.filter (fun v=>longPreparationCycleClass (F w) (hF w) K v=some i₀)).card:ℝ)/n) (u:U):
    (∑i:Fin K,ordinaryAssignedKeptFraction F hF K i₀ rsv θ u i)≤1-rsv:=by
  have hp:=ordinary_factor_frequency_partition hn (F u) (hF u) K hK i₀ rsv hrs (hreserve u)
  let f:=fun i:Fin K=>ordinaryAssignedFraction F hF K u (some i)-(if i=i₀ then rsv else 0)
  have hf:∀i,0≤f i:=by
    simpa only [f,ordinaryAssignedFraction] using hp.1
  have hlong:0≤ordinaryAssignedFraction F hF K u none:=by
    simpa only [ordinaryAssignedFraction] using hp.2.1
  have hpart:(∑i:Fin K,f i)+ordinaryAssignedFraction F hF K u none=1-rsv:=by
    simpa only [f,ordinaryAssignedFraction] using hp.2.2
  have hsum:(∑i:Fin K,ordinaryAssignedKeptFraction F hF K i₀ rsv θ u i)≤∑i:Fin K,f i:=by
    apply Finset.sum_le_sum
    intro i _
    change (if f i<θ/(100*(K:ℝ)) then 0 else f i)≤f i
    split
    · exact hf i
    · exact le_rfl
  linarith

theorem ordinary_assigned_marked_probability_upper_general_of_reserve
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (hn:0<n) (hK:0<K) (c:ℝ) (hc:8≤c)
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (Allowed:Set ℕ) (hAllowed:∀u,AllowedCycleLengths (F u) Allowed)
    (i₀:Fin K) (rsv θ:ℝ) (hrs0:0≤rsv) (hrs1:rsv≤1/100) (hθ:0<θ) (hθ1:θ≤1/100)
    (hreserve:∀w,rsv≤((Finset.univ.filter (fun v=>longPreparationCycleClass (F w) (hF w) K v=some i₀)).card:ℝ)/n):
    ∀u g,ordinaryAssignedMarkedProbability F hF K θ c u g≤1/c:=by
  intro u g
  have hh:=ordinary_factor_actual_marginals hn (F u) (hF u) K hK i₀ rsv θ c
    hrs0 hrs1 hθ.le hθ1 hc (hreserve u)
  have ha:ordinaryAssignedLongWeight F hF K θ c u≤1/c:=by
    simpa only [ordinaryAssignedLongWeight,ordinaryAssignedFraction] using hh.2.2.2.2.2.2.1
  cases g <;> simp only [ordinaryAssignedMarkedProbability,Bool.false_eq_true,ite_false,ite_true]
  · positivity
  · exact ha

end Oberwolfach

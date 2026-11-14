module

public import Oberwolfach.OrdinaryUnreservedResidualSizeFromCounts
public import Oberwolfach.OrdinaryCandidateClassReservation
public import Oberwolfach.CandidateOrdinaryAssignedRetainedMassUpper
public import Oberwolfach.OrdinaryUnreservedResidualSize
public import Oberwolfach.OrdinaryAssignedRetainedMassUpper
public import Oberwolfach.RetainedRawIntervalRootUpperGeneral
public import Oberwolfach.OrdinaryAssignedClassRecipe

@[expose] public section
/-! The residual retains the θ fraction, up to the sampled start and cycle
mass errors. This supplies the lower bound needed for matching capacity. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 15000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_unreserved_residual_size_lower_from_counts_candidate
    {n K:ℕ} {U J:Type} [Fintype U] [DecidableEq U] [DecidableEq J]
    (hn:0<n) (hK:0<K) (m d:ℕ) (hm:7≤m) (hd:0<d)
    (F:U→SimpleGraph (Fin n)) (hF:∀w,(F w).IsRegularOfDegree 2)
    (Allowed:Set ℕ) (hAllowed:∀u,AllowedCycleLengths (F u) Allowed)
    (i₀:Fin K) (rsv θ:ℝ) (hrs0:0≤rsv) (hrs1:rsv≤1/100) (hθ0:0<θ) (hθ1:θ≤1/100)
    (hrsclass:rsv≤1/(2*(K:ℝ))) (hclass:∀u,i₀∈factorShortCandidates (F u) K)
    (π:Equiv.Perm (Fin n)) (σ:RawIntervalFamilyOutcome (Fin n) U Bool Bool)
    (r:ℕ) (Jret:StartRetentionOutcome (rawStartHubSet π d σ false) r) (w:U)
    (Cres:Finset (F w).ConnectedComponent) (hsize:∀c:↥Cres,Fintype.card c.val=i₀.val+1)
    (hres:((i₀.val+1:ℕ):ℝ)*Cres.card=rsv*n)
    (data:ActualResidualData (K:=retainedAndRawIntervalIndex π d σ false true r Jret w) (J:=J) ((F w).induce {x | (F w).connectedComponentMk x∉Cres}))
    (hc:data.c=m+1) (hd':data.d=d)
    (hs1:data.s₁=firstSumIndices (A:=retainedMarkedIndex π d σ false r Jret w)
      (B:={a:Fin n // rawIntervalColouredStart π d (fun e=>σ (w,e)) a true}))
    (hs2:data.s₂=secondSumIndices (A:=retainedMarkedIndex π d σ false r Jret w)
      (B:={a:Fin n // rawIntervalColouredStart π d (fun e=>σ (w,e)) a true}))
    (t err:ℝ)
    (hcounts:∀g,|rawIntervalHubStartCount π d g σ w-
      (n:ℝ)*ordinaryAssignedMarkedProbability F hF K θ ((m:ℝ)+1) w g/(d:ℝ)|<t/(d:ℝ))
    (hC:((data.t.biUnion (fun j=>(data.C j).support.toFinset)).card:ℝ)≤
      (n:ℝ)*((1-θ)*(∑i:Fin K,ordinaryAssignedKeptFraction F hF K i₀ rsv θ w i))+err):
    (θ/2)*n-err-2*((m:ℝ)+1)*t≤(data.remaining.card:ℝ):=by
  have h1:data.s₁.card=Fintype.card (retainedMarkedIndex π d σ false r Jret w):=by
    rw [hs1]
    simpa only [Fintype.card_coe] using (Fintype.card_congr
      (firstSumIndexEquiv (A:=retainedMarkedIndex π d σ false r Jret w)
        (B:={a:Fin n // rawIntervalColouredStart π d (fun e=>σ (w,e)) a true}))).symm
  have h2:data.s₂.card=Fintype.card {a:Fin n // rawIntervalColouredStart π d (fun e=>σ (w,e)) a true}:=by
    rw [hs2]
    simpa only [Fintype.card_coe] using (Fintype.card_congr
      (secondSumIndexEquiv (A:=retainedMarkedIndex π d σ false r Jret w)
        (B:={a:Fin n // rawIntervalColouredStart π d (fun e=>σ (w,e)) a true}))).symm
  have hcard:=actual_residual_size_lower data
  rw [hc,hd',h1,h2,←Fintype.card_sum] at hcard
  have hsource:=ordinary_unreserved_factor_cardinality (F w) Cres hsize
  change Fintype.card {x:Fin n // (F w).connectedComponentMk x∉Cres}+(i₀.val+1)*Cres.card=n at hsource
  have hcardR:(n:ℝ)≤((i₀.val+1:ℕ):ℝ)*Cres.card+(data.remaining.card:ℝ)+
      ((data.t.biUnion (fun j=>(data.C j).support.toFinset)).card:ℝ)+
      (((m+1)*d-1:ℕ):ℝ)*Fintype.card (retainedAndRawIntervalIndex π d σ false true r Jret w):=by
    have hcard':n≤(i₀.val+1)*Cres.card+data.remaining.card+(data.t.biUnion (fun j=>(data.C j).support.toFinset)).card+
        ((m+1)*d-1)*Fintype.card (retainedAndRawIntervalIndex π d σ false true r Jret w):=by
      simp only [retainedAndRawIntervalIndex] at hcard ⊢
      have hEq : Fintype.card (↑{x:Fin n | (F w).connectedComponentMk x∉Cres}:Type) =
          Fintype.card {x:Fin n // (F w).connectedComponentMk x∉Cres} := by
        apply Fintype.card_congr
        exact Equiv.refl _
      omega
    exact_mod_cast hcard'
  rw [hres] at hcardR
  have hm':(((m+1)*d-1:ℕ):ℝ)≤(((m+1:ℕ):ℝ)*d):=by exact_mod_cast (Nat.sub_le ((m+1)*d) 1)
  have hindex:(0:ℝ)≤Fintype.card (retainedAndRawIntervalIndex π d σ false true r Jret w):=by positivity
  have hmul:=mul_le_mul_of_nonneg_right hm' hindex
  have hroot:=retained_raw_interval_root_upper_general π d (m+1) hd (by omega) σ r Jret w
    (ordinaryAssignedMarkedProbability F hF K θ ((m:ℝ)+1) w) t hcounts
  have hmass0:=ordinary_assigned_retained_mass_upper_candidate hn F hF Allowed hAllowed K hK i₀ rsv θ ((m:ℝ)+1)
    hrs0 hrs1 hθ0 hθ1 (by
      have hm8:8≤m+1:=by omega
      exact_mod_cast hm8) hrsclass hclass w
  have hmass:(∑g:Bool,ordinaryAssignedMarkedProbability F hF K θ ((m:ℝ)+1) w g)*((m:ℝ)+1)+
      (1-θ)*(∑i:Fin K,ordinaryAssignedKeptFraction F hF K i₀ rsv θ w i)≤1-rsv-θ/2:=by
    simp only [Fintype.sum_bool,ordinaryAssignedMarkedProbability,Bool.false_eq_true,ite_false,ite_true]
    nlinarith
  simp only [Fintype.sum_bool] at hmass
  have hmassN:=mul_le_mul_of_nonneg_left hmass (show 0≤(n:ℝ) by positivity)
  push_cast at hroot hmul
  nlinarith
end Oberwolfach

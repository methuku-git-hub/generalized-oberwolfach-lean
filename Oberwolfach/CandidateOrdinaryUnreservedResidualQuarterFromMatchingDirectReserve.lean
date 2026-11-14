module

public import Oberwolfach.OrdinaryClassReserveBound
public import Oberwolfach.CandidateOrdinaryUnreservedResidualQuarterFromMatching
public import Oberwolfach.OrdinaryUnreservedResidualQuarterFromMatching
public import Oberwolfach.OrdinaryCandidateClassReservation
public import Oberwolfach.CandidateOrdinaryAssignedKeptMassBoundDirectReserve
public import Oberwolfach.CandidateOrdinaryAssignedRetainedMassUpperDirectReserve
public import Oberwolfach.CandidateOrdinaryUnreservedResidualLowerMatchingDirectReserve
public import Oberwolfach.OrdinaryUnreservedResidualLowerMatching
public import Oberwolfach.OrdinaryAssignedKeptMassBound
public import Oberwolfach.ApproximateSublinearMargin
public import Oberwolfach.OrdinaryMatchingResidualCycleMassUpper
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

theorem ordinary_unreserved_residual_quarter_lower_from_matching_candidate_direct_reserve
    (m d:ℕ) (hm:7≤m) (hd:0<d) (θ:ℝ) (hθ0:0<θ):
    ∃N:ℕ,∀{n K:ℕ} (hnN:N≤n) {U:Type} [Fintype U] [DecidableEq U]
    (hn:0<n) (hK:0<K)
    (F:U→SimpleGraph (Fin n)) (hF:∀w,(F w).IsRegularOfDegree 2)
    (Allowed:Set ℕ) (hAllowed:∀u,AllowedCycleLengths (F u) Allowed)
    (i₀:Fin K) (rsv:ℝ) (hrs0:0≤rsv) (hrs1:rsv≤1/100) (hθ1:θ≤1/100)
    (hClassReserve:OrdinaryClassReserveBound F hF i₀ rsv)
    (π:Equiv.Perm (Fin n)) (σ:RawIntervalFamilyOutcome (Fin n) U Bool Bool)
    (r:ℕ) (Jret:StartRetentionOutcome (rawStartHubSet π d σ false) r) (w:U)
    (Cres:Finset (F w).ConnectedComponent) (hsize:∀c:↥Cres,Fintype.card c.val=i₀.val+1)
    (hres:((i₀.val+1:ℕ):ℝ)*Cres.card=rsv*n)
    (RM:MarkedWheel (Prod.fst:Fin n×Fin n→Fin n) Prod.snd Prod.fst Prod.snd m π (3*d)
      (fun _ (_:U)=>True) (fun _ (_:U)=>True)→Finset (((Fin n×Fin n)⊕(Fin n×Fin n))⊕(Bool×Fin n×U)))
    (state:(((Fin n×Fin n)⊕(Fin n×Fin n))⊕(Bool×Fin n×U))→Bool)
    (L:Finset (PhysicalSampledCandidate (mixedCandidateResources
      (ordinaryMixedGenericResources RM (fun (i:Fin K) (W:OrderedOrdinaryWheel (U:=U) π (3*d) (longPaddedSeedExponent i+2))=>orderedOrdinaryResources W))) state))
    (data:ActualResidualData (K:=retainedAndRawIntervalIndex π d σ false true r Jret w)
      (J:=OrdinaryPhysicalUnmarkedHub (K:=K) π d m RM state L w) ((F w).induce {x | (F w).connectedComponentMk x∉Cres}))
    (hc:data.c=m+1) (hd':data.d=d)
    (hs1:data.s₁=firstSumIndices (A:=retainedMarkedIndex π d σ false r Jret w)
      (B:={a:Fin n // rawIntervalColouredStart π d (fun e=>σ (w,e)) a true}))
    (hs2:data.s₂=secondSumIndices (A:=retainedMarkedIndex π d σ false r Jret w)
      (B:={a:Fin n // rawIntervalColouredStart π d (fun e=>σ (w,e)) a true}))
    (err:ℝ) (herr0:0≤err) (herr:err≤θ/8)
    (hcounts:∀g,|rawIntervalHubStartCount π d g σ w-
      (n:ℝ)*ordinaryAssignedMarkedProbability F hF K θ ((m:ℝ)+1) w g/(d:ℝ)|<(n:ℝ)^(3/4:ℝ)/(d:ℝ))
    (ht:data.t=Finset.univ)
    (hEmbed:data.Cembed=data.t.biUnion (fun j=>(data.C j).support.toFinset))
    (hlen:∀j,(data.C j).length=longPaddedSeedExponent (ordinaryPhysicalUnmarkedPayload π d m RM state L w j).1+2)
    (hmatch:((∑j:OrdinaryPhysicalUnmarkedHub (K:=K) π d m RM state L w,
        (longPaddedSeedExponent (ordinaryPhysicalUnmarkedPayload π d m RM state L w j).1+2)):ℝ)≤
      (1-θ+err)*(n:ℝ)*(∑i:Fin K,ordinaryAssignedKeptFraction F hF K i₀ rsv θ w i)),
    (θ/4)*n≤(data.remaining.card:ℝ):=by
  let c:ℝ:=(m:ℝ)+1
  have hc0:0<c:=by dsimp [c];positivity
  obtain ⟨N,hN⟩:=eventually_three_quarters_and_constant_le_linear (θ/(16*c)) 0 (by positivity)
  refine ⟨N,?_⟩
  intro n K hnN U _ _ hn hK F hF Allowed hAllowed i₀ rsv hrs0 hrs1 hθ1 hClassReserve π σ r Jret w Cres hsize hres RM state L data hc hd' hs1 hs2 err herr0 herr hcounts ht hEmbed hlen hmatch
  have hroot:=hN n hnN
  have hroot':2*c*(n:ℝ)^(3/4:ℝ)≤(θ/8)*n:=by
    have hh:=mul_le_mul_of_nonneg_left hroot (show 0≤2*c by positivity)
    have heq:2*c*(θ/(16*c)*(n:ℝ))=(θ/8)*n:=by field_simp;ring
    nlinarith [heq]
  have hkept:=ordinary_assigned_kept_mass_le_unreserved_candidate_direct_reserve hn F hF Allowed hAllowed K hK i₀ rsv θ hrs0 hClassReserve w
  have hkept1:(∑i:Fin K,ordinaryAssignedKeptFraction F hF K i₀ rsv θ w i)≤1:=by linarith
  have he:=mul_le_mul_of_nonneg_left hkept1 (show 0≤err*(n:ℝ) by positivity)
  have he':err*n*(∑i:Fin K,ordinaryAssignedKeptFraction F hF K i₀ rsv θ w i)≤(θ/8)*n:=by
    have hn0:(0:ℝ)≤n:=by positivity
    nlinarith [mul_le_mul_of_nonneg_right herr hn0]
  have hsize:=ordinary_unreserved_residual_size_lower_from_matching_candidate_direct_reserve hn hK m d hm hd F hF Allowed hAllowed i₀ rsv θ hrs0 hrs1 hθ0 hθ1 hClassReserve
    π σ r Jret w Cres hsize hres RM state L data hc hd' hs1 hs2 ((n:ℝ)^(3/4:ℝ)) err hcounts ht hEmbed hlen hmatch
  dsimp [c] at hroot'
  nlinarith
end Oberwolfach

module

public import Oberwolfach.OrdinaryUnreservedResidualLowerMatching
public import Oberwolfach.OrdinaryCandidateClassReservation
public import Oberwolfach.CandidateOrdinaryAssignedRetainedMassUpper
public import Oberwolfach.CandidateOrdinaryUnreservedResidualSizeFromCounts
public import Oberwolfach.OrdinaryUnreservedResidualSizeFromCounts
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

theorem ordinary_unreserved_residual_size_lower_from_matching_candidate
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (hn:0<n) (hK:0<K) (m d:ℕ) (hm:7≤m) (hd:0<d)
    (F:U→SimpleGraph (Fin n)) (hF:∀w,(F w).IsRegularOfDegree 2)
    (Allowed:Set ℕ) (hAllowed:∀u,AllowedCycleLengths (F u) Allowed)
    (i₀:Fin K) (rsv θ:ℝ) (hrs0:0≤rsv) (hrs1:rsv≤1/100) (hθ0:0<θ) (hθ1:θ≤1/100)
    (hrsclass:rsv≤1/(2*(K:ℝ))) (hclass:∀u,i₀∈factorShortCandidates (F u) K)
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
    (t err:ℝ)
    (hcounts:∀g,|rawIntervalHubStartCount π d g σ w-
      (n:ℝ)*ordinaryAssignedMarkedProbability F hF K θ ((m:ℝ)+1) w g/(d:ℝ)|<t/(d:ℝ))
    (ht:data.t=Finset.univ)
    (hEmbed:data.Cembed=data.t.biUnion (fun j=>(data.C j).support.toFinset))
    (hlen:∀j,(data.C j).length=longPaddedSeedExponent (ordinaryPhysicalUnmarkedPayload π d m RM state L w j).1+2)
    (hmatch:((∑j:OrdinaryPhysicalUnmarkedHub (K:=K) π d m RM state L w,
        (longPaddedSeedExponent (ordinaryPhysicalUnmarkedPayload π d m RM state L w j).1+2)):ℝ)≤
      (1-θ+err)*(n:ℝ)*(∑i:Fin K,ordinaryAssignedKeptFraction F hF K i₀ rsv θ w i)):
    (θ/2)*n-err*n*(∑i:Fin K,ordinaryAssignedKeptFraction F hF K i₀ rsv θ w i)-2*((m:ℝ)+1)*t≤(data.remaining.card:ℝ):=by
  have hcycle:=ordinary_matching_residual_cycle_mass_upper F hF i₀ rsv θ π d m RM state L w err hmatch data ht hEmbed hlen
  exact ordinary_unreserved_residual_size_lower_from_counts_candidate hn hK m d hm hd F hF Allowed hAllowed i₀ rsv θ hrs0 hrs1 hθ0 hθ1 hrsclass hclass
    π σ r Jret w Cres hsize hres data hc hd' hs1 hs2 t
    (err*n*(∑i:Fin K,ordinaryAssignedKeptFraction F hF K i₀ rsv θ w i)) hcounts hcycle
end Oberwolfach

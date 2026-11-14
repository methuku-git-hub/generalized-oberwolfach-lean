module

public import Oberwolfach.LongActualResidualMassLower
public import Oberwolfach.ActualResidualFullMassBound
public import Oberwolfach.LongActualResidualMissingBound
public import Oberwolfach.ResidualLongErrorBudget
public import Oberwolfach.LongMissingErrorBudget

@[expose] public section
/-! The actual residual has at most 10θn vertices once the same sample's
start, retention, ordinary-mass and matching tests hold. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 25000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance longActualResidualSizeToleranceFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem long_actual_residual_size_from_common_tests_at_tolerance
    (m d:ℕ) (hm:0<m) (hd:m+2≤d) (θ:ℝ) (hθ:0<θ) (hθmax:θ≤1/100)
    (ζ:ℝ) (N:ℕ)
    (hN:∀n:ℕ,N≤n→∀q errOrd:ℝ,
      q≤1/((m:ℝ)+1)→errOrd≤θ*n→
      (n:ℝ)*q/d+(((m+1)*d-1:ℕ):ℝ)*(2*((n:ℝ)^(3/4:ℝ)/d)+ζ*n)+errOrd≤4*θ*n):
    ∀(n K:ℕ) (hn:N≤n) (hn0:0<n) (hK:0<K)
    (U:Type) [Fintype U] [DecidableEq U]
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n))
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (ℓ:Fin K→ℕ) (raw:RawMarkedOutcome (Fin n) U Bool Bool)
    (t:ℕ) (Jret:StartRetentionOutcome (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false) t)
    (hgood:RetainedRestrictionGood π d (fun e=>raw (Sum.inr e)) false t
      (fun _:Unit=>Finset.univ) (fun _:Unit=>Finset.univ) ζ Jret)
    (Del:Finset (Sym2 (Fin n))),
    let R:=mixedCandidateResources (longRawSeedResources (U:=U) π d m ℓ)
    let T:=bernoulliVertexSet (longRawHubState P π d raw true true)
    let S:=longRawSurvivingResources P π d raw true true Del
    let hST:=long_raw_surviving_resources_subset P π d raw true true Del
    let q:=survivingCandidateEmbedding R S T hST
    let Q:=restrictedResourceSet R (Function.Embedding.subtype (·∈S))
    ∀(M:Finset (RestrictedResource R (Function.Embedding.subtype (·∈S)))) (w:U)
    (lam α γ errOrd:ℝ) (hlam:0≤lam) (hlamθ:lam≤θ) (hα:α≤lam/(10*(d:ℝ)))
    (hγ:0≤γ) (hγcap:γ≤lam/(10*(d:ℝ)))
    (hmatch:∀i,((longRawIncidenceSet S i\M.biUnion Q).card:ℝ)≤max (α*n) (γ*(longRawIncidenceSet S i).card))
    (herrOrd:errOrd≤θ*n)
    (hcounts:∀g:Bool,|rawIntervalHubStartCount π d g (fun e=>raw (Sum.inr e)) w-
      (n:ℝ)*longAssignedIntervalProbability F hF K m θ w g/d|<(n:ℝ)^(3/4:ℝ)/d),
    let A:=retainedMarkedIndex π d (fun e=>raw (Sum.inr e)) false t Jret w
    let B:={x:Fin n // rawIntervalColouredStart π d (fun e=>raw (Sum.inr (w,e))) x true}
    let Marked:=longRawMarkedWheelsAtHub P π d m ℓ raw true true (M.map q) w
    ∀{J:Type} [DecidableEq J] (a:ActualResidualData (K:=A⊕B) (J:=J) (F w))
    (hc:a.c=m+1) (hd':a.d=d) (hs₁:a.s₁=firstSumIndices) (hs₂:a.s₂=secondSumIndices)
    (hpositions:∀b:B,a.T (.inr b)=packedPhysicalSpokePositions _ _ _ _ m (3*d) d π
      (rawMarkedPairSpokes π d raw true true false) (rawMarkedPairSpokes π d raw true true true) Marked w b.val)
    (hC:(n:ℝ)*((1-θ)*(∑i:Fin K,longAssignedKeptFraction F hF K θ i w))-errOrd≤
      ((a.t.biUnion (fun j=>(a.C j).support.toFinset)).card:ℝ)),
    (a.remaining.card:ℝ)≤10*θ*n:=by
  have hd1:1≤d:=by omega
  intro n K hn hn0 hK U _ _ F hF P π hnoshort ℓ raw t Jret hgood Del R T S hST q Q M w lam α γ errOrd hlam hlamθ hα hγ hγcap hmatch herrOrd hcounts A B Marked J _ a hc hd' hs₁ hs₂ hpositions hC
  have hq:=long_assigned_interval_probability_sum_le (K:=K) hn0 m hm F hF θ hθ.le (by linarith) w
  have herr:=hN n hn (∑g:Bool,longAssignedIntervalProbability F hF K m θ w g) errOrd hq herrOrd
  have hmass:=long_actual_residual_full_mass_lower hn0 hK F hF m d hm hd1 θ hθ.le (by linarith) π
    (fun e=>raw (Sum.inr e)) t Jret ζ errOrd (4*θ) hgood w hcounts a hc hd' hs₁ hs₂ hC herr
  have hmissing:=long_actual_residual_missing_from_matching P π d m hd1 hnoshort ℓ raw t Jret Del M w α γ hγ hmatch a hd' hs₂ hpositions
  have hsize:=actual_residual_size_from_mass_and_missing a ((101/100:ℝ)*θ+4*θ) (max α γ)
    (by simp only [Fintype.card_fin]; convert hmass using 1 <;> ring) (by simpa only [Fintype.card_fin] using hmissing)
  have hbudget:=long_missing_error_le_theta m d hd θ lam α γ hθ.le hlam hlamθ hα hγcap
  rw [hc] at hsize
  have hnR:(0:ℝ)≤n:=by positivity
  have hbudgetN:=mul_le_mul_of_nonneg_right hbudget hnR
  simp only [Fintype.card_fin,Nat.cast_add,Nat.cast_one] at hsize
  nlinarith
end Oberwolfach

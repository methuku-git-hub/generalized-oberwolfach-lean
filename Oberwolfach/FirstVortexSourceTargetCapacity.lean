module

public import Oberwolfach.FirstVortexSourceMatchingTargetSize
public import Oberwolfach.FirstVortexSourceMatchingCapacity

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance firstVortexSourceTargetCapacityFin (n:ℕ):DecidableEq (Fin n):=selectedAlignedSourceWithLoadFin n

theorem first_vortex_source_matching_target_and_capacity
    (ε θ ρ₀ lam:ℝ) (m d:ℕ) (hm:0<m) (hε:0<ε) (hθ:0<θ) (hθ1:θ≤1)
    (hρhi:ρ₀≤1) (hεsmall:ε≤(ρ₀/4)/80000)
    (hlam:0≤lam) (hlam1:lam≤1) (hd:0<d) (hspacing:1/(d:ℝ)≤θ/1024):
    ∃N:ℕ,∀n K:ℕ,N≤n→0<K→∀(U:Type) [Fintype U] [DecidableEq U]
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n))
    (Dv mm:ℕ) (β:ℝ) (Vort:Vortex U P Dv β ε mm)
    (hreg:P.IsRegularOfDegree Dv) (hDv:0<Dv) (hρ:initialIndexDensity U Dv≤1) (hmm:0<mm)
    (σE:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)
    (Del:Finset (Sym2 (Fin n))) (t:ℕ)
    (Jret:StartRetentionOutcome (rawStartHubSet π d
      (fun e=>rawExpandedApproximateCollapse (Sum.inr e) (σE (Sum.inr e))) false) t),
    let ℓ:=fun i:Fin K=>longPaddedSeedExponent i+2
    let raw:RawMarkedOutcome (Fin n) U Bool Bool:=fun e=>rawExpandedApproximateCollapse e (σE e)
    let H:=Vort.extendedIndices 1
    let A:=Vort.extendedVertices 1
    let σ:=fun e=>raw (Sum.inr e)
    let R:=mixedCandidateResources (longRawSeedResources (U:=U) π d m ℓ)
    let T:=bernoulliVertexSet (longRawHubState P π d raw true true)
    let S:=longRawSurvivingResources P π d raw true true Del
    let hST:=long_raw_surviving_resources_subset P π d raw true true Del
    let q:=survivingCandidateEmbedding R S T hST
    let Q:=restrictedResourceSet R (Function.Embedding.subtype (·∈S))
    ∀(M:Finset (RestrictedResource R (Function.Embedding.subtype (·∈S))))
    (F:U→SimpleGraph (Fin n)) (hF:∀w,(F w).IsRegularOfDegree 2)
    (a γ ζ:ℝ) (hγ:0≤γ) (ha:a≤lam/(10*d)) (hγcap:γ≤lam/(10*d))
    (hζ:ζ≤θ/4096) (hζ0:0≤ζ)
    (hmatch:∀i,((longRawIncidenceSet S i\M.biUnion Q).card:ℝ)≤max (a*n) (γ*(longRawIncidenceSet S i).card))
    (hrows:RetainedRestrictionLocalGood π d σ false t A H ζ Jret)
    (hfixed:∀w∈H,|rawIntervalUnassignedHubCountOn π d σ w A-
      (A.card:ℝ)*(1-(∑g,longAssignedIntervalProbability F hF K m θ w g)-
        (∑j,longAssignedSpokeProbability F hF K m θ w j))|<(A.card:ℝ)^(3/4:ℝ))
    (hcolumn:∀v∈A,|rawIntervalUnassignedColumnCount π d σ v H-
      ∑w∈H,(1-(∑g,longAssignedIntervalProbability F hF K m θ w g)-
        (∑j,longAssignedSpokeProbability F hF K m θ w j))|<(A.card:ℝ)^(3/4:ℝ))
    (Kbad Used:SimpleGraph (Fin n)) (absorber:U→Finset (Fin n)) (δ:ℝ) (hU:0<Fintype.card U)
    (Extra:(U→Finset (Fin n))→Finset (Sym2 (Fin n))→Prop)
    (eps α:ℝ) (hK3:3≤K) (hθmax:θ≤1/100) (heps0:0≤eps)
    (hρ₀:0<ρ₀) (hα:0<α) (hlamθ:lam≤θ)
    (hepsAssign:3*eps≤lam*(θ/(100*(K:ℝ)^2)))
    (hαsmall:α/16≤((ρ₀/4)/40000)*θ/1024)
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (hdisj:∀c∈M,∀c'∈M,c≠c'→Disjoint (Q c) (Q c'))
    (hcounts:∀w g,|rawIntervalHubStartCount π d g σ w-
      (n:ℝ)*longAssignedIntervalProbability F hF K m θ w g/(d:ℝ)|<(n:ℝ)^(3/4:ℝ)/(d:ℝ))
    (hsourceCount:LongMatchingSourceCountWitness F hF π d m ℓ θ eps T (M.map q))
    (hExtraDegree:∀occupied Pack,Extra occupied Pack→∀v,(Kbad.degree v:ℝ)≤(α/16)*n),
    LongSelectedAlignedSourceWithLoadAndMatching hU F P π d m ℓ raw t Jret σE H A Kbad Used absorber δ Extra (M.map q) →
    LongSelectedAlignedSourceWithLoadMatchingCapacity hU F P π d m ℓ raw t Jret σE H A Kbad Used absorber δ
      (fun occupied Pack=>Extra occupied Pack ∧ ∀w,
        ((innerRequiredTargets H A (rawReservedSpokeList π d σ)
          (retainedFinalMarkedAt π d σ t Jret) absorber occupied w).card:ℝ)≤(θ/1024)*n) ρ₀ (M.map q) :=by
  obtain ⟨Nt,hT⟩:=first_vortex_source_matching_target_size ε θ ρ₀ lam d hε hθ hθ1 hρhi hεsmall hlam hlam1 hd hspacing
  obtain ⟨Nc,hC⟩:=first_vortex_source_matching_capacity m d hm hd θ hθ
  refine ⟨max Nt (max Nc 1),?_⟩
  intro n K hn hK U _ _ P π Dv mm β Vort hreg hDv hρ hmm σE Del t Jret ℓ raw H A σ R T S hST q Q M F hF a γ ζ hγ ha hγcap hζ hζ0 hmatch hrows hfixed hcolumn Kbad Used absorber δ hU Extra eps α hK3 hθmax heps0 hρ₀ hα hlamθ hepsAssign hαsmall hnoshort hdisj hcounts hsourceCount hExtraDegree hsource
  have ht:=hT n K (le_trans (le_max_left _ _) hn) hK
  have htdec : firstVortexSourceMatchingTargetSizeFin n = firstVortexSourceTargetCapacityFin n := Subsingleton.elim _ _
  have htdecK : firstVortexSourceMatchingTargetSizeFin K = firstVortexSourceTargetCapacityFin K := Subsingleton.elim _ _
  try rw [htdec] at ht
  try rw [htdecK] at ht
  have hsourceTarget:=ht U P π m hm ℓ Dv mm β Vort hreg hDv hρ hmm σE Del t Jret M F hF a γ ζ hγ ha hγcap hζ hζ0 hmatch hrows hfixed hcolumn Kbad Used absorber δ hU Extra hsource
  have hc:=hC n K (by omega) (by omega) hK3
  have hcdec : firstVortexSourceMatchingCapacityFin n = firstVortexSourceTargetCapacityFin n := Subsingleton.elim _ _
  have hcdecK : firstVortexSourceMatchingCapacityFin K = firstVortexSourceTargetCapacityFin K := Subsingleton.elim _ _
  try rw [hcdec] at hc
  try rw [hcdecK] at hc
  apply hc U P π σE hnoshort Del t Jret M F hF eps lam a γ ρ₀ α hθmax heps0 hγ hρ₀ hα hlam hlamθ hepsAssign hspacing ha hγcap hαsmall hdisj hmatch hcounts hsourceCount H A Kbad Used absorber δ hU
    (fun occupied Pack=>Extra occupied Pack ∧ ∀w,
      ((innerRequiredTargets H A (rawReservedSpokeList π d σ) (retainedFinalMarkedAt π d σ t Jret) absorber occupied w).card:ℝ)≤(θ/1024)*n)
  · intro occupied Pack h
    exact hExtraDegree occupied Pack h.1
  · intro occupied Pack h
    exact h.2
  · exact hsourceTarget
end Oberwolfach

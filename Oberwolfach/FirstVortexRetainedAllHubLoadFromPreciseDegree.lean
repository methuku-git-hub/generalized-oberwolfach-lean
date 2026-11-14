module

public import Oberwolfach.FirstVortexRetainedAllHubLoadFromTests

@[expose] public section
/-! The capacity and global degree hypotheses for the all-hub source follow
from a single precise degree estimate, with a capacity parameter independent
of the host margin. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance firstVortexAllHubPreciseDegreeFin (n:ℕ):DecidableEq (Fin n):=selectedAlignedSourceWithLoadFin n

theorem first_vortex_retained_all_hub_load_from_precise_degree
    (ε θ δglobal ρ₀ lam:ℝ) (m d:ℕ) (hm:0<m) (hd:0<d)
    (hε:0<ε) (hθ:0<θ) (hθmax:θ≤1/100) (hδ:0<δglobal) (hθδ:10*θ≤δglobal)
    (hρ₀:0<ρ₀) (hρhi:ρ₀≤1) (hεsmall:ε≤(ρ₀/4)/80000)
    (hlam:0≤lam) (hlam1:lam≤1) (hlamθ:lam≤θ) (hinv:1/(d:ℝ)≤θ/1024):
    ∃N:ℕ,∀n K:ℕ,N≤n→0<n→3≤K→∀(U:Type) [Fintype U] [DecidableEq U]
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n))
    (Dv mm:ℕ) (β:ℝ) (Vort:Vortex U P Dv β ε mm)
    (hreg:P.IsRegularOfDegree Dv) (hDv:0<Dv) (hρ:initialIndexDensity U Dv≤1)
    (σE:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
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
    let Q:=restrictedResourceSet R (Function.Embedding.subtype (·∈S));
    ∀(M:Finset (RestrictedResource R (Function.Embedding.subtype (·∈S))))
    (F:U→SimpleGraph (Fin n)) (hF:∀w,(F w).IsRegularOfDegree 2)
    (eps a γ ζ ρ:ℝ) (heps0:0≤eps) (hγ:0≤γ)
    (ha:a≤lam/(10*(d:ℝ))) (hγcap:γ≤lam/(10*(d:ℝ)))
    (hζ0:0≤ζ) (hζ:ζ≤θ/4096) (hρ0:0≤ρ) (hρscale:ρ≤θ/4096)
    (hscale:max a γ*n≤ρ*A.card)
    (hepsAssign:3*eps≤lam*(θ/(100*(K:ℝ)^2)))
    (hmarg:4/(m:ℝ)≤δglobal/4)
    (hdisj:∀c∈M,∀c'∈M,c≠c'→Disjoint (Q c) (Q c'))
    (hmatch:∀i,((longRawIncidenceSet S i\M.biUnion Q).card:ℝ)≤max (a*n) (γ*(longRawIncidenceSet S i).card))
    (hcounts:∀w g,|rawIntervalHubStartCount π d g σ w-
      (n:ℝ)*longAssignedIntervalProbability F hF K m θ w g/(d:ℝ)|<(n:ℝ)^(3/4:ℝ)/(d:ℝ))
    (hsourceCount:LongMatchingSourceCountWitness F hF π d m ℓ θ eps T (M.map q))
    (hOcc:∀v,((rawIntervalExtendedAnyHubSet π d σ v).card:ℝ)≤4*(Fintype.card U:ℝ)/(m:ℝ)+4*(n:ℝ)^(3/4:ℝ))
    (hrows:RetainedRestrictionGood π d σ false t (fun _:Unit=>Finset.univ) (fun _:Unit=>Finset.univ) ζ Jret)
    (hfixed:∀w,|rawIntervalUnassignedHubCountOn π d σ w A-
      (A.card:ℝ)*(1-(∑g,longAssignedIntervalProbability F hF K m θ w g)-
        (∑j,longAssignedSpokeProbability F hF K m θ w j))|<(n:ℝ)^(3/4:ℝ))
    (hcolumn:∀v,|rawIntervalUnassignedColumnCount π d σ v Finset.univ-
      ∑w:U,(1-(∑g,longAssignedIntervalProbability F hF K m θ w g)-
        (∑j,longAssignedSpokeProbability F hF K m θ w j))|<(n:ℝ)^(3/4:ℝ))
    (Kbad:Finset (Sym2 (Fin n))→SimpleGraph (Fin n)) (Used:SimpleGraph (Fin n))
    (absorber:U→Finset (Fin n)) (δ:ℝ) (hU:0<Fintype.card U)
    (Extra:(U→Finset (Fin n))→Finset (Sym2 (Fin n))→Prop)
    (hprecise:∀occupied Pack,Extra occupied Pack→∀v,((Kbad Pack).degree v:ℝ)≤((((ρ₀/4)/40000)*θ)/1024)*n),
    LongSelectedRetainedSourceDynamicGlobalLoad hU F P π d m ℓ raw t Jret σE H A Kbad Used absorber δ Extra ρ₀ θ δglobal (M.map q) →
    LongSelectedRetainedSourceDynamicAllHubLoad hU F P π d m ℓ raw t Jret σE H A Kbad Used absorber δ Extra ρ₀ θ δglobal (M.map q) :=by
  obtain ⟨N,hN⟩:=first_vortex_retained_all_hub_load_from_tests ε θ δglobal ρ₀ lam m d hm hd
    hε hθ hθmax hδ hθδ hρ₀ hρhi hεsmall hlam hlam1 hlamθ hinv
  refine ⟨N,?_⟩
  intro n K hn hn0 hK U _ _ P π Dv mm β Vort hreg hDv hρ σE hnoshort Del t Jret
    ℓ raw H A σ R T S hST q Q M F hF eps a γ ζ ρ heps0 hγ ha hγcap hζ0 hζ hρ0 hρscale hscale hepsAssign hmarg
    hdisj hmatch hcounts hsourceCount hOcc hrows hfixed hcolumn Kbad Used absorber δ hU Extra hprecise hsource
  let acap:ℝ:=((ρ₀/4)/40000)*θ/64
  have hacap:0<acap:=by dsimp [acap];positivity
  have hacapsmall:acap/16≤((ρ₀/4)/40000)*θ/1024:=by dsimp [acap];ring_nf;exact le_rfl
  have hdegree:∀occupied Pack,Extra occupied Pack→∀v,((Kbad Pack).degree v:ℝ)≤(acap/16)*n:=by
    intro occupied Pack hExtra v
    have hh:=hprecise occupied Pack hExtra v
    dsimp only [acap]
    convert hh using 1 <;> ring
  have ha1:((ρ₀/4)/40000)≤1:=by linarith
  have haθ:((ρ₀/4)/40000)*θ≤θ:=by nlinarith [mul_nonneg (sub_nonneg.mpr ha1) hθ.le]
  have hdegreeGlobal:∀occupied Pack,Extra occupied Pack→∀v,((Kbad Pack).degree v:ℝ)≤δglobal*n/4:=by
    intro occupied Pack hExtra v
    have hh:=hprecise occupied Pack hExtra v
    have hs:((ρ₀/4)/40000)*θ/1024≤δglobal/4:=by linarith
    have hs':=mul_le_mul_of_nonneg_right hs (Nat.cast_nonneg n)
    nlinarith only [hh,hs']
  exact hN n K hn hn0 hK U P π Dv mm β Vort hreg hDv hρ σE hnoshort Del t Jret M F hF
    eps a γ ζ ρ acap heps0 hγ ha hγcap hζ0 hζ hρ0 hρscale hscale hacap hepsAssign hacapsmall hmarg
    hdisj hmatch hcounts hsourceCount hOcc hrows hfixed hcolumn Kbad Used absorber δ hU Extra hdegree hdegreeGlobal hsource
end Oberwolfach

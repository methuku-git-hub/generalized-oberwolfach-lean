module

public import Oberwolfach.PositiveOrdinaryCycleWeights
public import Oberwolfach.AlmostSpanningCyclePacking
public import Oberwolfach.OrdinaryUniformLongSampledAbsorberInputs
public import Oberwolfach.OrdinaryPreparationProbability
public import Oberwolfach.OrdinaryIndexHubBoundFromDensity
public import Oberwolfach.OrdinaryUniformProfilePairProfilesAndInputsJointSmallBeta
public import Oberwolfach.OrdinaryUniformSampledProfileJointSmallBeta
public import Oberwolfach.OrdinaryUniformSampledProfileJointFixedBeta
public import Oberwolfach.OrdinaryUniformSampledProfileExistsFixedBeta
public import Oberwolfach.OrdinaryUniformSampledProfileExists
public import Oberwolfach.OrdinarySampledPropertyToProfiles

@[expose] public section
/-! Choose all error constants before the order threshold, then obtain an
actual sample supplying all two-hub profile inputs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
set_option synthInstance.maxSize 32768
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_uniform_sampled_long_absorber_inputs_from_threshold
    (m d:ℕ) (hm:3≤m) (hd:2≤d) (α pmin smin L ω:ℝ)
    (hα:0<α) (hpmin:0<pmin) (hsmin:0<smin) (hsmin1:smin≤1) (hω:0<ω) (hL:0≤L):
    ∃ a b:ℝ,0<a ∧ 0<b ∧ ∀ β:ℝ,0<β → β≤α*pmin^2*smin^2 → β≤ω*smin^(m+7)/4 → ∀ η:ℝ,0<η →
    ∃ ε:ℝ,0<ε ∧ ∃ N:ℕ,
    ∀ (V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [DecidableEq V] [DecidableEq U],
    N≤Fintype.card V → Fintype.card U≤Fintype.card V → ω*Fintype.card V≤(Fintype.card U:ℝ) →
    ∀ (P F:SimpleGraph V) (π:Equiv.Perm V),
    permutationConflictGraph π (3*d)≤F →
    (∀ x k,0<k→k<2*d+1→(π^k) x≠x) →
    (∀ v,(F.degree v:ℝ)≤L) →
    (∀ v,(cycleThreshold (m+1)+α)*Fintype.card V≤(P.degree v:ℝ)) →
    ∀ D:ℝ,(Fintype.card V:ℝ)/2≤D → D≤2*Fintype.card V →
    (∀ v,|(P.degree v:ℝ)-D|≤ε*Fintype.card V) →
    ∀ (p:ℝ) (hp:pmin≤p) (hp1:p≤1),
    ∀ (q:U→Γ→ℝ) (hq:∀ u g,0≤q u g) (hQ:∀ u,∑ g,q u g≤1/8)
      (s:U→Color→ℝ) (hs:∀ u j,0≤s u j)
      (hS:∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g)) (j:Color),
    (∀ u,smin≤s u j) → (∀ u,s u j≤1) →
    ∀ pH:ℝ,smin≤pH → (∀ u,s u j=pH) →
    ∃ σ:RawWheelOutcome V U Γ Color, ordinarySampledProfileProperty (r:=m+1) P F π d σ pmin smin j β η a b ∧
      Nonempty (OrdinaryCommonCycleProfiles (rawWheelGraph P σ\F) F (rawWheelSpokes π d σ j) (m+1)
        (fun (_:Unit)=>pairedAbsorberTemplate (m+1)) β ((ordinaryLocalCountCoeff m β/2)^(m+2))
          a (4*b/(pmin^(m+1)*(smin*smin)^m)) η) ∧
      (∀ T:Finset V,T.card≤m+7→(∀ v∈T,∀ w∈T,¬F.Adj v w)→
        β*Fintype.card V≤((common Finset.univ T (fun v=>Finset.univ.filter (rawWheelSpokes π d σ j v))).card:ℝ)) := by
  obtain ⟨a,b,ha,hb,Nw,hNw,hweights⟩:=positive_ordinary_fractional_cycle_weights (m+1) (by omega) α hα
  refine ⟨a,b,ha,hb,?_⟩
  intro β hβ hβmax hβhub η hη
  obtain ⟨ε,hε,Nsample,hSample⟩:=ordinary_uniform_sampled_long_absorber_inputs m d hm hd α pmin smin β η a b L ω
    hα hpmin hsmin hsmin1 hω hβ hβmax hβhub hη ha.le hb hL
  refine ⟨ε,hε,max Nw Nsample,?_⟩
  intro V U Γ Color _ _ _ _ _ _ hn hu hlo P F π hF hnoshort hdeg hP D hD hDhi hnear p hp hp1 q hq hQ s hs hS j hslo hshi pH hpH hj
  obtain ⟨weight,hw,he⟩:=hweights V (by omega) P hP
  have hweight:∀ C,0≤weight C:=fun C=>(div_nonneg ha.le (by positivity)).trans (hw C).1
  have he':=ordinary_cycle_incidence_load_adjacency P (m+1) weight he
  have hP':∀ v,(1/2+α)*Fintype.card V≤(P.degree v:ℝ):=by
    intro v
    have hth:=cycleThreshold_half_le (show 3≤m+1 by omega)
    have hcmp:(1/2:ℝ)+α≤cycleThreshold (m+1)+α:=by linarith
    exact (mul_le_mul_of_nonneg_right hcmp (by positivity)).trans (hP v)
  exact hSample V U Γ Color (by omega) hu hlo P F π hF hnoshort weight hweight (fun C=>(hw C).1) (fun C=>(hw C).2)
    hdeg hP' he' D hD hDhi hnear p hp hp1 q hq hQ s hs hS j hslo hshi pH hpH hj
end Oberwolfach

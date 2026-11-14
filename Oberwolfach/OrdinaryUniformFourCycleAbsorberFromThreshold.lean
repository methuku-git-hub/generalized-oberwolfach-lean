module

public import Oberwolfach.OrdinaryFourCycleTripleMargin
public import Oberwolfach.OrdinaryUniformLongSampledAbsorberInputsWithRows
public import Oberwolfach.OrdinaryPositiveHubDensity
public import Oberwolfach.FourSharpThreshold
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

theorem ordinary_uniform_sampled_four_cycle_absorber_inputs_from_threshold
    (d:ℕ) (hd:2≤d) (α pmin smin L ω:ℝ)
    (hα:0<α) (hpmin:0<pmin) (hsmin:0<smin) (hsmin1:smin≤1) (hω:0<ω) (hL:0≤L):
    ∃ a b β:ℝ,0<a ∧ 0<b ∧ 0<β ∧ ∀ η:ℝ,0<η →
    ∃ ε:ℝ,0<ε ∧ ∃ N:ℕ,
    ∀ (V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [DecidableEq V] [DecidableEq U],
    N≤Fintype.card V → Fintype.card U≤Fintype.card V → ω*Fintype.card V≤(Fintype.card U:ℝ) →
    ∀ (P F:SimpleGraph V) (π:Equiv.Perm V),
    permutationConflictGraph π (3*d)≤F →
    (∀ x k,0<k→k<2*d+1→(π^k) x≠x) →
    (∀ v,(F.degree v:ℝ)≤L) →
    (∀ v,(cycleThreshold 4+α)*Fintype.card V≤(P.degree v:ℝ)) →
    ∀ D:ℝ,(Fintype.card V:ℝ)/2≤D → D≤2*Fintype.card V →
    (∀ v,|(P.degree v:ℝ)-D|≤ε*Fintype.card V) →
    ∀ (p:ℝ) (hp:pmin≤p) (hp1:p≤1),
    ∀ (q:U→Γ→ℝ) (hq:∀ u g,0≤q u g) (hQ:∀ u,∑ g,q u g≤1/8)
      (s:U→Color→ℝ) (hs:∀ u j,0≤s u j)
      (hS:∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g)) (j:Color),
    (∀ u,smin≤s u j) → (∀ u,s u j≤1) →
    ∀ pH:ℝ,smin≤pH → (∀ u,s u j=pH) →
    ∃ σ:RawWheelOutcome V U Γ Color, ordinarySampledProfileProperty (r:=4) P F π d σ pmin smin j β η a b ∧
      Nonempty (OrdinaryCommonCycleProfiles (rawWheelGraph P σ\F) F (rawWheelSpokes π d σ j) 4
        (fun (_:Unit)=>pairedAbsorberTemplate 4) β ((ordinaryLocalCountCoeff 3 β/2)^5)
          a (4*b/(pmin^4*(smin*smin)^3)) η) ∧
      (∀ T:Finset V,T.card≤10→(∀ v∈T,∀ w∈T,¬F.Adj v w)→
        β*Fintype.card V≤((common Finset.univ T (fun v=>Finset.univ.filter (rawWheelSpokes π d σ j v))).card:ℝ)) ∧
      (∀ x y z,β*Fintype.card V≤(((rawWheelGraph P σ\F).neighborFinset x∩(rawWheelGraph P σ\F).neighborFinset y∩(rawWheelGraph P σ\F).neighborFinset z).card:ℝ)) := by
  obtain ⟨a,b,ha,hb,Nw,hNw,hweights⟩:=positive_ordinary_fractional_cycle_weights 4 (by omega) α hα
  obtain ⟨β,row,hβ,hrow,hβc,hrowc,hβmax,hβhub,hrowhub,Nmargin,hmargin⟩:=ordinary_four_cycle_triple_margin α pmin smin ω L hα hpmin hsmin hω hL
  refine ⟨a,b,β,ha,hb,hβ,?_⟩
  intro η hη
  obtain ⟨ε,hε,Nsample,hSample⟩:=ordinary_uniform_sampled_long_absorber_inputs_with_rows 3 d (by omega) hd α pmin smin β η a b L ω row
    hα hpmin hsmin hsmin1 hω hrow hrowhub hβ hβmax hβhub hη ha.le hb hL
  refine ⟨ε,hε,max Nw (max Nmargin Nsample),?_⟩
  intro V U Γ Color _ _ _ _ _ _ hn hu hlo P F π hF hnoshort hdeg hP D hD hDhi hnear p hp hp1 q hq hQ s hs hS j hslo hshi pH hpH hj
  obtain ⟨weight,hw,he⟩:=hweights V (by omega) P hP
  have hweight:∀ C,0≤weight C:=fun C=>(div_nonneg ha.le (by positivity)).trans (hw C).1
  have he':=ordinary_cycle_incidence_load_adjacency P 4 weight he
  have hP2:∀ v,(2/3+α)*Fintype.card V≤(P.degree v:ℝ):=by
    intro v
    have hcmp:(2/3:ℝ)+α≤cycleThreshold 4+α:=by linarith [cycleThreshold_four_lower]
    exact (mul_le_mul_of_nonneg_right hcmp (by positivity)).trans (hP v)
  have hP1:∀ v,(1/2+α)*Fintype.card V≤(P.degree v:ℝ):=by
    intro v
    have hcmp:(1/2:ℝ)+α≤(2/3:ℝ)+α:=by norm_num
    exact (mul_le_mul_of_nonneg_right hcmp (by positivity)).trans (hP2 v)
  obtain ⟨σ,hσ,hprofiles,hrows,hhub⟩:=hSample V U Γ Color (by omega) hu hlo P F π hF hnoshort weight hweight
    (fun C=>(hw C).1) (fun C=>(hw C).2) hdeg hP1 he' D hD hDhi hnear p hp hp1 q hq hQ s hs hS j hslo hshi pH hpH hj
  have hn0:0<Fintype.card V:=by omega
  letI:Nonempty U:=ordinary_positive_hub_density_nonempty V U ω hω hn0 hlo
  have hmargin':β*Fintype.card V≤(pmin^3*smin^3)*(3*(min α (1/3)))*Fintype.card V-row*Fintype.card V-3*L:=
    hmargin (Fintype.card V) (by exact_mod_cast (show Nmargin≤Fintype.card V by omega))
  have hthree:=ordinary_four_cycle_triple_neighbourhood P F π d 10 σ p pmin smin s j α (row*Fintype.card V) L β
    (by omega) hα hL hP2 hdeg hpmin hp hp1 hsmin hsmin1 hslo hrows hmargin'
  exact ⟨σ,hσ,hprofiles,hhub,hthree⟩
end Oberwolfach

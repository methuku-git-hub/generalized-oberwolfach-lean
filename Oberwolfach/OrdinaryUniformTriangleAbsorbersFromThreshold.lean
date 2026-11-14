module

public import Oberwolfach.OrdinaryAbsorberSlackChoice
public import Oberwolfach.OrdinaryTriangleAmbientAbsorberFromSampledInputs
public import Oberwolfach.OrdinaryUniformTriangleAbsorberFromThreshold
public import Oberwolfach.OrdinaryLongAmbientAbsorberFromSampledInputs
public import Oberwolfach.OrdinaryUniformFourCycleAbsorberFromThreshold
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

theorem ordinary_uniform_sampled_triangle_absorbers_from_threshold
    (d:ℕ) (hd:2≤d) (α pmin smin L ω:ℝ)
    (hα:0<α) (hpmin:0<pmin) (hsmin:0<smin) (hsmin1:smin≤1) (hω:0<ω) (hL:0≤L):
    ∃ εabs εsample:ℝ,0<εabs ∧ 0<εsample ∧ ∀ m:ℕ,∃ a₀ b₀:ℕ,∀ f:ℕ,∃ N:ℕ,
    ∀ (V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [DecidableEq V] [DecidableEq U],
    N≤Fintype.card V → Fintype.card U≤Fintype.card V → ω*Fintype.card V≤(Fintype.card U:ℝ) →
    ∀ (P F:SimpleGraph V) (π:Equiv.Perm V),
    permutationConflictGraph π (3*d)≤F →
    (∀ x k,0<k→k<2*d+1→(π^k) x≠x) →
    (∀ v,(F.degree v:ℝ)≤L) →
    (∀ v,(cycleThreshold 3+α)*Fintype.card V≤(P.degree v:ℝ)) →
    ∀ D:ℝ,(Fintype.card V:ℝ)/2≤D → D≤2*Fintype.card V →
    (∀ v,|(P.degree v:ℝ)-D|≤εsample*Fintype.card V) →
    ∀ (p:ℝ) (hp:pmin≤p) (hp1:p≤1),
    ∀ (q:U→Γ→ℝ) (hq:∀ u g,0≤q u g) (hQ:∀ u,∑ g,q u g≤1/8)
      (s:U→Color→ℝ) (hs:∀ u j,0≤s u j)
      (hS:∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g)) (j:Color),
    (∀ u,smin≤s u j) → (∀ u,s u j≤1) →
    ∀ pH:ℝ,smin≤pH → (∀ u,s u j=pH) →
    ∃ σ:RawWheelOutcome V U Γ Color,
      ∀ (G:SimpleGraph V) (Hs:V→U→Prop) (A Z W:Finset V) (B₀:Finset U),
      (ordinaryPhysicalGraph G Hs).support.toFinset.card≤m →
      (∀ v,G.degree v=2*(Finset.univ.filter (Hs v)).card) →
      (∀ u,3∣(Finset.univ.filter (fun v=>Hs v u)).card) →
      G≤rawWheelGraph P σ\F → (∀ v u,Hs v u→ rawWheelSpokes π d σ j v u) →
      (∀ u,(∃ v,Hs v u)→u∈B₀) →
      A=Finset.univ\Z → (Z.card:ℝ)≤εabs*Fintype.card V → W.card≤f → (B₀.card:ℝ)≤εabs*Fintype.card V+f →
      ∃ C:Finset (Sym2 V⊕(V×U)),
        IsResourceAbsorber (ordinaryWheelResources (P:=rawWheelGraph P σ\F) (F:=F) (Hbase:=rawWheelSpokes π d σ j) (r:=3))
          (ordinaryHostResources G Hs) C ∧
        C⊆ordinaryHostResources (rawWheelGraph P σ\F) (rawWheelSpokes π d σ j) ∧
        (ordinaryResourceRows C).card≤a₀ ∧ (ordinaryResourceHubs C).card≤b₀ ∧
        ordinaryResourceRows C⊆G.support.toFinset∪A ∧
        (∀ v∈ordinaryResourceRows C,v∈W→v∈G.support.toFinset) ∧
        (∀ u∈ordinaryResourceHubs C,u∈B₀→u∈Finset.univ.filter (fun u=>∃ v,Hs v u)) ∧
        Disjoint C (ordinaryRootResources W B₀) := by
  obtain ⟨a,b,ha,hb,hSample⟩:=ordinary_uniform_sampled_triangle_absorber_inputs_from_threshold d hd α pmin smin L ω hα hpmin hsmin hsmin1 hω hL
  obtain ⟨β,hβ,hβmax,hβhub⟩:=ordinary_triangle_absorber_slack_choice 9 α pmin smin ω hα hpmin hsmin hω
  obtain ⟨η,εabs,hη,hεabs,hεβ,hAbs⟩:=ordinary_triangle_ambient_absorber_from_sampled_inputs β a b pmin smin hβ ha hb hpmin hsmin
  obtain ⟨εsample,hεsample,Nsample,hSample⟩:=hSample β hβ hβmax hβhub η hη
  refine ⟨εabs,εsample,hεabs,hεsample,?_⟩
  intro m
  obtain ⟨a₀,b₀,hAbs⟩:=hAbs m
  refine ⟨a₀,b₀,?_⟩
  intro f
  obtain ⟨Nabs,hAbs⟩:=hAbs f L hL
  refine ⟨max Nsample (max Nabs 1),?_⟩
  intro V U Γ Color _ _ _ _ _ _ hn hu hlo P F π hF hnoshort hdeg hP D hD hDhi hnear p hp hp1 q hq hQ s hs hS j hslo hshi pH hpH hj
  obtain ⟨σ,hσ,hprofiles,hhub⟩:=hSample V U Γ Color (by omega) hu hlo P F π hF hnoshort hdeg hP D hD hDhi hnear p hp hp1 q hq hQ s hs hS j hslo hshi pH hpH hj
  have hn0:0<Fintype.card V:=by omega
  letI:Nonempty U:=ordinary_positive_hub_density_nonempty V U ω hω hn0 hlo
  refine ⟨σ,?_⟩
  intro G Hs A Z W B₀ hm hbal hdiv hG hHs hB₀ hA hZ hW hBsize
  apply hAbs V U Γ Color (by omega) G Hs (rawWheelGraph P σ\F) F (rawWheelSpokes π d σ j) A Z W B₀ P π d σ j rfl rfl
    hm hbal hdiv hG hHs hB₀ hA hZ hW hBsize hdeg
  · exact hhub
  · exact hσ
end Oberwolfach

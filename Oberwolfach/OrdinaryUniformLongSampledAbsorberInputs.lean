module

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

theorem ordinary_uniform_sampled_long_absorber_inputs
    (m d:ℕ) (hm:3≤m) (hd:2≤d) (α pmin smin β η a b L ω:ℝ)
    (hα:0<α) (hpmin:0<pmin) (hsmin:0<smin) (hsmin1:smin≤1)
    (hω:0<ω) (hβ:0<β) (hβmax:β≤α*pmin^2*smin^2) (hβhub:β≤ω*smin^(m+7)/4) (hη:0<η) (ha:0≤a) (hb:0<b) (hL:0≤L):
    ∃ ε:ℝ,0<ε ∧ ∃ N:ℕ,
    ∀ (V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [DecidableEq V] [DecidableEq U],
    N≤Fintype.card V → Fintype.card U≤Fintype.card V → ω*Fintype.card V≤(Fintype.card U:ℝ) →
    ∀ (P F:SimpleGraph V) (π:Equiv.Perm V),
    permutationConflictGraph π (3*d)≤F →
    (∀ x k,0<k→k<2*d+1→(π^k) x≠x) →
    ∀ weight:OrdinaryCycle P (m+1)→ℝ,(∀ C,0≤weight C) →
    (∀ C,a/(Fintype.card V:ℝ)^((m+1)-2)≤weight C) →
    (∀ C,weight C≤b/(Fintype.card V:ℝ)^((m+1)-2)) →
    (∀ v,(F.degree v:ℝ)≤L) →
    (∀ v,(1/2+α)*Fintype.card V≤(P.degree v:ℝ)) →
    (∀ x y,(∑ C,if C.val.val.Adj x y then weight C else 0)=if P.Adj x y then 1 else 0) →
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
  let eh:ℝ:=smin^(m+7)/4
  have heh:0<eh:=by dsimp [eh];positivity
  have hehmax:eh≤smin^(m+7)/2:=by
    dsimp [eh]
    have hh:0≤smin^(m+7):=by positivity
    linarith
  obtain ⟨ε,hε,Nsample,hSample⟩:=ordinary_uniform_sampled_pair_profiles_and_inputs_joint_small_beta m d hm hd
    α pmin smin β η a b L hα hpmin hsmin hsmin1 hβ hβmax hη ha hb hL
  obtain ⟨Nprep,hprep⟩:=ordinary_preparation_probability_exceeds_profile_failure ω eh hω heh d (m+7) hd
  refine ⟨ε,hε,max Nsample Nprep,?_⟩
  intro V U Γ Color _ _ _ _ _ _ hn hu hlo P F π hF hnoshort weight hweight hwlo hwhi hdeg hP he D hD hDhi hnear p hp hp1 q hq hQ s hs hS j hslo hshi pH hpH hj
  let E:RawWheelOutcome V U Γ Color→Prop:=fun σ=>RawOrdinaryRows P π d (m+7) Finset.univ p s j (eh*Fintype.card V) σ ∧
    RawOrdinaryIndices F π d (m+7) pH j (eh*Fintype.card U) σ
  have hE:=hprep V U Γ Color (by omega) hu hlo P F π hF hnoshort p (le_trans hpmin.le hp) hp1 q hq hQ s hs hS j pH hj
  obtain ⟨σ,hEσ,hσ,hprofiles⟩:=hSample V U Γ Color (by omega) hu P F π hF hnoshort weight hweight hwlo hwhi
    hdeg hP he D hD hDhi hnear p hp hp1 q hq hQ s hs hS j hslo hshi E hE
  have hhub:=ordinary_index_event_absorber_hub_bound_from_density F π d (m+7) pH j ω smin β eh σ
    hω hsmin hsmin1 hpH hβ.le hβhub heh.le hehmax hlo hEσ.2
  exact ⟨σ,hσ,hprofiles,hhub⟩
end Oberwolfach

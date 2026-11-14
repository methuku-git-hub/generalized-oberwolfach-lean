module

public import Oberwolfach.OrdinaryUniformSampledTriangleExistsFixedBeta
public import Oberwolfach.OrdinaryUniformSampledTriangleExists
public import Oberwolfach.OrdinaryTrianglePropertyToProfiles

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

theorem ordinary_uniform_sampled_triangle_pair_profiles_exists_fixed_beta
    (d:ℕ) (hd:2≤d) (α pmin smin η a b L:ℝ)
    (hα:0<α) (hpmin:0<pmin) (hsmin:0<smin) (hsmin1:smin≤1)
    (hη:0<η) (ha:0≤a) (hb:0<b) (hL:0≤L):
    let β:=2*(min α (1/4))*pmin^4*smin^4;
    ∃ ε:ℝ,0<ε ∧ ∃ N:ℕ,
    ∀ (V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [DecidableEq V] [DecidableEq U],
    N≤Fintype.card V → Fintype.card U≤Fintype.card V →
    ∀ (P F:SimpleGraph V) (π:Equiv.Perm V),
    permutationConflictGraph π (3*d)≤F →
    (∀ x k,0<k→k<2*d+1→(π^k) x≠x) →
    ∀ weight:OrdinaryCycle P 3→ℝ,(∀ C,0≤weight C) →
    (∀ C,a/(Fintype.card V:ℝ)≤weight C) →
    (∀ C,weight C≤b/(Fintype.card V:ℝ)) →
    (∀ v,(F.degree v:ℝ)≤L) →
    (∀ v,(3/4+α)*Fintype.card V≤(P.degree v:ℝ)) →
    (∀ x y,(∑ C,if C.val.val.Adj x y then weight C else 0)=if P.Adj x y then 1 else 0) →
    ∀ D:ℝ,(Fintype.card V:ℝ)/2≤D → D≤2*Fintype.card V →
    (∀ v,|(P.degree v:ℝ)-D|≤ε*Fintype.card V) →
    ∀ p:ℝ,pmin≤p → p≤1 →
    ∀ (q:U→Γ→ℝ) (hq:∀ u g,0≤q u g) (hQ:∀ u,∑ g,q u g≤1/8)
      (s:U→Color→ℝ) (hs:∀ u j,0≤s u j)
      (hS:∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g)) (j:Color),
    (∀ u,smin≤s u j) → (∀ u,s u j≤1) →
    ∃ σ:RawWheelOutcome V U Γ Color,
      Nonempty (OrdinaryCommonCycleProfiles (rawWheelGraph P σ\F) F (rawWheelSpokes π d σ j) 3
        (fun (_:Unit)=>pairedAbsorberTemplate 3) β ((ordinaryLocalCountCoeff 2 β/2)^4)
          a (4*b/(pmin^3*(smin*smin)^2)) η) := by
  intro β
  have hβ:0<β:=by
    have hx:0<min α (1/4:ℝ):=lt_min hα (by norm_num)
    dsimp [β];positivity
  obtain ⟨ε,hε,Nsample,hSample⟩:=ordinary_uniform_sampled_triangle_property_exists_fixed_beta d hd
    α pmin smin η a b L hα hpmin hsmin hsmin1 hη ha hb hL
  obtain ⟨Nprofile,hProfile⟩:=ordinary_triangle_property_to_pair_profiles β a b η L pmin smin hβ hL
  refine ⟨ε,hε,max Nsample Nprofile,?_⟩
  intro V U Γ Color _ _ _ _ _ _ hn hu P F π hF hnoshort weight hweight hwlo hwhi hdeg hP he D hD hDhi hnear p hp hp1 q hq hQ s hs hS j hslo hshi
  obtain ⟨σ,hσ⟩:=hSample V U Γ Color (by omega) hu P F π hF hnoshort weight hweight hwlo hwhi
    hdeg hP he D hD hDhi hnear p hp hp1 q hq hQ s hs hS j hslo hshi
  exact ⟨σ,hProfile V U Γ Color (by omega) P F π d σ j hdeg hσ⟩
end Oberwolfach

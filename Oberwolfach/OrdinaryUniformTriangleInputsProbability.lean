module

public import Oberwolfach.OrdinaryUniformTriangleInputsWithExtraEvent
public import Oberwolfach.FiniteHighEventsCommon

@[expose] public section
/-! High-probability form of the ordinary triangle preparation inputs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
set_option synthInstance.maxSize 32768
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_uniform_sampled_triangle_inputs_probability
    (d:ℕ) (hd:2≤d) (α pmin smin β η a b L ω:ℝ)
    (hα:0<α) (hpmin:0<pmin) (hsmin:0<smin) (hsmin1:smin≤1)
    (hω:0<ω) (hβ:0<β) (hβmax:β≤2*(min α (1/4))*pmin^4*smin^4) (hβhub:β≤ω*smin^(9)/4) (hη:0<η) (ha:0≤a) (hb:0<b) (hL:0≤L):
    ∃ ε:ℝ,0<ε ∧ ∃ N:ℕ,
    ∀ (V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [DecidableEq V] [DecidableEq U],
    N≤Fintype.card V → Fintype.card U≤Fintype.card V → ω*Fintype.card V≤(Fintype.card U:ℝ) →
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
    ∀ (p:ℝ) (hp:pmin≤p) (hp1:p≤1),
    ∀ (q:U→Γ→ℝ) (hq:∀ u g,0≤q u g) (hQ:∀ u,∑ g,q u g≤1/8)
      (s:U→Color→ℝ) (hs:∀ u j,0≤s u j)
      (hS:∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g)) (j:Color),
    (∀ u,smin≤s u j) → (∀ u,s u j≤1) →
    ∀ pH:ℝ,smin≤pH → (∀ u,s u j=pH) →
    let μ:=FiniteLaw.pi (rawWheelLaw (fun _ : Sym2 V=>p) (fun _=>le_trans (le_of_lt hpmin) hp) (fun _=>hp1) d hd q hq hQ s hs hS);
    1-(1/(Fintype.card V:ℝ)+2/(Fintype.card V:ℝ)^2) ≤ μ.probability
      (fun σ => ordinarySampledTriangleProfileProperty P F π d σ pmin smin j β η a b ∧
      Nonempty (OrdinaryCommonCycleProfiles (rawWheelGraph P σ\F) F (rawWheelSpokes π d σ j) 3
        (fun (_:Unit)=>pairedAbsorberTemplate 3) β ((ordinaryLocalCountCoeff 2 β/2)^4)
          a (4*b/(pmin^3*(smin*smin)^2)) η) ∧
      (∀ T:Finset V,T.card≤9→(∀ v∈T,∀ w∈T,¬F.Adj v w)→
        β*Fintype.card V≤((common Finset.univ T (fun v=>Finset.univ.filter (rawWheelSpokes π d σ j v))).card:ℝ))) := by
  obtain ⟨ε,hε,N,h⟩:=ordinary_uniform_sampled_triangle_inputs_with_extra_event d hd
    α pmin smin β η a b L ω hα hpmin hsmin hsmin1 hω hβ hβmax hβhub hη ha hb hL
  refine ⟨ε,hε,N,?_⟩
  intro V U Γ Color _ _ _ _ _ _ hn hu hlo P F π hF hnoshort weight hweight hwlo hwhi
    hdeg hP he D hD hDhi hnear p hp hp1 q hq hQ s hs hS j hslo hshi pH hpH hj μ
  let Good : RawWheelOutcome V U Γ Color → Prop := fun σ => ordinarySampledTriangleProfileProperty P F π d σ pmin smin j β η a b ∧
      Nonempty (OrdinaryCommonCycleProfiles (rawWheelGraph P σ\F) F (rawWheelSpokes π d σ j) 3
        (fun (_:Unit)=>pairedAbsorberTemplate 3) β ((ordinaryLocalCountCoeff 2 β/2)^4)
          a (4*b/(pmin^3*(smin*smin)^2)) η) ∧
      (∀ T:Finset V,T.card≤9→(∀ v∈T,∀ w∈T,¬F.Adj v w)→
        β*Fintype.card V≤((common Finset.univ T (fun v=>Finset.univ.filter (rawWheelSpokes π d σ j v))).card:ℝ))
  have hc:=finiteLaw_probability_compl μ Good
  have hbad : μ.probability (fun σ=>¬Good σ) ≤ 1/(Fintype.card V:ℝ)+2/(Fintype.card V:ℝ)^2 := by
    by_contra hnot
    have hprob : 1/(Fintype.card V:ℝ)+2/(Fintype.card V:ℝ)^2 < μ.probability (fun σ=>¬Good σ) := by linarith
    obtain ⟨σ,hσbad,hσ,hprof,hhub⟩:=h V U Γ Color hn hu hlo P F π hF hnoshort weight hweight hwlo hwhi
      hdeg hP he D hD hDhi hnear p hp hp1 q hq hQ s hs hS j hslo hshi pH hpH hj
      (fun σ=>¬Good σ) hprob
    exact hσbad ⟨hσ,hprof,hhub⟩
  change 1-(1/(Fintype.card V:ℝ)+2/(Fintype.card V:ℝ)^2) ≤ μ.probability Good
  linarith
end Oberwolfach

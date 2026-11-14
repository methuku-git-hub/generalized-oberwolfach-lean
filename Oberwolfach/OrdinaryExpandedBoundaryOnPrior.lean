module

public import Oberwolfach.ExpandedGlobalBoundaryFailure
public import Oberwolfach.CommonEvents

@[expose] public section
/-! Add the global start/end boundary estimate to any prior event of the
same expanded experiment, with an arbitrary dependent continuation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_expanded_boundary_on_prior
    (d:ℕ) (hd:2≤d) (χ:ℝ) (hχ:0<χ):
    ∃N:ℕ,∀n:ℕ,N≤n→∀(U:Type) [Fintype U] [DecidableEq U],
    0<Fintype.card U→Fintype.card U≤n→
    ∀(π:Equiv.Perm (Fin n)) (p k p₂ k₂ u:ℝ)
      (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u) (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
      (q:U→Bool→ℝ) (hq:∀w g,0≤q w g) (hQ:∀w,∑g,q w g≤1/8)
      (s:U→Bool→ℝ) (hs:∀w j,0≤s w j) (hS:∀w,∑j,s w j≤ intervalUncoveredProbability d (∑g,q w g)),
    (∀x l,0<l→l<2*d+1→(π^l) x≠x)→
    ∀{R:(∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)→Type}
      [∀ω,Fintype (R ω)] (ν:∀ω,FiniteLaw (R ω))
      (E:(Σω:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e,R ω)→Prop) (εE:ℝ),
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=Fin n) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS);
    1-εE≤(μ.sigma ν).probability E→
    1-(εE+χ)≤(μ.sigma ν).probability (fun z=>E z ∧ ∀v,
      ((rawIntervalBoundaryHubSet π d (fun e=>z.1 (Sum.inr e)) Finset.univ v).card:ℝ)≤
        4*(Fintype.card U:ℝ)/d+4*(n:ℝ)^(3/4:ℝ)) :=by
  obtain ⟨N,hN⟩:=expanded_global_boundary_arbitrary_failure d hd χ hχ
  refine ⟨N,?_⟩
  intro n hn U _ _ hU hUn π p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum q hq hQ s hs hS hnoshort R _ ν E εE μ hE
  let Test:=fun ω:(∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)=>∀v,
    ((rawIntervalBoundaryHubSet π d (fun e=>ω (Sum.inr e)) Finset.univ v).card:ℝ)≤
      4*(Fintype.card U:ℝ)/d+4*(n:ℝ)^(3/4:ℝ)
  have hraw:=hN (Fin n) (by simpa using hn) U Bool hU (by simpa using hUn) π p k p₂ k₂ u
    hp hk hp₂ hk₂ hu hsum q hq hQ s hs hS hnoshort (fun _=>Bool) (fun _=>FiniteLaw.fairCoin)
  have hraw':1-χ≤(μ.sigma (fun _=>FiniteLaw.fairCoin)).probability (fun z=>Test z.1):=by
    simp only [Finset.card_univ,Fintype.card_fin] at hraw
    convert hraw using 1 <;> (try simp only [Test]) <;> congr! 8 <;> exact Subsingleton.elim _ _
  have hbase:1-χ≤μ.probability Test:=by
    rw [finiteLaw_sigma_first_probability] at hraw'
    exact hraw' 
  have htest:1-χ≤(μ.sigma ν).probability (fun z=>Test z.1):=by
    rw [finiteLaw_sigma_first_probability]
    exact hbase
  have hh:=finiteLaw_good_intersection (μ.sigma ν) E (fun z=>Test z.1) χ htest
  linarith [hE]
end Oberwolfach

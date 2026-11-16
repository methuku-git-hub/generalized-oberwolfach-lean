module

public import Oberwolfach.OrdinaryReservedTestsOnPrior
public import Oberwolfach.OrdinaryReservedCompletionTests
public import Oberwolfach.ExpandedSelectedTwoPathsAnyStage

@[expose] public section
/-! Add all selected reserved-completion tests to an arbitrary prior event
on the same expanded sample, with an arbitrary dependent continuation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

set_option backward.isDefEq.respectTransparency true in
theorem ordinary_reserved_completion_tests_on_prior
    (d:ℕ) (hd:2≤d) (smin χnbr χpair χpath:ℝ)
    (hsmin:0≤smin) (hχnbr:0<χnbr) (hχpair:0<χpair) (hχpath:0<χpath):
    ∃N:ℕ,∀n:ℕ,N≤n→∀(U:Type) [Fintype U] [DecidableEq U],
    0<Fintype.card U→Fintype.card U≤n→
    ∀(P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (p k p₂ k₂ u:ℝ)
    (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u) (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
    (q:U→Bool→ℝ) (hq:∀w g,0≤q w g) (hQ:∀w,∑g,q w g≤1/8)
    (s:U→Bool→ℝ) (hs:∀w j,0≤s w j) (hS:∀w,∑j,s w j≤ intervalUncoveredProbability d (∑g,q w g))
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x) (hsl:∀w,smin≤s w false)
    {R:(∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)→Type}
    [∀ω,Fintype (R ω)] (ν:∀ω,FiniteLaw (R ω))
    (E:(Σω:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e,R ω)→Prop) (εE:ℝ),
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=Fin n) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS);
    1-εE≤(μ.sigma ν).probability E→
    1-(((εE+χnbr)+χpair)+χpath)≤(μ.sigma ν).probability (fun z=>E z ∧ OrdinaryReservedCompletionTests P π d p smin s z.1) :=by
  obtain ⟨Nres,hres⟩:=ordinary_reserved_tests_on_prior d hd smin χnbr χpair hsmin hχnbr hχpair
  obtain ⟨Npath,hpath⟩:=expanded_selected_two_paths_any_stage d hd χpath hχpath
  refine ⟨max Nres Npath,?_⟩
  intro n hn U _ _ hU hUn P π p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum q hq hQ s hs hS hnoshort hsl R _ ν E εE μ hE
  have hr:=hres n (by omega) U hU hUn P π p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum q hq hQ s hs hS hnoshort hsl ν E εE hE
  have hp':=hpath (Fin n) U Bool Bool (by simpa using (show Npath≤n by omega)) P π p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum q hq hQ s hs hS ν
  simp only [Fintype.card_fin] at hp'
  let Test:=fun z:(Σω:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e,R ω)=>
    ∀x y,x≠y→((P.neighborFinset x∩P.neighborFinset y).card:ℝ)*p^2-(n:ℝ)^(3/4:ℝ)-
      2*(2*((3*d:ℕ):ℝ)+1)≤((Finset.univ.filter (fun v=>
        0<markedPhysicalRim P π (3*d) (fun e=>markedExpandedPhysicalCollapse (z.1 (Sum.inl e))) false x v ∧
        0<markedPhysicalRim P π (3*d) (fun e=>markedExpandedPhysicalCollapse (z.1 (Sum.inl e))) false v y)).card:ℝ)
  have hp'':1-χpath≤(μ.sigma ν).probability Test:=by
    convert hp' using 1 <;> (try simp only [Test]) <;> congr! 20 <;> (try exact Subsingleton.elim _ _) <;> (try {ext w; simp; congr! 20; exact Subsingleton.elim _ _})
  have hh:=finiteLaw_intersection_lower (μ.sigma ν) _ Test ((εE+χnbr)+χpair) χpath (by linarith only [hr]) hp''
  have heq:1-(((εE+χnbr)+χpair)+χpath)=1-((εE+χnbr)+χpair)-χpath:=by ring
  rw [heq]
  apply hh.trans
  apply finiteLaw_probability_mono
  intro z hz
  exact ⟨hz.1.1.1,hz.2,hz.1.1.2,hz.1.2⟩
end Oberwolfach

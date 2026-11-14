module

public import Oberwolfach.RawReservedSelectedNeighbourTests
public import Oberwolfach.RawExpandedReservedPairsProbability
public import Oberwolfach.FiniteSigmaSameFirstEvent
public import Oberwolfach.FiniteLawIntersectionLower

@[expose] public section
/-! The selected reserved-spoke pair and neighbourhood tests can be added to
any earlier event on the same expanded sample and dependent continuation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_reserved_tests_on_prior
    (d:ℕ) (hd:2≤d) (smin χnbr χpair:ℝ)
    (hsmin:0≤smin) (hχnbr:0<χnbr) (hχpair:0<χpair):
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
    1-((εE+χnbr)+χpair)≤(μ.sigma ν).probability (fun z=>
      (E z ∧ ∀w i,|rawIntervalReservedLabelHubCountOn π d (fun e=>z.1 (Sum.inr e)) w false
        (rawSelectedNeighbourTestSet P π d (fun e=>z.1 (Sum.inl e)) i)-
        (rawSelectedNeighbourTestSet P π d (fun e=>z.1 (Sum.inl e)) i).card*s w false|<(n:ℝ)^(3/4:ℝ)) ∧
      ∀x y,x≠y→(5/8:ℝ)*smin^2*Fintype.card U-(n:ℝ)^(3/4:ℝ)≤
        (((Finset.univ:Finset U).filter (fun w=>rawIntervalFamilyState π d (fun e=>z.1 (Sum.inr e)) (x,w)=some (Sum.inr false) ∧
          rawIntervalFamilyState π d (fun e=>z.1 (Sum.inr e)) (y,w)=some (Sum.inr false))).card:ℝ)) :=by
  obtain ⟨Nn,hNn⟩:=raw_reserved_selected_neighbour_tests_high_probability d hd χnbr hχnbr
  obtain ⟨Np,hNp⟩:=raw_expanded_reserved_pairs_high_probability d hd smin χpair hsmin hχpair
  refine ⟨max Nn Np,?_⟩
  intro n hn U _ _ hU hUn P π p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum q hq hQ s hs hS hnoshort hsl R _ ν E εE μ hE
  let Nbr:=fun ω:(∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)=>
    ∀w i,|rawIntervalReservedLabelHubCountOn π d (fun e=>ω (Sum.inr e)) w false
      (rawSelectedNeighbourTestSet P π d (fun e=>ω (Sum.inl e)) i)-
      (rawSelectedNeighbourTestSet P π d (fun e=>ω (Sum.inl e)) i).card*s w false|<(n:ℝ)^(3/4:ℝ)
  let Pair:=fun ω:(∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)=>
    ∀x y,x≠y→(5/8:ℝ)*smin^2*Fintype.card U-(n:ℝ)^(3/4:ℝ)≤
      (((Finset.univ:Finset U).filter (fun w=>rawIntervalFamilyState π d (fun e=>ω (Sum.inr e)) (x,w)=some (Sum.inr false) ∧
        rawIntervalFamilyState π d (fun e=>ω (Sum.inr e)) (y,w)=some (Sum.inr false))).card:ℝ)
  let νunit:=fun (_:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)=>FiniteLaw.uniform Unit
  have hnbr:1-χnbr≤(μ.sigma νunit).probability (fun z=>Nbr z.1):=by
    have hh:=hNn (Fin n) (by simpa using (show Nn≤n by omega)) U Bool Bool (by simpa using hUn) false P π p k p₂ k₂ u
      hp hk hp₂ hk₂ hu hsum q hq hQ s hs hS hnoshort (fun _=>Unit) (fun _=>FiniteLaw.uniform Unit)
    simp only [Fintype.card_fin] at hh
    convert hh using 1 <;> (try simp only [Nbr]) <;> congr! 8 <;> exact Subsingleton.elim _ _
  have hpair:1-χpair≤(μ.sigma νunit).probability (fun z=>Pair z.1):=by
    have hh:=hNp (Fin n) (by simpa using (show Np≤n by omega)) U Bool Bool hU (by simpa using hUn) π p k p₂ k₂ u
      hp hk hp₂ hk₂ hu hsum q hq hQ s hs hS hnoshort false hsl (fun _=>Unit) (fun _=>FiniteLaw.uniform Unit)
    simp only [Fintype.card_fin] at hh
    convert hh using 1 <;> (try simp only [Pair]) <;> congr! 8 <;> (try exact Subsingleton.elim _ _) <;> ext w <;> simp <;> congr! 12 <;> exact Subsingleton.elim _ _
  rw [finiteLaw_sigma_same_first_event μ νunit ν Nbr] at hnbr
  rw [finiteLaw_sigma_same_first_event μ νunit ν Pair] at hpair
  have hfirst:=finiteLaw_intersection_lower (μ.sigma ν) E (fun z=>Nbr z.1) εE χnbr hE hnbr
  have hboth:=finiteLaw_intersection_lower (μ.sigma ν) (fun z=>E z ∧ Nbr z.1) (fun z=>Pair z.1)
    (εE+χnbr) χpair (by linarith only [hfirst]) hpair
  simpa only [Nbr,Pair,sub_add_eq_sub_sub] using hboth
end Oberwolfach

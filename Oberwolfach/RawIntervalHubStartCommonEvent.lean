module

public import Oberwolfach.MarkedExpandedStartCommonEvent
public import Oberwolfach.RawIntervalHubStartHighProbability
public import Oberwolfach.MarkedExpandedStartHighProbability
public import Oberwolfach.MarkedExpandedDegreeStrong
public import Oberwolfach.MarkedExpandedTwoPathEvent
public import Oberwolfach.MarkedExpandedRawCommonEvent

@[expose] public section
/-! The colour-degree event is available simultaneously with any selected
retained event of probability at least 7/10, without assuming the former. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem raw_expanded_marked_selected_degrees_paths_and_interval_counts (d:ℕ) (hd:2≤d) :
    ∃ N:ℕ,∀ (V:Type) [Fintype V] [LinearOrder V],
    N≤Fintype.card V→∀ (U Γ Color:Type) [Fintype U] [Fintype Γ] [Fintype Color] [DecidableEq U]
    (hm:0<Fintype.card U) (hmn:Fintype.card U≤Fintype.card V) (hΓ:Fintype.card Γ≤2)
    (G Z T:SimpleGraph V) (hTG:T≤G) (π:Equiv.Perm V)
    (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
    (hnoshort:∀ x l,0<l→l<2*d+1→(π^l) x≠x) (q:U→Γ→ℝ) (hq:∀ u g,0≤q u g) (hQ:∀ u,∑ g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀ u j,0≤s u j) (hS:∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
    (F:RawMarkedOutcome V U Γ Color→Type) [∀ a,Fintype (F a)] (ν:∀ a,FiniteLaw (F a)) (E:(Σ a,F a)→Prop),
    (7:ℝ)/10≤((FiniteLaw.pi (rawMarkedWheelLaw (V:=V) p k hp hk (by linarith) d hd q hq hQ s hs hS)).sigma ν).probability E→
    let ρ:=markedExpandedPhysicalProbability p k p₂ k₂ u
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS)
    let f:=fun (ω:∀ e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e) e=>rawExpandedMarkedCollapse e (ω e)
    ∃ z,0<(μ.sigma (fun ω=>ν (f ω))).mass z ∧ E ⟨f z.1,z.2⟩ ∧
      expandedPhysicalDegreeGood G Z ρ (fun e=>z.1 (Sum.inl e)) ∧
      (∀ x y,x≠y→|(eligibleTwoPathCount T (sampledColourOrientation G (fun e=>markedExpandedClass (z.1 (Sum.inl e))) 0) x y:ℝ)-
        ((T.neighborFinset x∩T.neighborFinset y).card:ℝ)*((2*p+2*k+2*p₂+2*k₂+u)/2)^2|<(Fintype.card V:ℝ)^(3/5:ℝ)) ∧
      (∀ g a,|((rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) g a).card:ℝ)-(∑ u,q u g/(d:ℝ))|<(Fintype.card V:ℝ)^(3/5:ℝ)) ∧
      (∀ u g,|rawIntervalHubStartCount π d g (fun e=>z.1 (Sum.inr e)) u-(Fintype.card V:ℝ)*q u g/d|<
        (Fintype.card V:ℝ)^(3/4:ℝ)/d) := by
  obtain ⟨ND,hD⟩:=raw_expanded_marked_colour_degrees_999
  obtain ⟨NT,hT⟩:=raw_expanded_marked_class_two_paths_highProbability
  obtain ⟨NS,hSstart⟩:=raw_expanded_starts_highProbability
  obtain ⟨NH,hH⟩:=raw_expanded_hub_starts_highProbability d hd
  refine ⟨max (max (max ND NT) NS) NH,?_⟩
  intro V _ _ hn U Γ Color _ _ _ _ hm hmn hΓ G Z T hTG π p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum hnoshort q hq hQ s hs hS F _ ν E hE ρ μ f
  let Dgood:=fun z:(Σ ω:(∀ e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e),F (f ω))=>
    expandedPhysicalDegreeGood G Z ρ (fun e=>z.1 (Sum.inl e))
  let Tgood:=fun z:(Σ ω:(∀ e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e),F (f ω))=>
    ∀ x y,x≠y→|(eligibleTwoPathCount T (sampledColourOrientation G (fun e=>markedExpandedClass (z.1 (Sum.inl e))) 0) x y:ℝ)-
        ((T.neighborFinset x∩T.neighborFinset y).card:ℝ)*((2*p+2*k+2*p₂+2*k₂+u)/2)^2|<(Fintype.card V:ℝ)^(3/5:ℝ)
  let Sgood:=fun z:(Σ ω:(∀ e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e),F (f ω))=>
    ∀ g a,|((rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) g a).card:ℝ)-(∑ u,q u g/(d:ℝ))|<(Fintype.card V:ℝ)^(3/5:ℝ)
  let Hgood:=fun z:(Σ ω:(∀ e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e),F (f ω))=>
    ∀ u g,|rawIntervalHubStartCount π d g (fun e=>z.1 (Sum.inr e)) u-(Fintype.card V:ℝ)*q u g/d|<
      (Fintype.card V:ℝ)^(3/4:ℝ)/d
  let law:=μ.sigma (fun ω=>ν (f ω))
  have hOld:max (max ND NT) NS≤Fintype.card V:=le_trans (le_max_left _ _) hn
  have hDP:(999:ℝ)/1000≤law.probability Dgood:=
    hD V (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hOld)) U Γ Color G Z p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS F ν
  have hTP:(999:ℝ)/1000≤law.probability Tgood:=
    hT V (le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hOld)) U Γ Color G T hTG p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS F ν
  have hSP:(999:ℝ)/1000≤law.probability Sgood:=
    hSstart V (le_trans (le_max_right _ _) hOld) U Γ Color hm hmn hΓ π d hd p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum q hq hQ s hs hS hnoshort F ν
  have hHP:(999:ℝ)/1000≤law.probability Hgood:=
    hH V (le_trans (le_max_right _ _) hn) U Γ Color hmn hΓ π p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum q hq hQ s hs hS hnoshort F ν
  have hTP':1-(1:ℝ)/1000≤law.probability Tgood:=by linarith
  have hSP':1-(1:ℝ)/1000≤law.probability Sgood:=by linarith
  have hHP':1-(1:ℝ)/1000≤law.probability Hgood:=by linarith
  have hboth:=finiteLaw_good_intersection law Dgood Tgood (1/1000) hTP'
  have hthree:=finiteLaw_good_intersection law (fun z=>Dgood z ∧ Tgood z) Sgood (1/1000) hSP'
  have hfour:=finiteLaw_good_intersection law (fun z=>(Dgood z ∧ Tgood z) ∧ Sgood z) Hgood (1/1000) hHP'
  have hExtra:(99:ℝ)/100≤law.probability (fun z=>((Dgood z ∧ Tgood z) ∧ Sgood z) ∧ Hgood z):=by linarith only [hDP,hboth,hthree,hfour]
  obtain ⟨z,hz,hE',⟨⟨⟨hDz,hTz⟩,hSz⟩,hHz⟩⟩:=raw_expanded_marked_retained_common_event p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS F ν E
    (fun z=>((Dgood z ∧ Tgood z) ∧ Sgood z) ∧ Hgood z) hE hExtra
  exact ⟨z,hz,hE',hDz,hTz,hSz,hHz⟩
end Oberwolfach

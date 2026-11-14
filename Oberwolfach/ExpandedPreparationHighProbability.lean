module

public import Oberwolfach.RawIntervalHubStartCommonEvent
public import Oberwolfach.RawIntervalUnassignedHighProbability
public import Oberwolfach.ExpandedUnassignedRimHighProbability
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

theorem raw_expanded_preparation_basic_plus_extra_highProbability (d:ℕ) (hd:2≤d) :
    ∃ N:ℕ,∀ (V:Type) [Fintype V] [LinearOrder V],
    N≤Fintype.card V→∀ (U Γ Color:Type) [Fintype U] [Fintype Γ] [Fintype Color] [DecidableEq U]
    (hm:0<Fintype.card U) (hmn:Fintype.card U≤Fintype.card V) (hΓ:Fintype.card Γ≤2)
    (G Z T:SimpleGraph V) (hTG:T≤G) (π:Equiv.Perm V) (I:Finset V) (J:Finset U) (hJ:J.Nonempty)
    (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
    (hnoshort:∀ x l,0<l→l<2*d+1→(π^l) x≠x) (q:U→Γ→ℝ) (hq:∀ u g,0≤q u g) (hQ:∀ u,∑ g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀ u j,0≤s u j) (hS:∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
    (F:RawMarkedOutcome V U Γ Color→Type) [∀ a,Fintype (F a)] (ν:∀ a,FiniteLaw (F a))
    (Extra:(Σ ω:(∀ e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e),
      F (fun e=>rawExpandedMarkedCollapse e (ω e)))→Prop),
    let ρ:=markedExpandedPhysicalProbability p k p₂ k₂ u
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS)
    let f:=fun (ω:∀ e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e) e=>rawExpandedMarkedCollapse e (ω e)
    (999:ℝ)/1000≤(μ.sigma (fun ω=>ν (f ω))).probability Extra→
    (99:ℝ)/100≤(μ.sigma (fun ω=>ν (f ω))).probability (fun z=>
      expandedPhysicalDegreeGood G Z ρ (fun e=>z.1 (Sum.inl e)) ∧
      (∀ x y,x≠y→|(eligibleTwoPathCount T (sampledColourOrientation G (fun e=>markedExpandedClass (z.1 (Sum.inl e))) 0) x y:ℝ)-
        ((T.neighborFinset x∩T.neighborFinset y).card:ℝ)*((2*p+2*k+2*p₂+2*k₂+u)/2)^2|<(Fintype.card V:ℝ)^(3/5:ℝ)) ∧
      (∀ g a,|((rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) g a).card:ℝ)-(∑ u,q u g/(d:ℝ))|<(Fintype.card V:ℝ)^(3/5:ℝ)) ∧
      (∀ u g,|rawIntervalHubStartCount π d g (fun e=>z.1 (Sum.inr e)) u-(Fintype.card V:ℝ)*q u g/d|<
        (Fintype.card V:ℝ)^(3/4:ℝ)/d) ∧
      ((∀ w,|rawIntervalUnassignedHubCountOn π d (fun e=>z.1 (Sum.inr e)) w I-(I.card:ℝ)*(1-(∑ g,q w g)-(∑ j,s w j))|<(Fintype.card V:ℝ)^(3/4:ℝ)) ∧
       (∀ v,|rawIntervalUnassignedColumnCount π d (fun e=>z.1 (Sum.inr e)) v J-∑ w∈J,(1-(∑ g,q w g)-(∑ j,s w j))|<(Fintype.card V:ℝ)^(3/4:ℝ))) ∧
      ((∀ w,|rawIntervalUnassignedHubCountOn π d (fun e=>z.1 (Sum.inr e)) w Finset.univ-(Fintype.card V:ℝ)*(1-(∑ g,q w g)-(∑ j,s w j))|<(Fintype.card V:ℝ)^(3/4:ℝ)) ∧
       (∀ v,|rawIntervalUnassignedColumnCount π d (fun e=>z.1 (Sum.inr e)) v Finset.univ-∑ w,(1-(∑ g,q w g)-(∑ j,s w j))|<(Fintype.card V:ℝ)^(3/4:ℝ))) ∧
      (∀ x,|(((G.neighborFinset x∩I).filter (fun y=>(z.1 (Sum.inl s(x,y))).1=4)).card:ℝ)-u*(G.neighborFinset x∩I).card|<(Fintype.card V:ℝ)^(3/4:ℝ)) ∧ Extra z) := by
  obtain ⟨ND,hD⟩:=raw_expanded_marked_colour_degrees_999
  obtain ⟨NT,hT⟩:=raw_expanded_marked_class_two_paths_highProbability
  obtain ⟨NS,hSstart⟩:=raw_expanded_starts_highProbability
  obtain ⟨NH,hH⟩:=raw_expanded_hub_starts_highProbability d hd
  obtain ⟨NU,hU⟩:=raw_expanded_unassigned_fixed_domains_highProbability d hd
  obtain ⟨NR,hR⟩:=raw_expanded_unassigned_rim_degree_highProbability
  refine ⟨max (max (max (max (max ND NT) NS) NH) NU) NR,?_⟩
  intro V _ _ hn U Γ Color _ _ _ _ hm hmn hΓ G Z T hTG π I J hJ p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum hnoshort q hq hQ s hs hS F _ ν Extra ρ μ f hExtra8
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
  let Ufixed:=fun z:(Σ ω:(∀ e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e),F (f ω))=>
    (∀ w,|rawIntervalUnassignedHubCountOn π d (fun e=>z.1 (Sum.inr e)) w I-(I.card:ℝ)*(1-(∑ g,q w g)-(∑ j,s w j))|<(Fintype.card V:ℝ)^(3/4:ℝ)) ∧
    (∀ v,|rawIntervalUnassignedColumnCount π d (fun e=>z.1 (Sum.inr e)) v J-∑ w∈J,(1-(∑ g,q w g)-(∑ j,s w j))|<(Fintype.card V:ℝ)^(3/4:ℝ))
  let Uall:=fun z:(Σ ω:(∀ e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e),F (f ω))=>
    (∀ w,|rawIntervalUnassignedHubCountOn π d (fun e=>z.1 (Sum.inr e)) w Finset.univ-(Fintype.card V:ℝ)*(1-(∑ g,q w g)-(∑ j,s w j))|<(Fintype.card V:ℝ)^(3/4:ℝ)) ∧
    (∀ v,|rawIntervalUnassignedColumnCount π d (fun e=>z.1 (Sum.inr e)) v Finset.univ-∑ w,(1-(∑ g,q w g)-(∑ j,s w j))|<(Fintype.card V:ℝ)^(3/4:ℝ))
  let Rgood:=fun z:(Σ ω:(∀ e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e),F (f ω))=>
    ∀ x,|(((G.neighborFinset x∩I).filter (fun y=>(z.1 (Sum.inl s(x,y))).1=4)).card:ℝ)-u*(G.neighborFinset x∩I).card|<(Fintype.card V:ℝ)^(3/4:ℝ)
  let law:=μ.sigma (fun ω=>ν (f ω))
  have hPrev:max (max (max ND NT) NS) NH≤Fintype.card V:=le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hn)
  have hOld:max (max ND NT) NS≤Fintype.card V:=le_trans (le_max_left _ _) hPrev
  have hDP:(999:ℝ)/1000≤law.probability Dgood:=
    hD V (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hOld)) U Γ Color G Z p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS F ν
  have hTP:(999:ℝ)/1000≤law.probability Tgood:=
    hT V (le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hOld)) U Γ Color G T hTG p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS F ν
  have hSP:(999:ℝ)/1000≤law.probability Sgood:=
    hSstart V (le_trans (le_max_right _ _) hOld) U Γ Color hm hmn hΓ π d hd p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum q hq hQ s hs hS hnoshort F ν
  have hHP:(999:ℝ)/1000≤law.probability Hgood:=
    hH V (le_trans (le_max_right _ _) hPrev) U Γ Color hmn hΓ π p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum q hq hQ s hs hS hnoshort F ν
  have hUbound:NU≤Fintype.card V:=le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hn)
  have hRbound:NR≤Fintype.card V:=le_trans (le_max_right _ _) hn
  have hUfixed:(999:ℝ)/1000≤law.probability Ufixed:=
    hU V hUbound U Γ Color hmn π p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum q hq hQ s hs hS hnoshort F ν I J hJ
  have hUniv:(Finset.univ:Finset U).Nonempty:=by
    obtain ⟨w⟩:=Fintype.card_pos_iff.mp hm
    exact ⟨w,Finset.mem_univ w⟩
  have hUall:(999:ℝ)/1000≤law.probability Uall:=by
    have hh:=hU V hUbound U Γ Color hmn π p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum q hq hQ s hs hS hnoshort F ν Finset.univ Finset.univ hUniv
    simpa only [Finset.card_univ] using hh
  have hRgood:(999:ℝ)/1000≤law.probability Rgood:=
    hR V hRbound U Γ Color G I p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS F ν
  have hTP':1-(1:ℝ)/1000≤law.probability Tgood:=by linarith
  have hSP':1-(1:ℝ)/1000≤law.probability Sgood:=by linarith
  have hHP':1-(1:ℝ)/1000≤law.probability Hgood:=by linarith
  have hboth:=finiteLaw_good_intersection law Dgood Tgood (1/1000) hTP'
  have hthree:=finiteLaw_good_intersection law (fun z=>Dgood z ∧ Tgood z) Sgood (1/1000) hSP'
  have hfour:=finiteLaw_good_intersection law (fun z=>(Dgood z ∧ Tgood z) ∧ Sgood z) Hgood (1/1000) hHP'
  have hUfixed':1-(1:ℝ)/1000≤law.probability Ufixed:=by linarith
  have hUall':1-(1:ℝ)/1000≤law.probability Uall:=by linarith
  have hRgood':1-(1:ℝ)/1000≤law.probability Rgood:=by linarith
  have hfive:=finiteLaw_good_intersection law (fun z=>((Dgood z ∧ Tgood z) ∧ Sgood z) ∧ Hgood z) Ufixed (1/1000) hUfixed'
  have hsix:=finiteLaw_good_intersection law (fun z=>(((Dgood z ∧ Tgood z) ∧ Sgood z) ∧ Hgood z) ∧ Ufixed z) Uall (1/1000) hUall'
  have hseven:=finiteLaw_good_intersection law (fun z=>((((Dgood z ∧ Tgood z) ∧ Sgood z) ∧ Hgood z) ∧ Ufixed z) ∧ Uall z) Rgood (1/1000) hRgood'
  have hExtra8':1-(1:ℝ)/1000≤law.probability Extra:=by linarith
  have height:=finiteLaw_good_intersection law (fun z=>(((((Dgood z ∧ Tgood z) ∧ Sgood z) ∧ Hgood z) ∧ Ufixed z) ∧ Uall z) ∧ Rgood z) Extra (1/1000) hExtra8'
  have hExtra:(99:ℝ)/100≤law.probability (fun z=>((((((Dgood z ∧ Tgood z) ∧ Sgood z) ∧ Hgood z) ∧ Ufixed z) ∧ Uall z) ∧ Rgood z) ∧ Extra z):=by linarith only [hDP,hboth,hthree,hfour,hfive,hsix,hseven,height]
  simpa only [Dgood,Tgood,Sgood,Hgood,Ufixed,Uall,Rgood,law,and_assoc] using hExtra
end Oberwolfach

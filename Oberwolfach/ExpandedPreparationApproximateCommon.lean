module

public import Oberwolfach.ExpandedPreparationEightEvents
public import Oberwolfach.MarkedExpandedApproximatePotentialHigh
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

theorem raw_expanded_selected_preparation_with_approx_potentials (d m:ℕ) (hd:2≤d) (hm:3≤m) (B t:ℝ) (hB:0<B) (ht:0<t) :
    ∃ N:ℕ,∀ (V:Type) [Fintype V] [LinearOrder V],
    N≤Fintype.card V→∀ (U Γ Color:Type) [Fintype U] [Fintype Γ] [Fintype Color] [DecidableEq U]
    (hm:0<Fintype.card U) (hmn:Fintype.card U≤Fintype.card V) (hΓ:Fintype.card Γ≤2)
    (G Z T:SimpleGraph V) (hTG:T≤G) (π:Equiv.Perm V) (I:Finset V) (J:Finset U) (hJ:J.Nonempty)
    (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
    (hnoshort:∀ x l,0<l→l<2*d+1→(π^l) x≠x) (q:U→Γ→ℝ) (hq:∀ u g,0≤q u g) (hQ:∀ u,∑ g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀ u j,0≤s u j) (hS:∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
    (H₀ Hₖ:V→U→Prop)
    (w:MarkedWheel (Prod.fst:V×V→V) Prod.snd Prod.fst Prod.snd m π (3*d) H₀ Hₖ→ℝ)
    (hw:∀ W,0≤w W ∧ w W≤B/(Fintype.card V:ℝ)^m) (g:Γ) (j:Color)
    (F:RawMarkedOutcome V U Γ Color→Type) [∀ a,Fintype (F a)] (ν:∀ a,FiniteLaw (F a)) (E:(Σ a,F a)→Prop),
    (7:ℝ)/10≤((FiniteLaw.pi (rawMarkedWheelLaw (V:=V) p k hp hk (by linarith) d hd q hq hQ s hs hS)).sigma ν).probability E→
    let ρ:=markedExpandedPhysicalProbability p k p₂ k₂ u
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS)
    let f:=fun (ω:∀ e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e) e=>rawExpandedMarkedCollapse e (ω e)
    let Extra:=fun z:(Σ ω:(∀ e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e),F (f ω))=>∀ root,
      |typedMarkedPotentialLoad w (rawMarkedPairRims G π d (fun e=>rawExpandedApproximateCollapse e (z.1 e)))
        (rawMarkedPairSpokes π d (fun e=>rawExpandedApproximateCollapse e (z.1 e)) g j) root-
        ∑ W,(if root∈typedMarkedOccurrenceResources W then w W else 0)*
          ∏ a∈typedMarkedOccurrenceResources W\{root},rawMarkedWheelMarginal G π d p₂ k₂ q s g j a|<t;
    ∃ z,0<(μ.sigma (fun ω=>ν (f ω))).mass z ∧ E ⟨f z.1,z.2⟩ ∧
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
      (∀ x,|(((G.neighborFinset x∩I).filter (fun y=>(z.1 (Sum.inl s(x,y))).1=4)).card:ℝ)-u*(G.neighborFinset x∩I).card|<(Fintype.card V:ℝ)^(3/4:ℝ)) ∧ Extra z := by
  obtain ⟨N₀,hBase⟩:=raw_expanded_selected_preparation_with_extra_event d hd
  obtain ⟨NP,hPot⟩:=raw_expanded_approximate_marked_potentials_highProbability d m hd hm B t hB ht
  refine ⟨max N₀ NP,?_⟩
  intro V _ _ hn U Γ Color _ _ _ _ hmU hmn hΓ G Z T hTG π I J hJ p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum hnoshort q hq hQ s hs hS H₀ Hₖ w hw g j F _ ν E hE ρ μ f Extra
  have hP:(999:ℝ)/1000≤(μ.sigma (fun ω=>ν (f ω))).probability Extra:=
    hPot V U Γ Color (le_trans (le_max_right _ _) hn) hmn G π p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum q hq hQ s hs hS hnoshort H₀ Hₖ w hw g j F ν
  exact hBase V (le_trans (le_max_left _ _) hn) U Γ Color hmU hmn hΓ G Z T hTG π I J hJ p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum hnoshort q hq hQ s hs hS F ν E Extra hE hP
end Oberwolfach

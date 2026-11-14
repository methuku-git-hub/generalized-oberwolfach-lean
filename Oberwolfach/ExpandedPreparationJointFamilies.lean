module

public import Oberwolfach.ExpandedApproximateJointFamilies
public import Oberwolfach.ExpandedPreparationEightEvents
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

theorem raw_expanded_preparation_joint_families
    (IType JType:Type) [Fintype IType] [Fintype JType] (d:ℕ) (hd:2≤d) (m:IType→ℕ) (hmtype:∀ i,2≤m i)
    (B t:IType→ℝ) (hB:∀ i,0<B i) (ht:∀ i,0<t i)
    (mK:ℕ) (hmK:3≤mK) (BK tK:ℝ) (hBK:0<BK) (htK:0<tK) :
    ∃ N:ℕ,∀ (V:Type) [Fintype V] [LinearOrder V],
    N≤Fintype.card V→∀ (U Γ Color:Type) [Fintype U] [Fintype Γ] [Fintype Color] [DecidableEq U]
    (hm:0<Fintype.card U) (hmn:Fintype.card U≤Fintype.card V) (hΓ:Fintype.card Γ≤2)
    (G Z T:SimpleGraph V) (hTG:T≤G) (π:Equiv.Perm V) (I:Finset V) (J:Finset U) (hJ:J.Nonempty)
    (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
    (hnoshort:∀ x l,0<l→l<2*d+1→(π^l) x≠x) (q:U→Γ→ℝ) (hq:∀ u g,0≤q u g) (hQ:∀ u,∑ g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀ u j,0≤s u j) (hS:∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
    (w:∀ i,OrderedOrdinaryWheel (U:=U) π (3*d) (m i+1)→ℝ)
    (hw:∀ i W,0≤w i W ∧ w i W≤B i/(Fintype.card V:ℝ)^(m i))
    (g:IType→Γ) (j:IType→Color) (H₀ Hₖ:V→U→Prop)
    (wK:∀ k:JType,MarkedWheel (Prod.fst:V×V→V) Prod.snd Prod.fst Prod.snd mK π (3*d) H₀ Hₖ→ℝ)
    (hwK:∀ k W,0≤wK k W ∧ wK k W≤BK/(Fintype.card V:ℝ)^mK) (gK:JType→Γ) (jK:JType→Color)
    (F:RawMarkedOutcome V U Γ Color→Type) [∀ a,Fintype (F a)] (ν:∀ a,FiniteLaw (F a)) (E:(Σ a,F a)→Prop),
    (7:ℝ)/10≤((FiniteLaw.pi (rawMarkedWheelLaw (V:=V) p k hp hk (by linarith) d hd q hq hQ s hs hS)).sigma ν).probability E→
    let ρ:=markedExpandedPhysicalProbability p k p₂ k₂ u
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS)
    let f:=fun (ω:∀ e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e) e=>rawExpandedMarkedCollapse e (ω e)
    let O:=fun z:(Σ ω:(∀ e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e),F (f ω))=>∀ i root,
      |resourcePatternLoad orderedOrdinaryResources (w i) (fun _ _=>true) root
        (orderedOrdinaryResourceState G π d (g i) (j i) (fun e=>rawExpandedApproximateCollapse e (z.1 e)))-
        ∑ W,(if root∈orderedOrdinaryResources W then w i W else 0)*
          ∏ a∈orderedOrdinaryResources W\{root},rawMarkedWheelMarginal G π d p₂ k₂ q s (g i) (j i) (orderedOrdinaryResourceEmbedding a)|<t i
    let K:=fun z:(Σ ω:(∀ e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e),F (f ω))=>∀ k root,
      |typedMarkedPotentialLoad (wK k) (rawMarkedPairRims G π d (fun e=>rawExpandedApproximateCollapse e (z.1 e)))
        (rawMarkedPairSpokes π d (fun e=>rawExpandedApproximateCollapse e (z.1 e)) (gK k) (jK k)) root-
        ∑ W,(if root∈typedMarkedOccurrenceResources W then wK k W else 0)*
          ∏ a∈typedMarkedOccurrenceResources W\{root},rawMarkedWheelMarginal G π d p₂ k₂ q s (gK k) (jK k) a|<tK;

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
      (∀ x,|(((G.neighborFinset x∩I).filter (fun y=>(z.1 (Sum.inl s(x,y))).1=4)).card:ℝ)-u*(G.neighborFinset x∩I).card|<(Fintype.card V:ℝ)^(3/4:ℝ)) ∧ O z ∧ K z := by
  obtain ⟨N₀,hBase⟩:=raw_expanded_selected_preparation_with_extra_event d hd
  obtain ⟨N₁,hJoint⟩:=raw_expanded_ordinary_marked_families_joint_highProbability IType JType d hd m hmtype B t hB ht mK hmK BK tK hBK htK
  refine ⟨max N₀ N₁,?_⟩
  intro V _ _ hn U Γ Color _ _ _ _ hm hmn hΓ G Z T hTG π I J hJ p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum hnoshort q hq hQ s hs hS w hw g j H₀ Hₖ wK hwK gK jK F _ ν E hE ρ μ f O K
  have hgood:(999:ℝ)/1000≤(μ.sigma (fun ω=>ν (f ω))).probability (fun z=>O z ∧ K z):=
    hJoint V U Γ Color ((le_max_right _ _).trans hn) hmn G π p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum q hq hQ s hs hS hnoshort w hw g j H₀ Hₖ wK hwK gK jK F ν
  obtain ⟨z,hz,hEz,hDeg,hPath,hStart,hHub,hRest,hAll,hRim,hO,hK⟩:=
    hBase V ((le_max_left _ _).trans hn) U Γ Color hm hmn hΓ G Z T hTG π I J hJ p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum hnoshort q hq hQ s hs hS F ν E (fun z=>O z ∧ K z) hE hgood
  exact ⟨z,hz,hEz,hDeg,hPath,hStart,hHub,hRest,hAll,hRim,hO,hK⟩
end Oberwolfach

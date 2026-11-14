module

public import Oberwolfach.ExpandedApproximateJointFamilies
public import Oberwolfach.ExpandedPreparationReferenceExtension

@[expose] public section
/-! The reference theorem, basic preparation estimates and every marked and
ordinary root event hold on one outcome of the original joint law. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 25000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
theorem raw_expanded_families_with_reference
    (I J:Type) [Fintype I] [Fintype J] (d:ℕ) (hd:2≤d) (m:I→ℕ) (hm:∀ i,2≤m i)
    (B t:I→ℝ) (hB:∀ i,0<B i) (ht:∀ i,0<t i)
    (mK:ℕ) (hmK:3≤mK) (BK tK:ℝ) (hBK:0<BK) (htK:0<tK):
    ∃ N:ℕ,∀ (V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [LinearOrder V] [DecidableEq U],
    N≤Fintype.card V→Fintype.card U≤Fintype.card V→Fintype.card Γ≤2→
    ∀ (P Z T:SimpleGraph V) (hTP:T≤P) (π:Equiv.Perm V) (Vset:Finset V) (Uset:Finset U) (hUset:Uset.Nonempty)
    (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
    (q:U→Γ→ℝ) (hq:∀ u g,0≤q u g) (hQ:∀ u,∑ g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀ u j,0≤s u j) (hS:∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
    (hnoshort:∀ x l,0<l→l<2*d+1→(π^l) x≠x)
    (w:∀ i,OrderedOrdinaryWheel (U:=U) π (3*d) (m i+1)→ℝ)
    (hw:∀ i W,0≤w i W ∧ w i W≤B i/(Fintype.card V:ℝ)^(m i))
    (g:I→Γ) (j:I→Color) (H₀ Hₖ:V→U→Prop)
    (wK:∀ k:J,MarkedWheel (Prod.fst:V×V→V) Prod.snd Prod.fst Prod.snd mK π (3*d) H₀ Hₖ→ℝ)
    (hwK:∀ k W,0≤wK k W ∧ wK k W≤BK/(Fintype.card V:ℝ)^mK) (gK:J→Γ) (jK:J→Color)
    (F:RawMarkedOutcome V U Γ Color→Type) [∀ a,Fintype (F a)] (ν:∀ a,FiniteLaw (F a)) (Ref:(Σ a,F a)→Prop),
    (∀ E:(Σ a,F a)→Prop,(99:ℝ)/100≤((FiniteLaw.pi (rawMarkedWheelLaw (V:=V) p k hp hk (by linarith) d hd q hq hQ s hs hS)).sigma ν).probability E→∃ y,Ref y ∧ E y)→
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS)
    let f:=fun (ω:∀ e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e) e=>rawExpandedMarkedCollapse e (ω e)
    let O:=fun z:(Σ ω:(∀ e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e),F (f ω))=>∀ i root,
      |resourcePatternLoad orderedOrdinaryResources (w i) (fun _ _=>true) root
        (orderedOrdinaryResourceState P π d (g i) (j i) (fun e=>rawExpandedApproximateCollapse e (z.1 e)))-
        ∑ W,(if root∈orderedOrdinaryResources W then w i W else 0)*
          ∏ a∈orderedOrdinaryResources W\{root},rawMarkedWheelMarginal P π d p₂ k₂ q s (g i) (j i) (orderedOrdinaryResourceEmbedding a)|<t i
    let K:=fun z:(Σ ω:(∀ e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e),F (f ω))=>∀ k root,
      |typedMarkedPotentialLoad (wK k) (rawMarkedPairRims P π d (fun e=>rawExpandedApproximateCollapse e (z.1 e)))
        (rawMarkedPairSpokes π d (fun e=>rawExpandedApproximateCollapse e (z.1 e)) (gK k) (jK k)) root-
        ∑ W,(if root∈typedMarkedOccurrenceResources W then wK k W else 0)*
          ∏ a∈typedMarkedOccurrenceResources W\{root},rawMarkedWheelMarginal P π d p₂ k₂ q s (gK k) (jK k) a|<tK
    let ρ:=markedExpandedPhysicalProbability p k p₂ k₂ u
    let Good:=fun z:(Σ ω:(∀ e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e),F (f ω))=>
      expandedPhysicalDegreeGood P Z ρ (fun e=>z.1 (Sum.inl e)) ∧
      (∀ x y,x≠y→|(eligibleTwoPathCount T (sampledColourOrientation P (fun e=>markedExpandedClass (z.1 (Sum.inl e))) 0) x y:ℝ)-
        ((T.neighborFinset x∩T.neighborFinset y).card:ℝ)*((2*p+2*k+2*p₂+2*k₂+u)/2)^2|<(Fintype.card V:ℝ)^(3/5:ℝ)) ∧
      (∀ g a,|((rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) g a).card:ℝ)-(∑ u,q u g/(d:ℝ))|<(Fintype.card V:ℝ)^(3/5:ℝ)) ∧
      (∀ u g,|rawIntervalHubStartCount π d g (fun e=>z.1 (Sum.inr e)) u-(Fintype.card V:ℝ)*q u g/d|<
        (Fintype.card V:ℝ)^(3/4:ℝ)/d) ∧
      ((∀ w,|rawIntervalUnassignedHubCountOn π d (fun e=>z.1 (Sum.inr e)) w Vset-(Vset.card:ℝ)*(1-(∑ g,q w g)-(∑ j,s w j))|<(Fintype.card V:ℝ)^(3/4:ℝ)) ∧
       (∀ v,|rawIntervalUnassignedColumnCount π d (fun e=>z.1 (Sum.inr e)) v Uset-∑ w∈Uset,(1-(∑ g,q w g)-(∑ j,s w j))|<(Fintype.card V:ℝ)^(3/4:ℝ))) ∧
      ((∀ w,|rawIntervalUnassignedHubCountOn π d (fun e=>z.1 (Sum.inr e)) w Finset.univ-(Fintype.card V:ℝ)*(1-(∑ g,q w g)-(∑ j,s w j))|<(Fintype.card V:ℝ)^(3/4:ℝ)) ∧
       (∀ v,|rawIntervalUnassignedColumnCount π d (fun e=>z.1 (Sum.inr e)) v Finset.univ-∑ w,(1-(∑ g,q w g)-(∑ j,s w j))|<(Fintype.card V:ℝ)^(3/4:ℝ))) ∧
      (∀ x,|(((P.neighborFinset x∩Vset).filter (fun y=>(z.1 (Sum.inl s(x,y))).1=4)).card:ℝ)-u*(P.neighborFinset x∩Vset).card|<(Fintype.card V:ℝ)^(3/4:ℝ)) ∧ O z ∧ K z;
    ∃ z,0<(μ.sigma (fun ω=>ν (f ω))).mass z ∧ Ref ⟨f z.1,z.2⟩ ∧ Good z:=by
  obtain ⟨N₁,hFamilies⟩:=raw_expanded_ordinary_marked_families_joint_highProbability I J d hd m hm B t hB ht mK hmK BK tK hBK htK
  obtain ⟨N₂,hBasic⟩:=raw_expanded_preparation_with_reference_extension d hd
  refine ⟨max N₁ N₂,?_⟩
  intro V U Γ Color _ _ _ _ _ _ hn hUV hΓ P Z T hTP π Vset Uset hUset p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum q hq hQ s hs hS hnoshort w hw g j H₀ Hₖ wK hwK gK jK F _ ν Ref hRef μ f O K ρ Good
  have hExtra:(999:ℝ)/1000≤(μ.sigma (fun ω=>ν (f ω))).probability (fun z=>O z ∧ K z):=
    hFamilies V U Γ Color ((le_max_left _ _).trans hn) hUV P π p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum q hq hQ s hs hS hnoshort w hw g j H₀ Hₖ wK hwK gK jK F ν
  have hUpos:0<Fintype.card U:=Fintype.card_pos_iff.mpr ⟨hUset.choose⟩
  exact hBasic V ((le_max_right _ _).trans hn) U Γ Color hUpos hUV hΓ P Z T hTP π Vset Uset hUset p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum hnoshort q hq hQ s hs hS F ν Ref (fun z=>O z ∧ K z) hRef hExtra
end Oberwolfach

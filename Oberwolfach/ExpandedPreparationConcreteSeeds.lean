module

public import Oberwolfach.PhysicalOrdinarySeedBound
public import Oberwolfach.MarkedVariableHubSeedBound
public import Oberwolfach.ExpandedPreparationJointFamilies
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

theorem raw_expanded_preparation_concrete_seed_families
    (IType JType:Type) [Fintype IType] [Fintype JType] (d:ℕ) (hd:2≤d) (n:IType→ℕ) (hnlen:∀ i,1≤n i)
    (B t:IType→ℝ) (hB:∀ i,0<B i) (ht:∀ i,0<t i)
    (mK:ℕ) (hmK:3≤mK) (BK tK pstar:ℝ) (hBK:0<BK) (htK:0<tK) (hpstar:0<pstar) :
    ∃ N:ℕ,∀ (V:Type) [Fintype V] [LinearOrder V],
    N≤Fintype.card V→∀ (U Γ Color:Type) [Fintype U] [Fintype Γ] [Fintype Color] [DecidableEq U]
    (hm:0<Fintype.card U) (hmn:Fintype.card U≤Fintype.card V) (hΓ:Fintype.card Γ≤2)
    (G Z T:SimpleGraph V) (hTG:T≤G) (π:Equiv.Perm V) (I:Finset V) (J:Finset U) (hJ:J.Nonempty)
    (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
    (hnoshort:∀ x l,0<l→l<2*d+1→(π^l) x≠x) (q:U→Γ→ℝ) (hq:∀ u g,0≤q u g) (hQ:∀ u,∑ g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀ u j,0≤s u j) (hS:∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
    (D τ AK:ℝ) (hDlo:(Fintype.card V:ℝ)/2≤D) (hDhi:D≤2*Fintype.card V)
    (hp₂lo:pstar≤p₂) (hk₂lo:pstar≤k₂)
    (g:IType→Γ) (j:IType→Color) (gK:JType→Γ) (jK:JType→Color)
    (hslo:∀ i v,pstar≤s v (j i)) (hsloK:∀ i v,pstar≤s v (jK i))
    (η:IType→U→ℝ) (hη0:∀ i v,0≤η i v) (hηhi:∀ i v,η i v≤1/s v (j i))
    (lamO:∀ i,OrdinaryCycle G (n i+2)→ℝ)
    (hlam:∀ i C,0≤lamO i C ∧ lamO i C≤B i/(Fintype.card V:ℝ)^(n i))
    (lamK:(Fin (mK+1)→V)→ℝ)
    (hlamK:SuccessorSequenceWeightConditions G π (3*d) D τ AK BK lamK)
    (F:RawMarkedOutcome V U Γ Color→Type) [∀ a,Fintype (F a)] (ν:∀ a,FiniteLaw (F a)) (E:(Σ a,F a)→Prop),
    (7:ℝ)/10≤((FiniteLaw.pi (rawMarkedWheelLaw (V:=V) p k hp hk (by linarith) d hd q hq hQ s hs hS)).sigma ν).probability E→
    let H₀:=fun (_:V) (_:U)=>True
    let Hₖ:=fun (_:V) (_:U)=>True
    let w:=fun (i:IType) (W:OrderedOrdinaryWheel (U:=U) π (3*d) (n i+2))=>
      η i W.2*physicalOrdinaryTupleWeight (π:=π) (b:=3*d) (hnlen i) (lamO i) W.1.val/
        (((n i+2:ℕ):ℝ)*D*p₂^(n i+2)*(s W.2 (j i))^(n i+1))
    let wK:=fun (i:JType) (W:MarkedWheel (Prod.fst:V×V→V) Prod.snd Prod.fst Prod.snd mK π (3*d) H₀ Hₖ)=>
      lamK W.1.val/(D*p₂^mK*k₂*(s W.2.val (jK i))^mK)
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
  let BO:=fun i:IType=>2*B i/pstar^(2*(n i+2))
  let BM:ℝ:=2*BK/pstar^(2*mK+1)
  have hBO:∀ i,0<BO i:=by intro i;have := hB i;dsimp [BO];positivity
  have hBM:0<BM:=by dsimp [BM];positivity
  obtain ⟨N₀,hBase⟩:=raw_expanded_preparation_joint_families IType JType d hd (fun i=>n i+1) (by intro i;have:=hnlen i;omega)
    BO t hBO ht mK hmK BM tK hBM htK
  refine ⟨max N₀ 1,?_⟩
  intro V _ _ hn U Γ Color _ _ _ _ hm hmn hΓ G Z T hTG π I J hJ p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum hnoshort q hq hQ s hs hS
    D τ AK hDlo hDhi hp₂lo hk₂lo g j gK jK hslo hsloK η hη0 hηhi lamO hlam lamK hlamK F _ ν E hE H₀ Hₖ w wK ρ μ f O K
  have hnV:0<Fintype.card V:=by omega
  have hp₂one:p₂≤1:=by linarith
  have hk₂one:k₂≤1:=by linarith
  have hsone:∀ v c,s v c≤1:=by
    intro v c
    have hsingle:s v c≤∑ j,s v j:=Finset.single_le_sum (fun i _=>hs v i) (Finset.mem_univ c)
    have hQ0:0≤∑ g,q v g:=Finset.sum_nonneg (fun i _=>hq v i)
    have hfactor:0≤(1+1/(d:ℝ))*(∑ g,q v g):=mul_nonneg (by positivity) hQ0
    have hh:=hS v
    unfold intervalUncoveredProbability at hh
    linarith
  have hw:∀ i W,0≤w i W ∧ w i W≤BO i/(Fintype.card V:ℝ)^(n i+1):=by
    intro i W
    exact physicalOrdinary_seed_upper (P:=G) (π:=π) (b:=3*d) (hnlen i) hnV (lamO i) (fun C=>(hlam i C).1) (B i) (hB i).le
      (fun C=>(hlam i C).2) D p₂ pstar hDlo hDhi hpstar hp₂lo hp₂one (fun v=>s v (j i)) (η i)
      (hslo i) (fun v=>hsone v (j i)) (hη0 i) (hηhi i) W
  have hwK:∀ i W,0≤wK i W ∧ wK i W≤BM/(Fintype.card V:ℝ)^mK:=by
    intro i W
    exact marked_variable_hub_seed_upper G π mK (3*d) (by omega) D τ AK BK p₂ k₂ pstar hnV hDlo hDhi hpstar hp₂lo hk₂lo hp₂one hk₂one
      (fun v=>s v (jK i)) (hsloK i) (fun v=>hsone v (jK i)) (hBK.le) lamK hlamK W
  exact hBase V ((le_max_left _ _).trans hn) U Γ Color hm hmn hΓ G Z T hTG π I J hJ p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum hnoshort q hq hQ s hs hS
    w hw g j H₀ Hₖ wK hwK gK jK F ν E hE
end Oberwolfach

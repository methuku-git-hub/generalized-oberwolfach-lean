module

public import Oberwolfach.ExpandedPreparationSelectedFamiliesReference
public import Oberwolfach.CombinedPreparationAllRoots
public import Oberwolfach.PhysicalOrdinarySeedBound
public import Oberwolfach.MarkedVariableHubSeedBound

@[expose] public section
/-! The original fixed seed formulas, retained reference property, and all
four balanced root estimates on the same enriched outcome. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 24000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
theorem raw_expanded_seeded_balanced_reference_all_roots
    (K:ℕ) (d:ℕ) (hd:2≤d) (n:Fin K→ℕ) (hnlen:∀ i,1≤n i)
    (B t:Fin K→ℝ) (hB:∀ i,0<B i) (ht:∀ i,0<t i)
    (mK:ℕ) (hmK:3≤mK) (BK tK pstar:ℝ) (hBK:0<BK) (htK:0<tK) (hpstar:0<pstar) :
    ∃ N:ℕ,∀ (V:Type) [Fintype V] [LinearOrder V],
    N≤Fintype.card V→∀ (S:Finset (Fin K)) (U Γ Color:Type) [Fintype U] [Fintype Γ] [Fintype Color] [DecidableEq U]
    (hm:0<Fintype.card U) (hmn:Fintype.card U≤Fintype.card V) (hΓ:Fintype.card Γ≤2)
    (G Z T:SimpleGraph V) (hTG:T≤G) (π:Equiv.Perm V) (I:Finset V) (J:Finset U) (hJ:J.Nonempty)
    (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
    (hnoshort:∀ x l,0<l→l<2*d+1→(π^l) x≠x) (q:U→Γ→ℝ) (hq:∀ u g,0≤q u g) (hQ:∀ u,∑ g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀ u j,0≤s u j) (hS:∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
    (D τ AK:ℝ) (hDlo:(Fintype.card V:ℝ)/2≤D) (hDhi:D≤2*Fintype.card V)
    (hp₂lo:pstar≤p₂) (hk₂lo:pstar≤k₂)
    (g:Γ) (j:Color)
    (hslo:∀ v,pstar≤s v j)
    (η:{i:Fin K // i∈S}→U→ℝ) (hη0:∀ i v,0≤η i v) (hηhi:∀ i v,η i v≤1/s v j)
    (lamO:∀ i:{i:Fin K // i∈S},OrdinaryCycle G (n i.val+2)→ℝ)
    (hlam:∀ i C,0≤lamO i C ∧ lamO i C≤B i.val/(Fintype.card V:ℝ)^(n i.val))
    (lamK:(Fin (mK+1)→V)→ℝ)
    (hlamK:SuccessorSequenceWeightConditions G π (3*d) D τ AK BK lamK)
    (ε:ℝ) (hreg:∀ x,|(G.degree x:ℝ)-D|≤ε*(Fintype.card V:ℝ))
    (hV:∀ i:{i:Fin K // i∈S},6*((n i.val+2:ℕ):ℝ)^4*B i.val*(2*(3*d))+ε*(Fintype.card V:ℝ)≤τ*D)
    (hR:∀ i:{i:Fin K // i∈S},5*((n i.val+2:ℕ):ℝ)^4*B i.val*(2*(3*d))/Fintype.card V≤τ)
    (he:∀ i x y,(∑ C,if C.val.val.Adj x y then lamO i C else 0)=if G.Adj x y then 1 else 0)
    (hbal:∀ v,(mK:ℝ)*q v g+(∑ i,η i v)*s v j=s v j)
    (hqbal:(∑ v,q v g)=D*k₂) (hsbal:(∑ v,s v j)=D*p₂)
    (F:RawMarkedOutcome V U Γ Color→Type) [∀ a,Fintype (F a)] (ν:∀ a,FiniteLaw (F a)) (Ref:(Σ a,F a)→Prop),
    (∀ E:(Σ a,F a)→Prop,(99:ℝ)/100≤((FiniteLaw.pi (rawMarkedWheelLaw (V:=V) p k hp hk (by linarith) d hd q hq hQ s hs hS)).sigma ν).probability E→∃ y,Ref y ∧ E y)→
    let H₀:=fun (_:V) (_:U)=>True
    let Hₖ:=fun (_:V) (_:U)=>True
    let w:=fun (i:{i:Fin K // i∈S}) (W:OrderedOrdinaryWheel (U:=U) π (3*d) (n i.val+2))=>
      η i W.2*physicalOrdinaryTupleWeight (π:=π) (b:=3*d) (hnlen i) (lamO i) W.1.val/
        (((n i.val+2:ℕ):ℝ)*D*p₂^(n i.val+2)*(s W.2 j)^(n i.val+1))
    let wK:=fun (i:Unit) (W:MarkedWheel (Prod.fst:V×V→V) Prod.snd Prod.fst Prod.snd mK π (3*d) H₀ Hₖ)=>
      lamK W.1.val/(D*p₂^mK*k₂*(s W.2.val j)^mK)
    let ρ:=markedExpandedPhysicalProbability p k p₂ k₂ u
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS)
    let f:=fun (ω:∀ e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e) e=>rawExpandedMarkedCollapse e (ω e)
    let O:=fun z:(Σ ω:(∀ e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e),F (f ω))=>∀ i root,
      |resourcePatternLoad orderedOrdinaryResources (w i) (fun _ _=>true) root
        (orderedOrdinaryResourceState G π d g j (fun e=>rawExpandedApproximateCollapse e (z.1 e)))-
        ∑ W,(if root∈orderedOrdinaryResources W then w i W else 0)*
          ∏ a∈orderedOrdinaryResources W\{root},rawMarkedWheelMarginal G π d p₂ k₂ q s g j (orderedOrdinaryResourceEmbedding a)|<t i.val
    let Kevent:=fun z:(Σ ω:(∀ e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e),F (f ω))=>∀ k root,
      |typedMarkedPotentialLoad (wK k) (rawMarkedPairRims G π d (fun e=>rawExpandedApproximateCollapse e (z.1 e)))
        (rawMarkedPairSpokes π d (fun e=>rawExpandedApproximateCollapse e (z.1 e)) g j) root-
        ∑ W,(if root∈typedMarkedOccurrenceResources W then wK k W else 0)*
          ∏ a∈typedMarkedOccurrenceResources W\{root},rawMarkedWheelMarginal G π d p₂ k₂ q s g j a|<tK
    let LK:=fun z root=>typedMarkedPotentialLoad (wK ()) (rawMarkedPairRims G π d (fun e=>rawExpandedApproximateCollapse e (z.1 e)))
      (rawMarkedPairSpokes π d (fun e=>rawExpandedApproximateCollapse e (z.1 e)) g j) root
    let LO:=fun z i root=>resourcePatternLoad orderedOrdinaryResources (w i) (fun _ _=>true) root
      (orderedOrdinaryResourceState G π d g j (fun e=>rawExpandedApproximateCollapse e (z.1 e)));

    ∃ z,0<(μ.sigma (fun ω=>ν (f ω))).mass z ∧ Ref ⟨f z.1,z.2⟩ ∧
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
      (∀ x,|(((G.neighborFinset x∩I).filter (fun y=>(z.1 (Sum.inl s(x,y))).1=4)).card:ℝ)-u*(G.neighborFinset x∩I).card|<(Fintype.card V:ℝ)^(3/4:ℝ)) ∧ O z ∧ Kevent z ∧
      (∀ v w,|LK z (Sum.inr (false,v,w))+∑ i,LO z i (Sum.inr (v,w))-1|<tK+(∑ i:{i:Fin K // i∈S},t i.val)+τ) ∧
      (∀ x y,G.Adj x y→¬PermutationClose π (3*d) x y→
        |LK z (Sum.inl (Sum.inl (x,y)))+∑ i,LO z i (Sum.inl (x,y))-1|<tK+(∑ i:{i:Fin K // i∈S},t i.val)+τ) ∧
      (∀ v w,q w g≠0→|LK z (Sum.inr (true,v,w))-1|<tK+τ) ∧
      (∀ x y,G.Adj x (π y)→¬PermutationClose π (3*d) x y→|LK z (Sum.inl (Sum.inr (x,y)))-1|<tK+τ) := by
  let BO:=fun i:Fin K=>2*B i/pstar^(2*(n i+2))
  let BM:ℝ:=2*BK/pstar^(2*mK+1)
  have hBO:∀ i,0<BO i:=by intro i;have :=hB i;dsimp [BO];positivity
  have hBM:0<BM:=by dsimp [BM];positivity
  obtain ⟨N,hFamilies⟩:=raw_expanded_selected_families_with_reference K Unit d hd (fun i=>n i+1) (by intro i;have:=hnlen i;omega) BO t hBO ht mK hmK BM tK hBM htK
  refine ⟨max N 1,?_⟩
  intro V _ _ hn S U Γ Color _ _ _ _ hm hmn hΓ G Z T hTG π I J hJ p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum hnoshort q hq hQ s hs hS
    D τ AK hDlo hDhi hp₂lo hk₂lo g j hslo η hη0 hηhi lamO hlam lamK hlamK ε hreg hV hR he hbal hqbal hsbal F _ ν Ref hRef H₀ Hₖ w wK ρ μ f O Kevent LK LO
  have hnV:0<Fintype.card V:=by omega
  have hD:0<D:=lt_of_lt_of_le (by exact_mod_cast (show (0:ℝ)<(Fintype.card V:ℝ)/2 by positivity)) hDlo
  have hp₂pos:0<p₂:=hpstar.trans_le hp₂lo
  have hk₂pos:0<k₂:=hpstar.trans_le hk₂lo
  have hp₂one:p₂≤1:=by linarith
  have hk₂one:k₂≤1:=by linarith
  have hactive:2*p₂+2*k₂≤1:=by linarith
  have hspos:∀ v,0<s v j:=fun v=>hpstar.trans_le (hslo v)
  have hsone:∀ v c,s v c≤1:=by
    intro v c
    have hsingle:s v c≤∑ j,s v j:=Finset.single_le_sum (fun i _=>hs v i) (Finset.mem_univ c)
    have hQ0:0≤∑ g,q v g:=Finset.sum_nonneg (fun i _=>hq v i)
    have hfactor:0≤(1+1/(d:ℝ))*(∑ g,q v g):=mul_nonneg (by positivity) hQ0
    have hh:=hS v
    unfold intervalUncoveredProbability at hh
    linarith
  have hw:∀ i W,0≤w i W ∧ w i W≤BO i.val/(Fintype.card V:ℝ)^(n i.val+1):=by
    intro i W
    exact physicalOrdinary_seed_upper (P:=G) (π:=π) (b:=3*d) (hnlen i.val) hnV (lamO i) (fun C=>(hlam i C).1) (B i.val) (hB i.val).le
      (fun C=>(hlam i C).2) D p₂ pstar hDlo hDhi hpstar hp₂lo hp₂one (fun v=>s v j) (η i)
      hslo (fun v=>hsone v j) (hη0 i) (hηhi i) W
  have hwK:∀ i W,0≤wK i W ∧ wK i W≤BM/(Fintype.card V:ℝ)^mK:=by
    intro i W
    exact marked_variable_hub_seed_upper G π mK (3*d) (by omega) D τ AK BK p₂ k₂ pstar hnV hDlo hDhi hpstar hp₂lo hk₂lo hp₂one hk₂one
      (fun v=>s v j) hslo (fun v=>hsone v j) hBK.le lamK hlamK W
  obtain ⟨z,hz,href,hgood⟩:=hFamilies V U Γ Color ((le_max_left _ _).trans hn) hmn hΓ G Z T hTG π I J hJ p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum q hq hQ s hs hS hnoshort S
    w hw (fun _=>g) (fun _=>j) H₀ Hₖ wK hwK (fun _=>g) (fun _=>j) F ν Ref hRef
  obtain ⟨hdegree,hpath,hstart,hhub,hU1,hU2,hrim,hO,hK⟩:=hgood
  refine ⟨z,hz,href,hdegree,hpath,hstart,hhub,hU1,hU2,hrim,hO,hK,?_⟩
  let σ:=fun e=>rawExpandedApproximateCollapse e (z.1 e)
  have htarget:=combined_preparation_all_ordinary_roots G π p₂ k₂ hp₂pos hk₂pos hactive d hd q hq hQ s hs hS hnoshort g j D τ ε hD hspos hnV
    (fun i:{i:Fin K // i∈S}=>n i.val) (fun i=>hnlen i.val) η hη0 lamO (fun i C=>(hlam i C).1) (fun i=>B i.val) (fun i=>(hB i.val).le) (fun i C=>(hlam i C).2)
    he hreg hV hR mK (by omega) AK BK lamK hlamK hbal hqbal hsbal σ tK (fun i=>t i.val)
  dsimp only at htarget
  exact htarget (hK ()) hO
end Oberwolfach

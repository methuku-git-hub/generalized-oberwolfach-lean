module

public import Oberwolfach.ExpandedApproximateBalancedRoots

@[expose] public section
/-! Restrict a fixed-index concentration event to the retained lengths when
identifying the balanced loads. Unretained coefficients contribute zero. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem padded_approximate_seeds_balanced_roots
    (K:ℕ) (S:Finset (Fin K)) (P:SimpleGraph V) (π:Equiv.Perm V) (p k:ℝ)
    (hp:0<p) (hk:0<k) (hsum:2*p+2*k≤1) (d:ℕ) (hd:2≤d)
    (q:U→Γ→ℝ) (hq:∀ u g,0≤q u g) (hQ:∀ u,∑ g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀ u j,0≤s u j) (hS:∀ u,∑ j,s u j ≤ intervalUncoveredProbability d (∑ g,q u g))
    (hnoshort:∀ x l,0<l→l<2*d+1→(π^l) x≠x)
    (g:Γ) (j:Color) (D τ ε:ℝ) (hD:0<D) (hspos:∀ u,0<s u j) (hnV:0<Fintype.card V)
    (n:Fin K→ℕ) (hn:∀ i,1≤n i) (η:Fin K→U→ℝ) (hη:∀ i u,0≤η i u)
    (hηzero:∀ i∉S,∀ u,η i u=0)
    (w:∀ i:Fin K,OrdinaryCycle P (n i+2)→ℝ) (hw:∀ i C,0≤w i C)
    (B:Fin K→ℝ) (hB:∀ i,0≤B i) (hb:∀ i C,w i C≤B i/(Fintype.card V:ℝ)^(n i))
    (he:∀ i:↥S,∀ x y,(∑ C,if C.val.val.Adj x y then w i.val C else 0)=if P.Adj x y then 1 else 0)
    (hdeg:∀ x,|(P.degree x:ℝ)-D|≤ε*(Fintype.card V:ℝ))
    (hbudgetV:∀ i:↥S,6*((n i.val+2:ℕ):ℝ)^4*B i.val*(2*(3*d))+ε*(Fintype.card V:ℝ)≤τ*D)
    (hbudgetE:∀ i:↥S,5*((n i.val+2:ℕ):ℝ)^4*B i.val*(2*(3*d))/Fintype.card V≤τ)
    (m:ℕ) (hm:2≤m) (A BK:ℝ) (weight:(Fin (m+1)→V)→ℝ)
    (hweight:SuccessorSequenceWeightConditions P π (3*d) D τ A BK weight)
    (hbalance:∀ u,(m:ℝ)*q u g+(∑ i,η i u)*s u j=s u j)
    (hqbal:(∑ u,q u g)=D*k) (hsbal:(∑ u,s u j)=D*p)
    (ω:∀ e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e) (tK:ℝ) (t:Fin K→ℝ):
    let σ:=fun e=>rawExpandedApproximateCollapse e (ω e)
    let H₀:=fun (_:V) (_:U)=>True
    let Hₖ:=fun (_:V) (_:U)=>True
    let seedK:=fun W:MarkedWheel (Prod.fst:V×V→V) Prod.snd Prod.fst Prod.snd m π (3*d) H₀ Hₖ=>
      weight W.1.val/(D*p^m*k*(s W.2.val j)^m)
    let seedO:=fun (i:Fin K) (W:OrderedOrdinaryWheel (U:=U) π (3*d) (n i+2))=>
      η i W.2*physicalOrdinaryTupleWeight (π:=π) (b:=3*d) (hn i) (w i) W.1.val/
        (((n i+2:ℕ):ℝ)*D*p^(n i+2)*(s W.2 j)^(n i+1))
    let LK:=fun root=>typedMarkedPotentialLoad seedK (rawMarkedPairRims P π d σ) (rawMarkedPairSpokes π d σ g j) root
    let LO:=fun i root=>resourcePatternLoad orderedOrdinaryResources (seedO i) (fun _ _=>true) root (orderedOrdinaryResourceState P π d g j σ);
    (∀ root,|LK root-∑ W,(if root∈typedMarkedOccurrenceResources W then seedK W else 0)*
        ∏ a∈typedMarkedOccurrenceResources W\{root},rawMarkedWheelMarginal P π d p k q s g j a|<tK)→
    (∀ i root,|LO i root-∑ W,(if root∈orderedOrdinaryResources W then seedO i W else 0)*
        ∏ a∈orderedOrdinaryResources W\{root},rawMarkedWheelMarginal P π d p k q s g j (orderedOrdinaryResourceEmbedding a)|<t i)→
    (∀ v u,|LK (Sum.inr (false,v,u))+∑ i:↥S,LO i.val (Sum.inr (v,u))-1|<tK+(∑ i:↥S,t i.val)+τ) ∧
    (∀ x y,P.Adj x y→¬PermutationClose π (3*d) x y→
      |LK (Sum.inl (Sum.inl (x,y)))+∑ i:↥S,LO i.val (Sum.inl (x,y))-1|<tK+(∑ i:↥S,t i.val)+τ) ∧
    (∀ v u,q u g≠0→|LK (Sum.inr (true,v,u))-1|<tK+τ) ∧
    (∀ x y,P.Adj x (π y)→¬PermutationClose π (3*d) x y→|LK (Sum.inl (Sum.inr (x,y)))-1|<tK+τ):=by
  intro σ H₀ Hₖ seedK seedO LK LO hK hO
  have hsumη:∀ u,(∑ i:↥S,η i.val u)=∑ i:Fin K,η i u:=by
    intro u
    rw [Finset.sum_coe_sort S (fun i=>η i u)]
    apply Finset.sum_subset (Finset.subset_univ S)
    intro i _ hi
    exact hηzero i hi u
  have hbal:∀ u,(m:ℝ)*q u g+(∑ i:↥S,η i.val u)*s u j=s u j:=by
    intro u;rw [hsumη];exact hbalance u
  have h:=expanded_approximate_seed_families_imply_balanced_roots P π p k hp hk hsum d hd q hq hQ s hs hS hnoshort g j D τ ε hD hspos hnV
    (fun i:↥S=>n i.val) (fun i=>hn i.val) (fun i u=>η i.val u) (fun i u=>hη i.val u)
    (fun i=>w i.val) (fun i C=>hw i.val C) (fun i=>B i.val) (fun i=>hB i.val) (fun i C=>hb i.val C)
    he hdeg hbudgetV hbudgetE m hm A BK weight hweight hbal hqbal hsbal ω tK (fun i=>t i.val)
  apply h hK
  intro i root
  exact hO i.val root
end Oberwolfach

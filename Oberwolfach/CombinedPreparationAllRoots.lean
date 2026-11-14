module

public import Oberwolfach.CombinedPreparationSpoke
public import Oberwolfach.CombinedPreparationRim
public import Oberwolfach.RawMarkedVariableSpokeConcentrationTarget
public import Oberwolfach.RawMarkedClosingArcConcentration

@[expose] public section
/-! The simultaneous root-omitted event gives both mixed ordinary-spoke and
ordinary-rim estimates on the same exposed state. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 25000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color I:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [Fintype I]
  [LinearOrder V] [DecidableEq U]

theorem combined_preparation_all_ordinary_roots
    (P:SimpleGraph V) (π:Equiv.Perm V) (p k:ℝ) (hp:0<p) (hk:0<k) (hsum:2*p+2*k≤1)
    (d:ℕ) (hd:2≤d) (q:U→Γ→ℝ) (hq:∀ u g,0≤q u g) (hQ:∀ u,∑ g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀ u j,0≤s u j) (hS:∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
    (hnoshort:∀ x l,0<l→l<2*d+1→(π^l) x≠x)
    (g:Γ) (j:Color) (D τ ε:ℝ) (hD:0<D) (hspos:∀ u,0<s u j) (hnV:0<Fintype.card V)
    (n:I→ℕ) (hn:∀ i,1≤n i) (η:I→U→ℝ) (hη:∀ i u,0≤η i u)
    (w:∀ i,OrdinaryCycle P (n i+2)→ℝ) (hw:∀ i C,0≤w i C)
    (B:I→ℝ) (hB:∀ i,0≤B i) (hb:∀ i C,w i C≤B i/(Fintype.card V:ℝ)^(n i))
    (he:∀ i x y,(∑ C,if C.val.val.Adj x y then w i C else 0)=if P.Adj x y then 1 else 0)
    (hdeg:∀ x,|(P.degree x:ℝ)-D|≤ε*(Fintype.card V:ℝ))
    (hbudgetV:∀ i,6*((n i+2:ℕ):ℝ)^4*B i*(2*(3*d))+ε*(Fintype.card V:ℝ)≤τ*D)
    (hbudgetE:∀ i,5*((n i+2:ℕ):ℝ)^4*B i*(2*(3*d))/Fintype.card V≤τ)
    (m:ℕ) (hm:2≤m) (A BK:ℝ) (weight:(Fin (m+1)→V)→ℝ)
    (hweight:SuccessorSequenceWeightConditions P π (3*d) D τ A BK weight)
    (hbalance:∀ u,(m:ℝ)*q u g+(∑ i,η i u)*s u j=s u j)
    (hqbal:(∑ u,q u g)=D*k) (hsbal:(∑ u,s u j)=D*p)
    (σ:RawMarkedOutcome V U Γ Color) (tK:ℝ) (t:I→ℝ):
    let H₀:=fun (_:V) (_:U)=>True
    let Hₖ:=fun (_:V) (_:U)=>True
    let seedK:=fun W:MarkedWheel (Prod.fst:V×V→V) Prod.snd Prod.fst Prod.snd m π (3*d) H₀ Hₖ=>
      weight W.1.val/(D*p^m*k*(s W.2.val j)^m)
    let seedO:=fun (i:I) (W:OrderedOrdinaryWheel (U:=U) π (3*d) (n i+2))=>
      η i W.2*physicalOrdinaryTupleWeight (π:=π) (b:=3*d) (hn i) (w i) W.1.val/
        (((n i+2:ℕ):ℝ)*D*p^(n i+2)*(s W.2 j)^(n i+1))
    let LK:=fun root=>typedMarkedPotentialLoad seedK (rawMarkedPairRims P π d σ) (rawMarkedPairSpokes π d σ g j) root
    let LO:=fun i root=>resourcePatternLoad orderedOrdinaryResources (seedO i) (fun _ _=>true) root (orderedOrdinaryResourceState P π d g j σ);
    (∀ root,|LK root-∑ W,(if root∈typedMarkedOccurrenceResources W then seedK W else 0)*
        ∏ a∈typedMarkedOccurrenceResources W\{root},rawMarkedWheelMarginal P π d p k q s g j a|<tK)→
    (∀ i root,|LO i root-∑ W,(if root∈orderedOrdinaryResources W then seedO i W else 0)*
        ∏ a∈orderedOrdinaryResources W\{root},rawMarkedWheelMarginal P π d p k q s g j (orderedOrdinaryResourceEmbedding a)|<t i)→
    (∀ v u,|LK (Sum.inr (false,v,u))+∑ i,LO i (Sum.inr (v,u))-1|<tK+(∑ i,t i)+τ) ∧
    (∀ x y,P.Adj x y→¬PermutationClose π (3*d) x y→
      |LK (Sum.inl (Sum.inl (x,y)))+∑ i,LO i (Sum.inl (x,y))-1|<tK+(∑ i,t i)+τ) ∧
    (∀ v u,q u g≠0→|LK (Sum.inr (true,v,u))-1|<tK+τ) ∧
    (∀ x y,P.Adj x (π y)→¬PermutationClose π (3*d) x y→|LK (Sum.inl (Sum.inr (x,y)))-1|<tK+τ):=by
  intro H₀ Hₖ seedK seedO LK LO hK hO
  constructor
  · intro v u
    have h:=combined_preparation_spoke_target P π p k hp hk hsum d hd q hq hQ s hs hS hnoshort g j D τ ε hD hspos hnV
      n hn η hη w hw B hB hb he hdeg hbudgetV m hm A BK weight hweight v u (hbalance u) σ tK t
    dsimp only at h
    apply h hK
    intro i
    exact hO i (Sum.inr (v,u))
  · constructor
    · intro x y hxy hclose
      have h:=combined_preparation_rim_target P π p k hp hk hsum d hd q hq hQ s hs hS hnoshort g j D τ ε hD hspos hnV
        n hn η hη w hw B hB hb he hbudgetE m hm A BK weight hweight x y hxy hclose hbalance hqbal hsbal σ tK t
      dsimp only at h
      apply h hK
      intro i
      exact hO i (Sum.inl (x,y))
    · constructor
      · intro v u hqpos
        have h:=rawMarked_variable_marked_spoke_concentration_target P π p k hp hk hsum d hd q hq hQ s hs hS hnoshort m hm g j D τ A BK tK hD hspos weight hweight σ
        dsimp only at h
        exact h hK v u hqpos
      · intro x y hxy hclose
        have h:=rawMarked_closing_arc_concentration_target P π p k hp hk hsum d hd q hq hQ s hs hS hnoshort m hm g j D τ A BK tK hD hspos hqbal weight hweight σ
        dsimp only at h
        exact h hK x y hclose hxy
end Oberwolfach

module

public import Oberwolfach.PhysicalOrdinarySampledTarget
public import Oberwolfach.RawMarkedOrdinarySpokeConcentration
public import Oberwolfach.PreparationTargetErrorsBalance

@[expose] public section
/-! At an ordinary spoke, combine the marked-cycle load and all ordinary-cycle
loads on the same sampled outcome, using the prescribed hub balance. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color I:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [Fintype I]
  [LinearOrder V] [DecidableEq U]

theorem combined_preparation_spoke_target
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
    (hbudget:∀ i,6*((n i+2:ℕ):ℝ)^4*B i*(2*(3*d))+ε*(Fintype.card V:ℝ)≤τ*D)
    (m:ℕ) (hm:2≤m) (A BK:ℝ) (weight:(Fin (m+1)→V)→ℝ)
    (hweight:SuccessorSequenceWeightConditions P π (3*d) D τ A BK weight)
    (v:V) (u:U) (hbalance:(m:ℝ)*q u g+(∑ i,η i u)*s u j=s u j)
    (σ:RawMarkedOutcome V U Γ Color) (tK:ℝ) (t:I→ℝ):
    let H₀:=fun (_:V) (_:U)=>True
    let Hₖ:=fun (_:V) (_:U)=>True
    let seedK:=fun W:MarkedWheel (Prod.fst:V×V→V) Prod.snd Prod.fst Prod.snd m π (3*d) H₀ Hₖ=>
      weight W.1.val/(D*p^m*k*(s W.2.val j)^m)
    let seedO:=fun (i:I) (W:OrderedOrdinaryWheel (U:=U) π (3*d) (n i+2))=>
      η i W.2*physicalOrdinaryTupleWeight (π:=π) (b:=3*d) (hn i) (w i) W.1.val/
        (((n i+2:ℕ):ℝ)*D*p^(n i+2)*(s W.2 j)^(n i+1))
    let loadK:=typedMarkedPotentialLoad seedK (rawMarkedPairRims P π d σ) (rawMarkedPairSpokes π d σ g j) (Sum.inr (false,v,u))
    let loadO:=fun i=>resourcePatternLoad orderedOrdinaryResources (seedO i) (fun _ _=>true) (Sum.inr (v,u)) (orderedOrdinaryResourceState P π d g j σ);
    (∀ root,|typedMarkedPotentialLoad seedK (rawMarkedPairRims P π d σ) (rawMarkedPairSpokes π d σ g j) root-
      ∑ W,(if root∈typedMarkedOccurrenceResources W then seedK W else 0)*
        ∏ a∈typedMarkedOccurrenceResources W\{root},rawMarkedWheelMarginal P π d p k q s g j a|<tK)→
    (∀ i,|loadO i-∑ W,(if Sum.inr (v,u)∈orderedOrdinaryResources W then seedO i W else 0)*
        ∏ a∈orderedOrdinaryResources W\{Sum.inr (v,u)},rawMarkedWheelMarginal P π d p k q s g j (orderedOrdinaryResourceEmbedding a)|<t i)→
    |loadK+∑ i,loadO i-1|<tK+(∑ i,t i)+τ:=by
  intro H₀ Hₖ seedK seedO loadK loadO hK hO
  have hkTarget:=rawMarked_variable_ordinary_spoke_concentration_target P π p k hp hk hsum d hd q hq hQ s hs hS hnoshort m hm g j D τ A BK tK hD hspos weight hweight σ
  dsimp only at hkTarget
  have hkVal:|loadK-(m:ℝ)*q u g/s u j|<tK+τ*((m:ℝ)*q u g/s u j):=hkTarget hK v u
  have hoVal:∀ i,|loadO i-η i u|<t i+τ*η i u:=by
    intro i
    have h:=physical_ordinary_sampled_spoke_target P π p k hp hk.le hsum d hd q hq hQ s hs hS hnoshort
      (n i) (hn i) hnV g j D τ ε hD hspos (η i) (hη i) (w i) (hw i) (B i) (hB i) (hb i) (he i) hdeg (hbudget i) v u σ (t i)
    dsimp only at h
    exact h (hO i)
  have hratio:(m:ℝ)*q u g/s u j=1-∑ i,η i u:=by
    apply (div_eq_iff (ne_of_gt (hspos u))).2
    nlinarith [hbalance]
  have hbalance':(m:ℝ)*q u g/s u j+∑ i,η i u=1:=by linarith
  exact preparation_target_errors_balanced_sum τ ((m:ℝ)*q u g/s u j) loadK tK (fun i=>η i u) loadO t hbalance' hkVal hoVal
end Oberwolfach

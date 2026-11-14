module

public import Oberwolfach.PhysicalOrdinaryTargetsFromConcentration

@[expose] public section
/-! The all-root estimates for a fixed family yield the spoke and rim targets
for every active cycle length on the same sampled graph. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color I:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [Fintype I]
  [LinearOrder V] [DecidableEq U]

theorem physical_ordinary_family_targets_from_concentration
    (P:SimpleGraph V) (π:Equiv.Perm V) (p k:ℝ) (hp:0<p) (hk:0≤k) (hsum:2*p+2*k≤1)
    (d:ℕ) (hd:2≤d) (q:U→Γ→ℝ) (hq:∀u g,0≤q u g) (hQ:∀u,∑g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀u j,0≤s u j) (hS:∀u,∑j,s u j≤ intervalUncoveredProbability d (∑g,q u g))
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (n:I→ℕ) (hn:∀i,1≤n i) (hnV:0<Fintype.card V) (g:I→Γ) (j:I→Color)
    (D τ ε:ℝ) (hD:0<D) (hspos:∀i u,0<s u (j i))
    (η:I→U→ℝ) (hη:∀i u,0≤η i u)
    (w:∀i,OrdinaryCycle P (n i+2)→ℝ) (hw:∀i C,0≤w i C)
    (B:I→ℝ) (hB:∀i,0≤B i) (hb:∀i C,w i C≤B i/(Fintype.card V:ℝ)^(n i))
    (Active:Finset I)
    (he:∀i∈Active,∀x y,(∑C,if C.val.val.Adj x y then w i C else 0)=if P.Adj x y then 1 else 0)
    (hdeg:∀x,|(P.degree x:ℝ)-D|≤ε*(Fintype.card V:ℝ))
    (hbudgetV:∀i∈Active,6*((n i+2:ℕ):ℝ)^4*B i*(2*(3*d))+ε*(Fintype.card V:ℝ)≤τ*D)
    (hbudgetE:∀i∈Active,5*((n i+2:ℕ):ℝ)^4*B i*(2*(3*d))/Fintype.card V≤τ)
    (σ:RawMarkedOutcome V U Γ Color) (t:I→ℝ):
    let weight:=fun i=>physicalOrdinaryTupleWeight (π:=π) (b:=3*d) (hn i) (w i)
    let seed:=fun i (W:OrderedOrdinaryWheel (U:=U) π (3*d) (n i+2))=>
      η i W.2*weight i W.1.val/(((n i+2:ℕ):ℝ)*D*p^(n i+2)*(s W.2 (j i))^(n i+1));
    (∀i∈Active,∀root,|resourcePatternLoad orderedOrdinaryResources (seed i) (fun _ _=>true) root
      (orderedOrdinaryResourceState P π d (g i) (j i) σ)-
      ∑W,(if root∈orderedOrdinaryResources W then seed i W else 0)*
        ∏a∈orderedOrdinaryResources W\{root},rawMarkedWheelMarginal P π d p k q s (g i) (j i) (orderedOrdinaryResourceEmbedding a)|<t i)→
    ∀i∈Active,
    (∀v u,|resourcePatternLoad orderedOrdinaryResources (seed i) (fun _ _=>true) (Sum.inr (v,u))
      (orderedOrdinaryResourceState P π d (g i) (j i) σ)-η i u|<t i+τ*η i u) ∧
    (∀x y,P.Adj x y→¬PermutationClose π (3*d) x y→
      |resourcePatternLoad orderedOrdinaryResources (seed i) (fun _ _=>true) (Sum.inl (x,y))
        (orderedOrdinaryResourceState P π d (g i) (j i) σ)-(∑u,η i u*s u (j i))/(D*p)|<
          t i+τ*((∑u,η i u*s u (j i))/(D*p))) :=by
  intro weight seed hconc i hi
  exact physical_ordinary_all_targets_from_concentration P π p k hp hk hsum d hd q hq hQ s hs hS hnoshort
    (n i) (hn i) hnV (g i) (j i) D τ ε hD (hspos i) (η i) (hη i) (w i) (hw i) (B i) (hB i) (hb i)
    (he i hi) hdeg (hbudgetV i hi) (hbudgetE i hi) σ (t i) (hconc i hi)
end Oberwolfach

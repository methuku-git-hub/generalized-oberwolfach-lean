module

public import Oberwolfach.PhysicalOrdinarySampledTarget
public import Oberwolfach.PhysicalOrdinarySampledRimTarget

@[expose] public section
/-! Convert the fixed physical-cycle seed's all-root concentration event
into its spoke and rim targets on the same sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem physical_ordinary_all_targets_from_concentration
    (P:SimpleGraph V) (π:Equiv.Perm V) (p k:ℝ) (hp:0<p) (hk:0≤k) (hsum:2*p+2*k≤1)
    (d:ℕ) (hd:2≤d) (q:U→Γ→ℝ) (hq:∀u g,0≤q u g) (hQ:∀u,∑g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀u j,0≤s u j) (hS:∀u,∑j,s u j≤ intervalUncoveredProbability d (∑g,q u g))
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (n:ℕ) (hn:1≤n) (hnV:0<Fintype.card V) (g:Γ) (j:Color) (D τ ε:ℝ) (hD:0<D) (hspos:∀u,0<s u j)
    (η:U→ℝ) (hη:∀u,0≤η u) (w:OrdinaryCycle P (n+2)→ℝ) (hw:∀C,0≤w C)
    (B:ℝ) (hB:0≤B) (hb:∀C,w C≤B/(Fintype.card V:ℝ)^n)
    (he:∀x y,(∑C,if C.val.val.Adj x y then w C else 0)=if P.Adj x y then 1 else 0)
    (hdeg:∀x,|(P.degree x:ℝ)-D|≤ε*(Fintype.card V:ℝ))
    (hbudgetV:6*((n+2:ℕ):ℝ)^4*B*(2*(3*d))+ε*(Fintype.card V:ℝ)≤τ*D)
    (hbudgetE:5*((n+2:ℕ):ℝ)^4*B*(2*(3*d))/Fintype.card V≤τ)
    (σ:RawMarkedOutcome V U Γ Color) (t:ℝ):
    let weight:=physicalOrdinaryTupleWeight (π:=π) (b:=3*d) hn w
    let seed:=fun W:OrderedOrdinaryWheel (U:=U) π (3*d) (n+2)=>η W.2*weight W.1.val/(((n+2:ℕ):ℝ)*D*p^(n+2)*(s W.2 j)^(n+1));
    (∀root,|resourcePatternLoad orderedOrdinaryResources seed (fun _ _=>true) root
      (orderedOrdinaryResourceState P π d g j σ)-
      ∑W,(if root∈orderedOrdinaryResources W then seed W else 0)*
        ∏a∈orderedOrdinaryResources W\{root},rawMarkedWheelMarginal P π d p k q s g j (orderedOrdinaryResourceEmbedding a)|<t)→
    (∀v u,|resourcePatternLoad orderedOrdinaryResources seed (fun _ _=>true) (Sum.inr (v,u))
      (orderedOrdinaryResourceState P π d g j σ)-η u|<t+τ*η u) ∧
    (∀x y,P.Adj x y→¬PermutationClose π (3*d) x y→
      |resourcePatternLoad orderedOrdinaryResources seed (fun _ _=>true) (Sum.inl (x,y))
        (orderedOrdinaryResourceState P π d g j σ)-(∑u,η u*s u j)/(D*p)|<
          t+τ*((∑u,η u*s u j)/(D*p))) :=by
  intro weight seed hconc
  constructor
  · intro v u
    apply physical_ordinary_sampled_spoke_target P π p k hp hk hsum d hd q hq hQ s hs hS hnoshort n hn hnV g j D τ ε hD hspos η hη w hw B hB hb he hdeg hbudgetV v u σ t
    exact hconc (Sum.inr (v,u))
  · intro x y hxy hclose
    apply physical_ordinary_sampled_rim_target P π p k hp hk hsum d hd q hq hQ s hs hS hnoshort n hn hnV g j D τ ε hD hspos η hη w hw B hB hb he hbudgetE x y hxy hclose σ t
    exact hconc (Sum.inl (x,y))
end Oberwolfach

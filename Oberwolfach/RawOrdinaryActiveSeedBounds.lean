module

public import Oberwolfach.OrdinaryRetainedActiveSeedBounds
public import Oberwolfach.PhysicalOrdinaryFrequencyTargets
public import Oberwolfach.MarkedExpandedApproximateProjection

@[expose] public section
/-! The original ordinary frequency targets hold at each active raw
approximate rim or spoke resource. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [Nonempty V] [LinearOrder V] [DecidableEq U]

theorem raw_ordinary_active_seed_bounds
    (P:SimpleGraph V) (π:Equiv.Perm V) (d n:ℕ) (hd:2≤d) (hn:1≤n)
    (p k:ℝ) (hp:0<p) (hk:0≤k) (hsum:2*p+2*k≤1)
    (q:U→Bool→ℝ) (hq:∀u g,0≤q u g) (hQ:∀u,∑g,q u g≤1/8)
    (s:U→Bool→ℝ) (hs:∀u j,0≤s u j)
    (hS:∀u,∑j,s u j≤ intervalUncoveredProbability d (∑g,q u g))
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (g j:Bool) (D τ ε θ B t:ℝ) (hD:0<D) (hB:0≤B) (hspos:∀u,0<s u j)
    (η f:U→ℝ) (hη:∀u,0≤η u) (hηexact:∀u,η u=(1-θ)*f u/s u j)
    (w:OrdinaryCycle P (n+2)→ℝ) (hw:∀C,0≤w C)
    (hb:∀C,w C≤B/(Fintype.card V:ℝ)^n)
    (he:∀x y,(∑C,if C.val.val.Adj x y then w C else 0)=if P.Adj x y then 1 else 0)
    (hdeg:∀x,|(P.degree x:ℝ)-D|≤ε*(Fintype.card V:ℝ))
    (hbudgetV:6*((n+2:ℕ):ℝ)^4*B*(2*(3*d))+ε*(Fintype.card V:ℝ)≤τ*D)
    (hbudgetE:5*((n+2:ℕ):ℝ)^4*B*(2*(3*d))/Fintype.card V≤τ)
    (σ:RawMarkedOutcome V U Bool Bool)
:
    let R:=fun e:V×V=>rawMarkedPairRims P π d σ (Sum.inl e)
    let H:=rawMarkedSpokes π d (fun e=>σ (Sum.inr e)) g j false
    let weight:=physicalOrdinaryTupleWeight (π:=π) (b:=3*d) hn w
    let seed:=fun W:OrderedOrdinaryWheel (U:=U) π (3*d) (n+2)=>
      η W.2*weight W.1.val/(((n+2:ℕ):ℝ)*D*p^(n+2)*(s W.2 j)^(n+1))
    (∀root,|resourcePatternLoad orderedOrdinaryResources seed (fun _ _=>true) root
      (orderedOrdinaryResourceState P π d g j σ)-
      ∑W,(if root∈orderedOrdinaryResources W then seed W else 0)*
        ∏a∈orderedOrdinaryResources W\{root},rawMarkedWheelMarginal P π d p k q s g j
          (orderedOrdinaryResourceEmbedding a)|<t) →
    ∀root,decide (ordinaryPotentialKeep R H root)=true →
      |resourcePatternLoad orderedOrdinaryResources seed (fun _ _=>true) root
        (fun e=>decide (ordinaryPotentialKeep R H e))-ordinarySeedRootTarget D p θ f η root|≤
        t+τ*ordinarySeedRootTarget D p θ f η root := by
  intro R H weight seed hconc root hactive
  have hnV:0<Fintype.card V:=Fintype.card_pos
  have htarg:=physical_ordinary_frequency_targets_from_concentration P π p k hp hk hsum d hd q hq hQ s hs hS
    hnoshort n hn hnV g j D τ ε hD hspos η hη θ f hηexact w hw B hB hb he hdeg hbudgetV hbudgetE σ t hconc
  have hraw:|resourcePatternLoad orderedOrdinaryResources seed (fun _ _=>true) root
      (orderedOrdinaryResourceState P π d g j σ)-ordinarySeedRootTarget D p θ f η root|≤
      t+τ*ordinarySeedRootTarget D p θ f η root := by
    cases root with
    | inl xy=>
      rcases xy with ⟨x,y⟩
      have hR:R (x,y):=by simpa [ordinaryPotentialKeep] using hactive
      have hr:markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) false x y=1 := by
        simpa [R,rawMarkedPairRims] using hR
      have hh:=(markedPhysicalRim_eq_one_iff P π (3*d) (fun e=>σ (Sum.inl e)) false x y).mp hr
      simpa [ordinarySeedRootTarget,seed,weight] using (htarg.2 x y hh.2.1 hh.1).le
    | inr vu=>
      rcases vu with ⟨v,u⟩
      simpa [ordinarySeedRootTarget,seed,weight] using (htarg.1 v u).le
  have hstate : (fun e=>decide (ordinaryPotentialKeep R (rawMarkedSpokes π d (fun e=>σ (Sum.inr e)) g j false) e)) =
      orderedOrdinaryResourceState P π d g j σ := by
    funext e
    cases e with
    | inl xy=>simp [ordinaryPotentialKeep,R,orderedOrdinaryResourceState,typedMarkedResourceState,orderedOrdinaryResourceEmbedding]
    | inr vu=>simp [ordinaryPotentialKeep,orderedOrdinaryResourceState,typedMarkedResourceState,
        orderedOrdinaryResourceEmbedding,rawMarkedPairSpokes]
  rw [←hstate] at hraw
  exact hraw
end Oberwolfach

module

public import Oberwolfach.RawOrdinaryActiveSeedBounds
public import Oberwolfach.LongSeedEvents
public import Oberwolfach.MarkedOrdinaryRetainedState

@[expose] public section
/-! Express the active ordinary target estimate using the named event and
the common typed raw sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [Nonempty V] [LinearOrder V] [DecidableEq U]

theorem raw_ordinary_named_seed_active_targets
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
    (σ:RawMarkedOutcome V U Bool Bool):
    let state:=typedMarkedResourceState (rawMarkedPairRims P π d σ) (rawMarkedPairSpokes π d σ g j)
    let weight:=physicalOrdinaryTupleWeight (π:=π) (b:=3*d) hn w
    let seed:=fun W:OrderedOrdinaryWheel (U:=U) π (3*d) (n+2)=>
      η W.2*weight W.1.val/(((n+2:ℕ):ℝ)*D*p^(n+2)*(s W.2 j)^(n+1))
    rawOrdinarySeedConcentrated P π d (n+2) p k q s g j t seed σ →
    ∀root,state (ordinaryMarkedResourceEmbedding root)=true→
      |resourcePatternLoad orderedOrdinaryResources seed (fun _ _=>true) root
        (fun x=>state (ordinaryMarkedResourceEmbedding x))-ordinarySeedRootTarget D p θ f η root|≤
        t+τ*ordinarySeedRootTarget D p θ f η root :=by
  intro state weight seed hconc root hactive
  have hpull:=ordinary_marked_state_pullback (rawMarkedPairRims P π d σ) (rawMarkedPairSpokes π d σ g j)
  have hactive':decide (ordinaryPotentialKeep (fun xy=>rawMarkedPairRims P π d σ (Sum.inl xy))
      (rawMarkedSpokes π d (fun e=>σ (Sum.inr e)) g j false) root)=true:=by
    have hh:=congrFun hpull root
    simpa only [state,rawMarkedPairSpokes] using hh.symm.trans hactive
  have hraw:=raw_ordinary_active_seed_bounds P π d n hd hn p k hp hk hsum q hq hQ s hs hS hnoshort
    g j D τ ε θ B t hD hB hspos η f hη hηexact w hw hb he hdeg hbudgetV hbudgetE σ
    (by exact hconc) root hactive'
  simpa only [state,ordinary_marked_state_pullback,rawMarkedPairSpokes] using hraw
end Oberwolfach

module

public import Oberwolfach.PhysicalOrdinarySampledHubFrequency
public import Oberwolfach.OrdinaryExpandedHubTotalEvent

@[expose] public section
/-! Convert all full hub-weight tests on an expanded outcome to the
frequency targets, using the same cycle weights and sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U I:Type} [Fintype V] [Fintype U] [Fintype I] [LinearOrder V] [DecidableEq U]

theorem physical_ordinary_expanded_hub_frequencies
    (P:SimpleGraph V) (π:Equiv.Perm V) (p k:ℝ) (hp:0<p) (hk:0≤k) (hsum:2*p+2*k≤1)
    (d:ℕ) (hd:2≤d) (q:U→Bool→ℝ) (hq:∀u g,0≤q u g) (hQ:∀u,∑g,q u g≤1/8)
    (s:U→Bool→ℝ) (hs:∀u j,0≤s u j) (hS:∀u,∑j,s u j≤ intervalUncoveredProbability d (∑g,q u g))
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (f:I→ℕ) (hf:∀i,1≤f i) (hV:0<Fintype.card V) (D τ ε θ t:ℝ) (hD:0<D) (hτ:0≤τ)
    (hspos:∀u,0<s u true) (η:I→U→ℝ) (hη:∀i u,0≤η i u) (freq:I→U→ℝ)
    (hfreq:∀i u,η i u*s u true=(1-θ)*freq i u)
    (w:∀i,OrdinaryCycle P (f i+2)→ℝ) (hw0:∀i C,0≤w i C)
    (B:I→ℝ) (hB:∀i,0≤B i) (hb:∀i C,w i C≤B i/(Fintype.card V:ℝ)^(f i))
    (he:∀i x y,(∑C,if C.val.val.Adj x y then w i C else 0)=if P.Adj x y then 1 else 0)
    (hdeg:∀x,|(P.degree x:ℝ)-D|≤ε*(Fintype.card V:ℝ))
    (hbudget:∀i,6*((f i+2:ℕ):ℝ)^4*(B i)*(2*(3*d))+ε*(Fintype.card V:ℝ)≤τ*D)
    (σ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Bool Bool e):
    let raw:RawMarkedOutcome V U Bool Bool:=fun e=>rawExpandedApproximateCollapse e (σ e)
    let seed:=fun i (W:OrderedOrdinaryWheel (U:=U) π (3*d) (f i+2))=>η i W.2*
      physicalOrdinaryTupleWeight (π:=π) (b:=3*d) (hf i) (w i) W.1.val/
      (((f i+2:ℕ):ℝ)*D*p^(f i+2)*(s W.2 true)^(f i+1));
    OrdinaryExpandedHubTotalEvent P π d (fun i=>f i+1) p k q s seed (fun _=>true) (fun _=>true) (fun _=>t) σ→
    ∀i u,
      let target:ℝ:=(1-θ)*freq i u*(Fintype.card V:ℝ)/((f i+2:ℕ):ℝ);
      |orderedOrdinarySampledHubTotal P π d (f i+1) (seed i) true true u raw-target|<
        t*(Fintype.card V:ℝ)+τ*target :=by
  intro raw seed htotal i u target
  have hh:=physical_ordinary_sampled_hub_frequency P π p k hp hk hsum d hd q hq hQ s hs hS hnoshort
    (f i) (hf i) hV true true D τ ε hD hτ hspos (η i) (hη i) (w i) (hw0 i)
    (B i) (hB i) (hb i) (he i) hdeg (hbudget i) u θ (freq i u) (t*(Fintype.card V:ℝ)) (hfreq i u) raw
  apply hh
  exact htotal i u
end Oberwolfach

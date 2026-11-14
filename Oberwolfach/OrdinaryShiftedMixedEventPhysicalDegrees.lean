module

public import Oberwolfach.OrdinaryShiftedMarkedRootTargets
public import Oberwolfach.OrdinaryShiftedUnmarkedRootTargets
public import Oberwolfach.OrdinaryShiftedMixedEventRootTargets
public import Oberwolfach.OrdinaryMixedGenericPhysicalDegrees
public import Oberwolfach.OrdinaryShiftedMixedLoadEvent

@[expose] public section
/-! The marked and unmarked concentration tests give the family-wise
ideal root targets on one and the same wheel sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U I:Type} [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U] [Fintype I]

theorem ordinary_shifted_mixed_event_physical_degrees
    (P:SimpleGraph (V)) (π:Equiv.Perm (V)) (p k:ℝ) (hp:0<p) (hk:0≤k) (hsum:2*p+2*k≤1)
    (d:ℕ) (hd:2≤d) (q:U→Bool→ℝ) (hq:∀ u g,0≤q u g) (hQ:∀ u,∑ g,q u g≤1/8)
    (s:U→Bool→ℝ) (hs:∀ u j,0≤s u j) (hS:∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
    (hnoshort:∀ x l,0<l→l<2*d+1→(π^l) x≠x)
    (m:ℕ) (hm:2≤m) (f:I→ℕ) (hf:∀i,1≤f i) (hV:0<Fintype.card V)
    (D τ ε A BM t:ℝ) (hD:0<D) (ht:0≤t) (hspos:∀u,0<s u true)
    (weight:(Fin (m+1)→V)→ℝ)
    (hw:SuccessorSequenceWeightConditions P π (3*d) D τ A BM weight)
    (η:I→U→ℝ) (hη:∀i u,0≤η i u)
    (w:∀i,OrdinaryCycle P (f i+2)→ℝ) (hw0:∀i C,0≤w i C)
    (B:I→ℝ) (hB:∀i,0≤B i) (hb:∀i C,w i C≤B i/(Fintype.card V:ℝ)^(f i))
    (he:∀i x y,(∑C,if C.val.val.Adj x y then w i C else 0)=if P.Adj x y then 1 else 0)
    (hdeg:∀x,|(P.degree x:ℝ)-D|≤ε*(Fintype.card V:ℝ))
    (hbudgetS:∀i,6*((f i+2:ℕ):ℝ)^4*(B i)*(2*(3*d))+ε*(Fintype.card V:ℝ)≤τ*D)
    (hbudgetR:∀i,5*((f i+2:ℕ):ℝ)^4*(B i)*(2*(3*d))/(Fintype.card V:ℝ)≤τ)
    (σ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Bool Bool e):
    let raw:RawMarkedOutcome V U Bool Bool:=fun e=>rawExpandedApproximateCollapse e (σ e)
    let seedM:=fun W:MarkedWheel (Prod.fst:V×V→V) Prod.snd Prod.fst Prod.snd m π (3*d)
      (fun _ (_:U)=>True) (fun _ (_:U)=>True)=>weight W.1.val/(D*p^(m+1)*(s W.2.val true)^m)
    let seedO:=fun i (W:OrderedOrdinaryWheel (U:=U) π (3*d) (f i+2))=>η i W.2*
      physicalOrdinaryTupleWeight (π:=π) (b:=3*d) (hf i) (w i) W.1.val/
      (((f i+2:ℕ):ℝ)*D*p^(f i+2)*(s W.2 true)^(f i+1))
    let st:=typedMarkedResourceState (ordinaryShiftedPairRims P π d raw) (rawMarkedPairSpokes π d raw true true)
    let R:=ordinaryMixedGenericResources
      (fun W:MarkedWheel (Prod.fst:V×V→V) Prod.snd Prod.fst Prod.snd m π (3*d)
        (fun _ (_:U)=>True) (fun _ (_:U)=>True)=>typedMarkedOccurrenceResources W)
      (fun i (W:OrderedOrdinaryWheel (U:=U) π (3*d) (f i+2))=>orderedOrdinaryResources W)
    let seed:=ordinaryMixedGenericWeight seedM seedO
    let target:=ordinaryMixedIdealTarget (m:ℝ) D p (fun u=>q u true) (fun u=>s u true) η;
    OrdinaryShiftedMixedLoadEvent P π d m (fun i:I=>f i+1) p k q s
      (fun _ _=>True) (fun _ _=>True) (fun _:Unit=>seedM) (fun _=>true) (fun _=>true)
      seedO (fun _=>true) (fun _=>true) t (fun _=>t) σ→
    (∀x u,rawMarkedPairSpokes π d raw true true true x u→q u true≠0)→
    (∀x:PhysicalSampledActive (ordinaryMixedPhysicalResource (U:=U) π) st,
      ∑a∈Finset.univ.filter (fun a=>ordinaryMixedPhysicalResource π a=x.val ∧ st a=true),∑i,target i a=1)→
    ∀x:PhysicalSampledActive (ordinaryMixedPhysicalResource (U:=U) π) st,
      |hypergraphWeightedDegree (physicalSampledCandidateSet (ordinaryMixedPhysicalResource π) (mixedCandidateResources R) st)
        (fun c=>mixedCandidateWeight seed c.val) x-1|≤4*((Fintype.card I:ℝ)+1)*t+τ :=by
  intro raw seedM seedO st R seed target hevent hpositive htarget x
  have hroot:=ordinary_shifted_mixed_event_root_targets P π p k hp hk hsum d hd q hq hQ s hs hS hnoshort
    m hm f hf hV D τ ε A BM t hD ht hspos weight hw η hη w hw0 B hB hb he hdeg hbudgetS hbudgetR σ hevent hpositive
  have hh:=ordinary_mixed_generic_physical_degrees π (3*d) m hm (by omega) f hf seedM seedO st target τ t ht htarget hroot x
  exact hh
end Oberwolfach

module

public import Oberwolfach.OrdinaryShiftedMarkedRootTargets
public import Oberwolfach.OrdinaryShiftedUnmarkedRootTargets
public import Oberwolfach.OrdinaryMixedGenericFamily

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
variable {V U I:Type} [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U] [Fintype I] [DecidableEq I]

theorem ordinary_shifted_retained_mixed_root_targets
    (P:SimpleGraph (V)) (π:Equiv.Perm (V)) (p k:ℝ) (hp:0<p) (hk:0≤k) (hsum:2*p+2*k≤1)
    (d:ℕ) (hd:2≤d) (q:U→Bool→ℝ) (hq:∀ u g,0≤q u g) (hQ:∀ u,∑ g,q u g≤1/8)
    (s:U→Bool→ℝ) (hs:∀ u j,0≤s u j) (hS:∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
    (hnoshort:∀ x l,0<l→l<2*d+1→(π^l) x≠x)
    (m:ℕ) (hm:2≤m) (f:I→ℕ) (hf:∀i,1≤f i) (hV:0<Fintype.card V)
    (D τ ε A BM t:ℝ) (hD:0<D) (ht:0≤t) (hspos:∀u,0<s u true)
    (weight:(Fin (m+1)→V)→ℝ)
    (hw:SuccessorSequenceWeightConditions P π (3*d) D τ A BM weight)
    (η:I→U→ℝ) (hη:∀i u,0≤η i u) (J:Finset I) (hzero:∀i∉J,∀u,η i u=0)
    (w:∀i,OrdinaryCycle P (f i+2)→ℝ) (hw0:∀i C,0≤w i C)
    (B:I→ℝ) (hB:∀i,0≤B i) (hb:∀i C,w i C≤B i/(Fintype.card V:ℝ)^(f i))
    (he:∀i∈J,∀x y,(∑C,if C.val.val.Adj x y then w i C else 0)=if P.Adj x y then 1 else 0)
    (hdeg:∀x,|(P.degree x:ℝ)-D|≤ε*(Fintype.card V:ℝ))
    (hbudgetS:∀i∈J,6*((f i+2:ℕ):ℝ)^4*(B i)*(2*(3*d))+ε*(Fintype.card V:ℝ)≤τ*D)
    (hbudgetR:∀i∈J,5*((f i+2:ℕ):ℝ)^4*(B i)*(2*(3*d))/(Fintype.card V:ℝ)≤τ)
    (σ:RawMarkedOutcome (V) U Bool Bool):
    let seedM:=fun W:MarkedWheel (Prod.fst:V×V→V) Prod.snd Prod.fst Prod.snd m π (3*d)
      (fun _ (_:U)=>True) (fun _ (_:U)=>True)=>weight W.1.val/(D*p^(m+1)*(s W.2.val true)^m)
    let seedO:=fun i (W:OrderedOrdinaryWheel (U:=U) π (3*d) (f i+2))=>η i W.2*
      physicalOrdinaryTupleWeight (π:=π) (b:=3*d) (hf i) (w i) W.1.val/
      (((f i+2:ℕ):ℝ)*D*p^(f i+2)*(s W.2 true)^(f i+1))
    let st:=typedMarkedResourceState (ordinaryShiftedPairRims P π d σ) (rawMarkedPairSpokes π d σ true true)
    let R:=ordinaryMixedGenericResources
      (fun W:MarkedWheel (Prod.fst:V×V→V) Prod.snd Prod.fst Prod.snd m π (3*d)
        (fun _ (_:U)=>True) (fun _ (_:U)=>True)=>typedMarkedOccurrenceResources W)
      (fun i (W:OrderedOrdinaryWheel (U:=U) π (3*d) (f i+2))=>orderedOrdinaryResources W)
    let seed:=ordinaryMixedGenericWeight seedM seedO
    let target:=ordinaryMixedIdealTarget (m:ℝ) D p (fun u=>q u true) (fun u=>s u true) η;
    (∀ root,|typedMarkedPotentialLoad seedM (ordinaryShiftedPairRims P π d σ) (rawMarkedPairSpokes π d σ true true) root-
        ∑ W,(if root∈typedMarkedOccurrenceResources W then seedM W else 0)*
          ∏ a∈typedMarkedOccurrenceResources W\{root},rawMarkedWheelMarginal P π d p p q s true true a|<t)→
    (∀i root,|resourcePatternLoad orderedOrdinaryResources (seedO i) (fun _ _=>true) root
      (orderedOrdinaryResourceState P π d true true σ)-
      ∑ W,(if root∈orderedOrdinaryResources W then seedO i W else 0)*
        ∏ a∈orderedOrdinaryResources W\{root},rawMarkedWheelMarginal P π d p k q s true true (orderedOrdinaryResourceEmbedding a)|<t)→
    (∀x u,rawMarkedPairSpokes π d σ true true true x u→q u true≠0)→
    ∀i root,st root=true→
      |resourcePatternLoad (R i) (seed i) (fun _ _=>true) root st-target i root|≤t+τ*target i root :=by
  intro seedM seedO st R seed target hM hO hpositive i root hactive
  cases i with
  | none=>
    have ha : Sum.elim (ordinaryShiftedPairRims P π d σ)
        (fun z=>rawMarkedPairSpokes π d σ true true z.1 z.2.1 z.2.2) root:=by
      simpa only [st,typedMarkedResourceState,decide_eq_true_eq] using hactive
    have hh:=ordinary_shifted_marked_root_targets P π p k hp hk hsum d hd q hq hQ s hs hS
      hnoshort m hm D τ A BM t hD hspos weight hw η σ hM hpositive root ha
    rw [typedMarkedPotentialLoad_eq_pattern] at hh
    dsimp only [R,seed,target,ordinaryMixedGenericResources,ordinaryMixedGenericWeight,st,seedM]
    convert hh using 1 <;> (try simp only [ordinaryMixedGenericResources,ordinaryMixedGenericWeight]) <;> congr! 3
  | some i=>
    by_cases hi:i∈J
    · have hh:=ordinary_shifted_unmarked_root_targets P π p k hp hk hsum d hd q hq hQ s hs hS hnoshort
        (f i) (hf i) hV D τ ε hD hspos (m:ℝ) η i (hη i) (w i) (hw0 i)
        (B i) (hB i) (by simpa using hb i) (he i hi) (by simpa using hdeg)
        (by simpa using hbudgetS i hi) (by simpa using hbudgetR i hi) σ t ht (hO i) root hactive
      dsimp only [R,seed,target,ordinaryMixedGenericResources,ordinaryMixedGenericWeight,st,seedO]
      convert hh using 1 <;> (try simp only [ordinaryMixedGenericResources,ordinaryMixedGenericWeight]) <;> congr! 3
    · have hz:∀u,η i u=0:=hzero i hi
      have hweight:∀W,seedO i W=0:=by
        intro W
        simp only [seedO,hz,zero_mul,zero_div]
      have hloadzero:resourcePatternLoad (R (some i)) (seed (some i)) (fun _ _=>true) root st=0:=by
        unfold resourcePatternLoad
        apply Finset.sum_eq_zero
        intro W _
        have hw0:seed (some i) W=0:=by
          change seedO i W=0
          exact hweight W
        simp [hw0]
      have htargetzero:target (some i) root=0:=by
        cases root with
        | inl a=>cases a <;> simp [target,ordinaryMixedIdealTarget,hz]
        | inr a=>rcases a with ⟨b,v,u⟩;cases b <;> simp [target,ordinaryMixedIdealTarget,hz]
      simp only [hloadzero,htargetzero,sub_zero,abs_zero,mul_zero,add_zero]
      exact ht
end Oberwolfach

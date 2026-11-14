module

public import Oberwolfach.OrdinaryShiftedUnmarkedLoadBridge
public import Oberwolfach.OrdinaryMixedIdealTarget
public import Oberwolfach.PhysicalOrdinarySampledTarget
public import Oberwolfach.PhysicalOrdinarySampledRimTarget

@[expose] public section
/-! Pointwise unmarked-cycle loads in the common shifted resource universe. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U I:Type} [Fintype V] [Fintype U] [Fintype I]
  [LinearOrder V] [DecidableEq U]

theorem ordinary_shifted_unmarked_root_targets
    (P:SimpleGraph V) (π:Equiv.Perm V) (p k:ℝ) (hp:0<p) (hk:0≤k) (hsum:2*p+2*k≤1)
    (d:ℕ) (hd:2≤d) (q:U→Bool→ℝ) (hq:∀ u g,0≤q u g) (hQ:∀ u,∑ g,q u g≤1/8)
    (s:U→Bool→ℝ) (hs:∀ u j,0≤s u j) (hS:∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
    (hnoshort:∀ x l,0<l→l<2*d+1→(π^l) x≠x)
    (n:ℕ) (hn:1≤n) (hnV:0<Fintype.card V) (D τ ε:ℝ) (hD:0<D) (hspos:∀ u,0<s u true)
    (m:ℝ) (η:I→U→ℝ) (i:I) (hη:∀ u,0≤η i u) (w:OrdinaryCycle P (n+2)→ℝ) (hw:∀ C,0≤w C)
    (B:ℝ) (hB:0≤B) (hb:∀ C,w C≤B/(Fintype.card V:ℝ)^n)
    (he:∀ x y,(∑ C,if C.val.val.Adj x y then w C else 0)=if P.Adj x y then 1 else 0)
    (hdeg:∀ x,|(P.degree x:ℝ)-D|≤ε*(Fintype.card V:ℝ))
    (hbudgetS:6*((n+2:ℕ):ℝ)^4*B*(2*(3*d))+ε*(Fintype.card V:ℝ)≤τ*D)
    (hbudgetR:5*((n+2:ℕ):ℝ)^4*B*(2*(3*d))/Fintype.card V≤τ)
    (σ:RawMarkedOutcome V U Bool Bool) (t:ℝ) (ht:0≤t):
    let seed:=fun W:OrderedOrdinaryWheel (U:=U) π (3*d) (n+2)=>η i W.2*
      physicalOrdinaryTupleWeight (π:=π) (b:=3*d) hn w W.1.val/
      (((n+2:ℕ):ℝ)*D*p^(n+2)*(s W.2 true)^(n+1))
    let st:=typedMarkedResourceState (ordinaryShiftedPairRims P π d σ) (rawMarkedPairSpokes π d σ true true)
    let R:=fun W:OrderedOrdinaryWheel (U:=U) π (3*d) (n+2)=>(orderedOrdinaryResources W).map ordinaryMarkedResourceEmbedding;
    (∀ root,|resourcePatternLoad orderedOrdinaryResources seed (fun _ _=>true) root
      (orderedOrdinaryResourceState P π d true true σ)-
      ∑ W,(if root∈orderedOrdinaryResources W then seed W else 0)*
        ∏ a∈orderedOrdinaryResources W\{root},rawMarkedWheelMarginal P π d p k q s true true (orderedOrdinaryResourceEmbedding a)|<t)→
    ∀ root,st root=true→
    |resourcePatternLoad R seed (fun _ _=>true) root st-
      ordinaryMixedIdealTarget m D p (fun u=>q u true) (fun u=>s u true) η (some i) root|≤
      t+τ*ordinaryMixedIdealTarget m D p (fun u=>q u true) (fun u=>s u true) η (some i) root :=by
  intro seed st R hconc root hactive
  cases root with
  | inl a=>
    cases a with
    | inl xy=>
      obtain ⟨x,y⟩:=xy
      have ha:¬PermutationClose π (3*d) x y ∧ P.Adj x y :=by
        have hh:=hactive
        simp only [st,typedMarkedResourceState,Sum.elim_inl,ordinaryShiftedPairRims,decide_eq_true_eq] at hh
        exact ⟨hh.1,hh.2.1⟩
      have hh:=physical_ordinary_sampled_rim_target P π p k hp hk hsum d hd q hq hQ s hs hS hnoshort
        n hn hnV true true D τ ε hD hspos (η i) hη w hw B hB hb he hbudgetR x y ha.2 ha.1 σ t (hconc (Sum.inl (x,y)))
      have heq:=ordinary_shifted_unmarked_load_bridge P π d true true σ orderedOrdinaryResources seed (Sum.inl (x,y))
      change resourcePatternLoad R seed (fun _ _=>true) (Sum.inl (Sum.inl (x,y))) st = _ at heq
      rw [←heq] at hh
      simpa only [ordinaryMixedIdealTarget] using hh.le
    | inr xy=>
      have hz:=ordinary_load_zero_at_nonordinary_resource orderedOrdinaryResources seed
        (ordinaryShiftedPairRims P π d σ) (rawMarkedPairSpokes π d σ true true) (Sum.inl (Sum.inr xy)) (by
          intro z
          cases z <;> simp [orderedOrdinaryResourceEmbedding])
      change resourcePatternLoad R seed (fun _ _=>true) (Sum.inl (Sum.inr xy)) st=0 at hz
      simp only [ordinaryMixedIdealTarget,hz,sub_zero,abs_zero,mul_zero,add_zero]
      exact ht
  | inr z=>
    obtain ⟨b,x,u⟩:=z
    cases b with
    | false=>
      have hh:=physical_ordinary_sampled_spoke_target P π p k hp hk hsum d hd q hq hQ s hs hS hnoshort
        n hn hnV true true D τ ε hD hspos (η i) hη w hw B hB hb he hdeg hbudgetS x u σ t (hconc (Sum.inr (x,u)))
      have heq:=ordinary_shifted_unmarked_load_bridge P π d true true σ orderedOrdinaryResources seed (Sum.inr (x,u))
      change resourcePatternLoad R seed (fun _ _=>true) (Sum.inr (false,x,u)) st = _ at heq
      rw [←heq] at hh
      simpa only [ordinaryMixedIdealTarget] using hh.le
    | true=>
      have hz:=ordinary_load_zero_at_nonordinary_resource orderedOrdinaryResources seed
        (ordinaryShiftedPairRims P π d σ) (rawMarkedPairSpokes π d σ true true) (Sum.inr (true,x,u)) (by
          intro z
          cases z <;> simp [orderedOrdinaryResourceEmbedding])
      change resourcePatternLoad R seed (fun _ _=>true) (Sum.inr (true,x,u)) st=0 at hz
      simp only [ordinaryMixedIdealTarget,hz,sub_zero,abs_zero,mul_zero,add_zero]
      exact ht
end Oberwolfach

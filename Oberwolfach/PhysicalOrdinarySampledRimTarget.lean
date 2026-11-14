module

public import Oberwolfach.OrdinarySampledSpokeTarget
public import Oberwolfach.OrdinarySampledRimTarget
public import Oberwolfach.PhysicalOrdinaryPositional

@[expose] public section
/-! The positional estimates and the sampled targets refer to the same
physical fractional cycle weights. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem physical_ordinary_sampled_rim_target
    (P:SimpleGraph V) (π:Equiv.Perm V) (p k:ℝ) (hp:0<p) (hk:0≤k) (hsum:2*p+2*k≤1)
    (d:ℕ) (hd:2≤d) (q:U→Γ→ℝ) (hq:∀ u g,0≤q u g) (hQ:∀ u,∑ g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀ u j,0≤s u j) (hS:∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
    (hnoshort:∀ x l,0<l→l<2*d+1→(π^l) x≠x)
    (n:ℕ) (hn:1≤n) (hnV:0<Fintype.card V) (g:Γ) (j:Color) (D τ ε:ℝ) (hD:0<D) (hspos:∀ u,0<s u j)
    (η:U→ℝ) (hη:∀ u,0≤η u) (w:OrdinaryCycle P (n+2)→ℝ) (hw:∀ C,0≤w C)
    (B:ℝ) (hB:0≤B) (hb:∀ C,w C≤B/(Fintype.card V:ℝ)^n)
    (he:∀ x y,(∑ C,if C.val.val.Adj x y then w C else 0)=if P.Adj x y then 1 else 0)
    (hbudget:5*((n+2:ℕ):ℝ)^4*B*(2*(3*d))/Fintype.card V≤τ)
    (x y:V) (hxy:P.Adj x y) (hclose:¬PermutationClose π (3*d) x y) (σ:∀ e:RawWheelCoordinate V U,RawMarkedCoordinateState Γ Color e) (t:ℝ) :
    let weight:=physicalOrdinaryTupleWeight (π:=π) (b:=3*d) hn w
    let seed:=fun W:OrderedOrdinaryWheel (U:=U) π (3*d) (n+2)=>η W.2*weight W.1.val/(((n+2:ℕ):ℝ)*D*p^(n+2)*(s W.2 j)^(n+1))
    let load:=resourcePatternLoad orderedOrdinaryResources seed (fun _ _=>true) (Sum.inl (x,y)) (orderedOrdinaryResourceState P π d g j σ)
    let rootMean:=∑ W,(if Sum.inl (x,y)∈orderedOrdinaryResources W then seed W else 0)*
      ∏ a∈orderedOrdinaryResources W\{Sum.inl (x,y)},rawMarkedWheelMarginal P π d p k q s g j (orderedOrdinaryResourceEmbedding a)
    |load-rootMean|<t → |load-(∑ u,η u*s u j)/(D*p)|<t+τ*((∑ u,η u*s u j)/(D*p)) := by
  intro weight seed load rootMean hload
  have hsupport:∀ W:OrderedOrdinaryWheel (U:=U) π (3*d) (n+2),weight W.1.val≠0→
      ∀ i,P.Adj (W.1.val i) (W.1.val (cycleNext i)):=by
    intro W h
    exact (physicalOrdinaryTupleWeight_support (π:=π) (b:=3*d) hn w W.1.val h).2
  have hpos:∀ i:Fin (n+2),1-τ≤(∑ C:{C:Fin (n+2)→V // PermutationSeparated π (3*d) C},if C.val i=x ∧ C.val (cycleNext i)=y then weight C.val else 0) ∧
      (∑ C:{C:Fin (n+2)→V // PermutationSeparated π (3*d) C},if C.val i=x ∧ C.val (cycleNext i)=y then weight C.val else 0)≤1+τ:=by
    intro i
    apply physicalOrdinaryTupleWeight_edge_positions (π:=π) (b:=3*d) hn hnV w hw B hB hb he τ _ i x y hxy hclose
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hbudget
  have ht:=ordinary_sampled_rim_target P π p k hp hk hsum d hd q hq hQ s hs hS hnoshort (n+2) (by omega) g j D τ hD hspos η hη weight hsupport x y hpos σ t
  dsimp only at ht
  exact ht hload
end Oberwolfach

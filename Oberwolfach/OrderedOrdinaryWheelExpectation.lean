module

public import Oberwolfach.OrderedOrdinaryWheelGeometry
public import Oberwolfach.RawMarkedPotentialSampling

@[expose] public section
/-! Exact omitted-root expectation for ordered ordinary wheels on the same
physical and interval experiment as the marked wheels. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

def orderedOrdinaryResourceState (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ)
    (g:Γ) (j:Color) (σ:RawMarkedOutcome V U Γ Color) (a:(V×V)⊕(V×U)):Bool:=
  typedMarkedResourceState (rawMarkedPairRims P π d σ) (rawMarkedPairSpokes π d σ g j)
    (orderedOrdinaryResourceEmbedding a)

theorem orderedOrdinary_resource_supported (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ)
    (g:Γ) (j:Color) (a:(V×V)⊕(V×U)) (σ τ:RawMarkedOutcome V U Γ Color)
    (ha:∀ e∈orderedOrdinaryResourceCoordinates π d a,σ e=τ e):
    orderedOrdinaryResourceState P π d g j σ a=orderedOrdinaryResourceState P π d g j τ a :=by
  exact congrArg (fun Q:Prop=>decide Q) (propext (rawMarkedResourceState_supported P π d g j
    (orderedOrdinaryResourceEmbedding a) σ τ ha))

theorem orderedOrdinary_potential_expectation
    (P:SimpleGraph V) (π:Equiv.Perm V) (p k:ℝ) (hp:0≤p) (hk:0≤k) (hsum:2*p+2*k≤1)
    (d:ℕ) (hd:2≤d) (q:U→Γ→ℝ) (hq:∀ u g,0≤q u g) (hQ:∀ u,∑ g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀ u j,0≤s u j) (hS:∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
    (hnoshort:∀ x l,0<l→l<2*d+1→(π^l) x≠x)
    (r:ℕ) (hr:3≤r) (w:OrderedOrdinaryWheel (U:=U) π (3*d) r→ℝ)
    (g:Γ) (j:Color) (root:(V×V)⊕(V×U)):
    (FiniteLaw.pi (rawMarkedWheelLaw p k hp hk hsum d hd q hq hQ s hs hS)).expectation
      (fun σ=>resourcePatternLoad orderedOrdinaryResources w (fun _ _=>true) root
        (orderedOrdinaryResourceState P π d g j σ))=
      ∑ W,(if root∈orderedOrdinaryResources W then w W else 0)*
        ∏ a∈orderedOrdinaryResources W\{root},rawMarkedWheelMarginal P π d p k q s g j (orderedOrdinaryResourceEmbedding a) :=by
  let μ:=rawMarkedWheelLaw (V:=V) p k hp hk hsum d hd q hq hQ s hs hS
  have hh:=resourcePatternLoad_supported_expectation μ orderedOrdinaryResources w
    (fun _ _=>true) (orderedOrdinaryResourceCoordinates π d) (orderedOrdinaryResourceState P π d g j)
    (orderedOrdinary_resource_supported P π d g j) root
    (by
      intro W _ a ha b hb hab
      exact orderedOrdinaryCoordinates_disjoint d hr W a b (Finset.mem_sdiff.mp ha).1 (Finset.mem_sdiff.mp hb).1 hab)
  rw [hh]
  apply Finset.sum_congr rfl
  intro W _
  congr 1
  apply Finset.prod_congr rfl
  intro a _
  exact rawMarkedResource_probability P π p k hp hk hsum d hd q hq hQ s hs hS hnoshort g j (orderedOrdinaryResourceEmbedding a)
end Oberwolfach

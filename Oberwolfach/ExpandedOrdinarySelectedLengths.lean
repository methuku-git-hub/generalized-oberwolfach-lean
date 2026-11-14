module

public import Oberwolfach.ExpandedOrderedOrdinaryFiniteFamily
public import Mathlib.Data.Fintype.Powerset

@[expose] public section
/-! The family of short lengths may be selected after the order threshold.
The finite ambient family and all numerical constants are fixed beforehand. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem raw_expanded_ordinary_selected_lengths_highProbability
    (K d:ℕ) (hd:2≤d) (m:Fin K→ℕ) (hm:∀ i,2≤m i)
    (B t:Fin K→ℝ) (hB:∀ i,0<B i) (ht:∀ i,0<t i) (ζ:ℝ) (hζ:0<ζ):
    ∃ N:ℕ,∀ (V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [LinearOrder V] [DecidableEq U],
    N≤Fintype.card V→Fintype.card U≤Fintype.card V→
    ∀ (P:SimpleGraph V) (π:Equiv.Perm V)
    (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
    (q:U→Γ→ℝ) (hq:∀ u g,0≤q u g) (hQ:∀ u,∑ g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀ u j,0≤s u j) (hS:∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
    (hnoshort:∀ x l,0<l→l<2*d+1→(π^l) x≠x)
    (S:Finset (Fin K))
    (w:∀ i:{i // i∈S},OrderedOrdinaryWheel (U:=U) π (3*d) (m i.val+1)→ℝ)
    (hw:∀ i W,0≤w i W ∧ w i W≤B i.val/(Fintype.card V:ℝ)^(m i.val))
    (g:{i // i∈S}→Γ) (j:{i // i∈S}→Color)
    (F:RawMarkedOutcome V U Γ Color→Type) [∀ a,Fintype (F a)] (ν:∀ a,FiniteLaw (F a)),
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS)
    let f:=fun (ω:∀ e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e) e=>rawExpandedMarkedCollapse e (ω e)
    1-ζ≤(μ.sigma (fun ω=>ν (f ω))).probability (fun z=>∀ i root,
      |resourcePatternLoad orderedOrdinaryResources (w i) (fun _ _=>true) root
        (orderedOrdinaryResourceState P π d (g i) (j i) (fun e=>rawExpandedApproximateCollapse e (z.1 e)))-
        ∑ W,(if root∈orderedOrdinaryResources W then w i W else 0)*
          ∏ a∈orderedOrdinaryResources W\{root},rawMarkedWheelMarginal P π d p₂ k₂ q s (g i) (j i) (orderedOrdinaryResourceEmbedding a)|<t i.val):=by
  classical
  have hex (S:Finset (Fin K)):=raw_expanded_ordinary_finite_family_highProbability
    {i // i∈S} d hd (fun i=>m i.val) (fun i=>hm i.val)
    (fun i=>B i.val) (fun i=>t i.val) (fun i=>hB i.val) (fun i=>ht i.val) ζ hζ
  choose NS hNS using hex
  refine ⟨Finset.univ.sup NS,?_⟩
  intro V U Γ Color _ _ _ _ _ _ hn hUV P π p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum q hq hQ s hs hS hnoshort S w hw g j F _ ν
  exact hNS S V U Γ Color ((Finset.le_sup (Finset.mem_univ S)).trans hn) hUV P π p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum q hq hQ s hs hS hnoshort w hw g j F ν
end Oberwolfach

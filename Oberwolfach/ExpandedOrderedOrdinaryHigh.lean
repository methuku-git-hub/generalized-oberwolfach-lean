module

public import Oberwolfach.ExpandedOrderedOrdinaryPotentials
public import Oberwolfach.OrderedOrdinaryPotentialFailureAny

@[expose] public section
/-! Arbitrarily small failure probability for all roots of one fixed
ordinary cycle type, on the enriched experiment. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem raw_expanded_approximate_ordered_potentials_highProbability
    (d m:ℕ) (hd:2≤d) (hm:2≤m) (B t ε:ℝ) (hB:0<B) (ht:0<t) (hε:0<ε):
    ∃ N:ℕ,∀ (V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [LinearOrder V] [DecidableEq U],
    N≤Fintype.card V→Fintype.card U≤Fintype.card V→
    ∀ (P:SimpleGraph V) (π:Equiv.Perm V)
    (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
    (q:U→Γ→ℝ) (hq:∀ u g,0≤q u g) (hQ:∀ u,∑ g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀ u j,0≤s u j) (hS:∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
    (hnoshort:∀ x l,0<l→l<2*d+1→(π^l) x≠x)
    (w:OrderedOrdinaryWheel (U:=U) π (3*d) (m+1)→ℝ)
    (hw:∀ W,0≤w W ∧ w W≤B/(Fintype.card V:ℝ)^m)
    (g:Γ) (j:Color)
    (F:RawMarkedOutcome V U Γ Color→Type) [∀ a,Fintype (F a)] (ν:∀ a,FiniteLaw (F a)),
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS)
    let f:=fun (ω:∀ e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e) e=>rawExpandedMarkedCollapse e (ω e)
    1-ε≤(μ.sigma (fun ω=>ν (f ω))).probability (fun z=>∀ root,
      |resourcePatternLoad orderedOrdinaryResources w (fun _ _=>true) root
        (orderedOrdinaryResourceState P π d g j (fun e=>rawExpandedApproximateCollapse e (z.1 e)))-
        ∑ W,(if root∈orderedOrdinaryResources W then w W else 0)*
          ∏ a∈orderedOrdinaryResources W\{root},rawMarkedWheelMarginal P π d p₂ k₂ q s g j (orderedOrdinaryResourceEmbedding a)|<t):=by
  obtain ⟨N,hN⟩:=ordered_ordinary_potential_failure_small_any d m B t ε hB ht hε
  refine ⟨max N 1,?_⟩
  intro V U Γ Color _ _ _ _ _ _ hn huV P π p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum q hq hQ s hs hS hnoshort w hw g j F _ ν
  have hnpos:0<Fintype.card V:=by omega
  have hh:=raw_expanded_approximate_ordered_potentials_event P π p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS
    hnoshort m hm hnpos huV w B hB hw g j t ht F ν
  have hroot:(Fintype.card ((V×V)⊕(V×U)):ℝ)≤4*(Fintype.card V:ℝ)^2:=by
    simp only [Fintype.card_sum,Fintype.card_prod,Nat.cast_add,Nat.cast_mul]
    have huR:(Fintype.card U:ℝ)≤Fintype.card V:=by exact_mod_cast huV
    have hnR:(0:ℝ)≤Fintype.card V:=by positivity
    nlinarith [mul_nonneg hnR (sub_nonneg.mpr huR)]
  have hfail:=hN (Fintype.card V) (le_trans (le_max_left _ _) hn)
  have hbudget:(Fintype.card ((V×V)⊕(V×U)):ℝ)*
      (2*Real.exp (-2*t^2/((8*(d:ℝ)+6)^2*(((m:ℝ)+1)^3*B/Fintype.card V)*(2*((m:ℝ)+1))*(((m:ℝ)+1)^2*B))))≤ε:=by
    have hmull:=mul_le_mul_of_nonneg_right hroot (show 0≤2*Real.exp (-2*t^2/((8*(d:ℝ)+6)^2*(((m:ℝ)+1)^3*B/Fintype.card V)*(2*((m:ℝ)+1))*(((m:ℝ)+1)^2*B))) by positivity)
    nlinarith only [hmull,hfail]
  exact (sub_le_sub_left hbudget 1).trans hh
end Oberwolfach

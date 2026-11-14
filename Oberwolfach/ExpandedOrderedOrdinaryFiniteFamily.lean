module

public import Oberwolfach.ExpandedOrderedOrdinaryHigh
public import Oberwolfach.FiniteHighEventsCommon

@[expose] public section
/-! All fixed ordinary cycle types use one order threshold and one common
concentration event on the enriched experiment. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem raw_expanded_ordinary_finite_family_highProbability
    (I:Type) [Fintype I] (d:ℕ) (hd:2≤d) (m:I→ℕ) (hm:∀ i,2≤m i)
    (B t:I→ℝ) (hB:∀ i,0<B i) (ht:∀ i,0<t i) (ζ:ℝ) (hζ:0<ζ):
    ∃ N:ℕ,∀ (V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [LinearOrder V] [DecidableEq U],
    N≤Fintype.card V→Fintype.card U≤Fintype.card V→
    ∀ (P:SimpleGraph V) (π:Equiv.Perm V)
    (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
    (q:U→Γ→ℝ) (hq:∀ u g,0≤q u g) (hQ:∀ u,∑ g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀ u j,0≤s u j) (hS:∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
    (hnoshort:∀ x l,0<l→l<2*d+1→(π^l) x≠x)
    (w:∀ i,OrderedOrdinaryWheel (U:=U) π (3*d) (m i+1)→ℝ)
    (hw:∀ i W,0≤w i W ∧ w i W≤B i/(Fintype.card V:ℝ)^(m i))
    (g:I→Γ) (j:I→Color)
    (F:RawMarkedOutcome V U Γ Color→Type) [∀ a,Fintype (F a)] (ν:∀ a,FiniteLaw (F a)),
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS)
    let f:=fun (ω:∀ e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e) e=>rawExpandedMarkedCollapse e (ω e)
    1-ζ≤(μ.sigma (fun ω=>ν (f ω))).probability (fun z=>∀ i root,
      |resourcePatternLoad orderedOrdinaryResources (w i) (fun _ _=>true) root
        (orderedOrdinaryResourceState P π d (g i) (j i) (fun e=>rawExpandedApproximateCollapse e (z.1 e)))-
        ∑ W,(if root∈orderedOrdinaryResources W then w i W else 0)*
          ∏ a∈orderedOrdinaryResources W\{root},rawMarkedWheelMarginal P π d p₂ k₂ q s (g i) (j i) (orderedOrdinaryResourceEmbedding a)|<t i):=by
  let ε:ℝ:=ζ/((Fintype.card I:ℝ)+1)
  have hε:0<ε:=by dsimp [ε];positivity
  have hex:∀ i,∃ N,∀ (V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [LinearOrder V] [DecidableEq U],
      N≤Fintype.card V→Fintype.card U≤Fintype.card V→
      ∀ (P:SimpleGraph V) (π:Equiv.Perm V)
      (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
      (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
      (q:U→Γ→ℝ) (hq:∀ u g,0≤q u g) (hQ:∀ u,∑ g,q u g≤1/8)
      (s:U→Color→ℝ) (hs:∀ u j,0≤s u j) (hS:∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
      (hnoshort:∀ x l,0<l→l<2*d+1→(π^l) x≠x)
      (w:OrderedOrdinaryWheel (U:=U) π (3*d) (m i+1)→ℝ)
      (hw:∀ W,0≤w W ∧ w W≤B i/(Fintype.card V:ℝ)^(m i))
      (g:Γ) (j:Color)
      (F:RawMarkedOutcome V U Γ Color→Type) [∀ a,Fintype (F a)] (ν:∀ a,FiniteLaw (F a)),
      let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS)
      let f:=fun (ω:∀ e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e) e=>rawExpandedMarkedCollapse e (ω e)
      1-ε≤(μ.sigma (fun ω=>ν (f ω))).probability (fun z=>∀ root,
        |resourcePatternLoad orderedOrdinaryResources w (fun _ _=>true) root
          (orderedOrdinaryResourceState P π d g j (fun e=>rawExpandedApproximateCollapse e (z.1 e)))-
          ∑ W,(if root∈orderedOrdinaryResources W then w W else 0)*
            ∏ a∈orderedOrdinaryResources W\{root},rawMarkedWheelMarginal P π d p₂ k₂ q s g j (orderedOrdinaryResourceEmbedding a)|<t i):=by
    intro i
    exact raw_expanded_approximate_ordered_potentials_highProbability d (m i) hd (hm i) (B i) (t i) ε (hB i) (ht i) hε
  choose Ni hNi using hex
  refine ⟨Finset.univ.sup Ni,?_⟩
  intro V U Γ Color _ _ _ _ _ _ hn huV P π p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum q hq hQ s hs hS hnoshort w hw g j F _ ν μ f
  let law:=μ.sigma (fun ω=>ν (f ω))
  let E:=fun (i:I) (z:(Σ ω:(∀ e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e),F (f ω)))=>∀ root,
      |resourcePatternLoad orderedOrdinaryResources (w i) (fun _ _=>true) root
        (orderedOrdinaryResourceState P π d (g i) (j i) (fun e=>rawExpandedApproximateCollapse e (z.1 e)))-
        ∑ W,(if root∈orderedOrdinaryResources W then w i W else 0)*
          ∏ a∈orderedOrdinaryResources W\{root},rawMarkedWheelMarginal P π d p₂ k₂ q s (g i) (j i) (orderedOrdinaryResourceEmbedding a)|<t i
  have hi:∀ i∈(Finset.univ:Finset I),1-ε≤law.probability (E i):=by
    intro i _
    exact hNi i V U Γ Color ((Finset.le_sup (Finset.mem_univ i)).trans hn) huV P π p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum q hq hQ s hs hS hnoshort (w i) (hw i) (g i) (j i) F ν
  have hh:=finiteLaw_high_events_common law (Finset.univ:Finset I) E (fun _=>ε) hi
  have hbudget:(∑ _i:I,ε)≤ζ:=by
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    dsimp [ε]
    have hcard:(0:ℝ)≤Fintype.card I:=by positivity
    have hden:0<((Fintype.card I:ℝ)+1):=by positivity
    rw [←mul_div_assoc]
    apply (div_le_iff₀ hden).mpr
    nlinarith
  have hnum:1-ζ≤1-∑ _i:I,ε:=by linarith
  change 1-ζ≤law.probability (fun z=>∀ i,E i z)
  have hh':1-∑ _i:I,ε≤law.probability (fun z=>∀ i,E i z):=by
    simpa only [Finset.mem_univ,true_implies] using hh
  exact hnum.trans hh' 
end Oberwolfach

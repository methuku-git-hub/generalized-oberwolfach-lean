module

public import Oberwolfach.MarkedExpandedApproximatePotentialHighAny
public import Oberwolfach.FiniteHighEventsCommon

@[expose] public section
/-! One event for every fixed marked type, with an arbitrary total failure
budget. All tests share the same enriched experiment. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem raw_expanded_marked_finite_family_highProbability
    (I:Type) [Fintype I] (d m:ℕ) (hd:2≤d) (hm:3≤m) (B t ζ:ℝ) (hB:0<B) (ht:0<t) (hζ:0<ζ):
    ∃ N:ℕ,∀ (V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [LinearOrder V] [DecidableEq U],
    N≤Fintype.card V→Fintype.card U≤Fintype.card V→
    ∀ (P:SimpleGraph V) (π:Equiv.Perm V)
    (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
    (q:U→Γ→ℝ) (hq:∀ u g,0≤q u g) (hQ:∀ u,∑ g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀ u j,0≤s u j) (hS:∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
    (hnoshort:∀ x l,0<l→l<2*d+1→(π^l) x≠x)
    (H₀ Hₖ:V→U→Prop)
    (w:∀ i:I,MarkedWheel (Prod.fst:V×V→V) Prod.snd Prod.fst Prod.snd m π (3*d) H₀ Hₖ→ℝ)
    (hw:∀ i W,0≤w i W ∧ w i W≤B/(Fintype.card V:ℝ)^m)
    (g:I→Γ) (j:I→Color)
    (F:RawMarkedOutcome V U Γ Color→Type) [∀ a,Fintype (F a)] (ν:∀ a,FiniteLaw (F a)),
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS)
    let f:=fun (ω:∀ e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e) e=>rawExpandedMarkedCollapse e (ω e)
    1-ζ≤(μ.sigma (fun ω=>ν (f ω))).probability (fun z=>∀ i root,
      |typedMarkedPotentialLoad (w i) (rawMarkedPairRims P π d (fun e=>rawExpandedApproximateCollapse e (z.1 e)))
        (rawMarkedPairSpokes π d (fun e=>rawExpandedApproximateCollapse e (z.1 e)) (g i) (j i)) root-
        ∑ W,(if root∈typedMarkedOccurrenceResources W then w i W else 0)*
          ∏ a∈typedMarkedOccurrenceResources W\{root},rawMarkedWheelMarginal P π d p₂ k₂ q s (g i) (j i) a|<t):=by
  let ε:ℝ:=ζ/((Fintype.card I:ℝ)+1)
  have hε:0<ε:=by dsimp [ε];positivity
  obtain ⟨N,hN⟩:=raw_expanded_approximate_marked_potentials_highProbability_any d m hd hm B t ε hB ht hε
  refine ⟨N,?_⟩
  intro V U Γ Color _ _ _ _ _ _ hn huV P π p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum q hq hQ s hs hS hnoshort H₀ Hₖ w hw g j F _ ν μ f
  let law:=μ.sigma (fun ω=>ν (f ω))
  let E:=fun (i:I) (z:(Σ ω:(∀ e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e),F (f ω)))=>∀ root,
      |typedMarkedPotentialLoad (w i) (rawMarkedPairRims P π d (fun e=>rawExpandedApproximateCollapse e (z.1 e)))
        (rawMarkedPairSpokes π d (fun e=>rawExpandedApproximateCollapse e (z.1 e)) (g i) (j i)) root-
        ∑ W,(if root∈typedMarkedOccurrenceResources W then w i W else 0)*
          ∏ a∈typedMarkedOccurrenceResources W\{root},rawMarkedWheelMarginal P π d p₂ k₂ q s (g i) (j i) a|<t
  have hi:∀ i∈(Finset.univ:Finset I),1-ε≤law.probability (E i):=by
    intro i _
    exact hN V U Γ Color hn huV P π p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum q hq hQ s hs hS hnoshort H₀ Hₖ (w i) (hw i) (g i) (j i) F ν
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

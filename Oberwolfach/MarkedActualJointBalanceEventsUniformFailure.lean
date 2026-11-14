module

public import Oberwolfach.MarkedActualVortexBalanceProperty
public import Oberwolfach.MarkedActualInnerBalanceEventUniformFailure
public import Oberwolfach.MarkedActualDeeperBalanceEventUniformFailure

@[expose] public section
/-! Inner and deeper balance on one retained law and the same fixed outcome. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 50000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
theorem marked_actual_joint_balance_events_uniform_failure
    (c:ℕ) (hc:3≤c) (α ρ₀ sstar tstar epsBal Qexp ζ:ℝ)
    (hα:0<α) (hρ₀:0<ρ₀) (hsstar:0<sstar) (htstar:0<tstar)
    (hepsBal:0<epsBal) (hζ:0<ζ):
    ∃ βmax:ℝ,0<βmax ∧ ∀ χ:ℝ,0<χ→∀ ε:ℝ,0<ε→ε≤1/4→∀ (d:ℕ) (hd:2≤d),∃ N₀:ℕ,1≤N₀ ∧
    ∃ m₀:ℕ,1≤m₀ ∧ ∀ (V U:Type) [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
      (G:SimpleGraph V) (D m:ℕ) (β:ℝ) (Q:Vortex U G D β ε m),
    G.IsRegularOfDegree D→∀ (hn:0<Fintype.card V),N₀≤Fintype.card V→
    (1/2+α)*Fintype.card V≤(D:ℝ)→∀ (hρlo:ρ₀≤ initialIndexDensity U D) (hρhi:initialIndexDensity U D≤1),
    0≤β→β≤βmax→m₀≤m→∀ (π:Equiv.Perm V)
      (hπ:∀ i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i),
    (∀ x l,0<l→l<2*d+1→(π^l) x≠x)→∀ L:ℕ,L+1<Q.length→
    letI : Nonempty V:=Fintype.card_pos_iff.mp hn
    let W:=markedVortexVertexType Q
    letI : ∀ i,DecidableEq (W i):=fun _ a b=>Classical.propDecidable (a=b)
    let Z:=markedVortexHubType Q
    let f:=markedVortexVertexEmbedding Q
    let g:=markedVortexHubEmbedding Q
    let ρ:=markedVortexPermutation Q π hπ
    let A:=markedVortexInnerVertices Q
    let B:=markedVortexInnerHubs Q
    let M:=fun i=>(A i).card
    let Dbal:=fun i=>2*((B i).card:ℝ)/initialIndexDensity U D;
    ∀ (Γ Color:Type) [Fintype Γ] [Fintype Color] (s₀:ℝ) (hslo:sstar≤s₀) (hshi:s₀≤1/100),
    let dens:=initialIndexDensity U D
    let densities:=marked_seed_density_bounds c (by omega) dens s₀ ρ₀ sstar hρ₀ hsstar hρlo hρhi hslo hshi
    let p:=dens*s₀/2
    let kval:=p/(c:ℝ);
    ∀ (q:U→Γ→ℝ) (hq:∀ u a,0≤q u a) (hQ:∀ u,∑ a,q u a≤1/8)
      (s:U→Color→ℝ) (hs:∀ u j,0≤s u j)
      (hS:∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ a,q u a)) (a:Γ) (j:Color),
      (∀ u,q u a=s₀/c)→(∀ u,s u j=s₀)→tstar≤s₀/c→
    ∀ (Extra:RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d a→Prop) (extraErr:ℝ),
    1-extraErr≤(rawMarkedRetentionLaw π d hd a p kval (densities.1.trans_le densities.2.1).le
      (densities.1.trans_le densities.2.2.1).le densities.2.2.2.2.2.2.2.2 q hq hQ s hs hS).probability Extra→
    1-2*χ-2*(Fintype.card V:ℝ)^(-Qexp)-extraErr≤
      (rawMarkedRetentionLaw π d hd a p kval (densities.1.trans_le densities.2.1).le
        (densities.1.trans_le densities.2.2.1).le densities.2.2.2.2.2.2.2.2 q hq hQ s hs hS).probability
      (fun z=>MarkedActualVortexBalanceProperty Q π hπ d c (L+1) a j epsBal ζ A B z ∧
        MarkedActualVortexBalanceProperty Q π hπ d c L a j epsBal ζ
          (markedVortexDeeperVertices Q) (markedVortexDeeperHubs Q) z ∧ Extra z)  :=by
  obtain ⟨βI,hβI,hinner⟩:=marked_actual_inner_balance_event_uniform_failure c hc α ρ₀ sstar tstar epsBal Qexp ζ hα hρ₀ hsstar htstar hepsBal hζ
  obtain ⟨βT,hβT,hdeep⟩:=marked_actual_deeper_balance_event_uniform_failure c hc α ρ₀ sstar tstar epsBal Qexp ζ hα hρ₀ hsstar htstar hepsBal hζ
  let βmax:=min βI βT
  refine ⟨βmax,by dsimp [βmax];positivity,?_⟩
  intro χ hχ ε he he1 d hd
  have hinner:=hinner χ hχ
  have hdeep:=hdeep χ hχ
  obtain ⟨NI,hNI,mI,hmI,hinner⟩:=hinner ε he he1 d hd
  obtain ⟨NT,hNT,mT,hmT,hdeep⟩:=hdeep ε he he1 d hd
  refine ⟨max NI NT, hNI.trans (le_max_left _ _), max mI mT, hmI.trans (le_max_left _ _), ?_⟩
  intro V U _ _ _ _ G D m β Q hreg hn hn0 hD hρlo hρhi hb hbmax hm π hπ hshort L hL W Z f g ρ A B M Dbal
  letI : Nonempty V:=Fintype.card_pos_iff.mp hn
  have hnI:NI≤Fintype.card V:=(le_max_left _ _).trans hn0
  have hnT:NT≤Fintype.card V:=(le_max_right _ _).trans hn0
  have hmI':mI≤m:=(le_max_left _ _).trans hm
  have hmT':mT≤m:=(le_max_right _ _).trans hm
  have hbI:β≤βI:=hbmax.trans (min_le_left _ _)
  have hbT:β≤βT:=hbmax.trans (min_le_right _ _)
  intro Γ Color _ _ s₀ hslo hshi dens densities p kval q hq hQ s hs hS a j hq0 hs0 htlo Extra extraErr hExtra
  let E:=fun z:RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d a=>
    MarkedActualVortexBalanceProperty Q π hπ d c (L+1) a j epsBal ζ A B z ∧ Extra z
  let err:=χ+(Fintype.card V:ℝ)^(-Qexp)+extraErr
  have hi:=hinner V U G D m β Q hreg hn hnI hD hρlo hρhi hb hbI hmI' π hπ hshort (L+1) hL
    Γ Color s₀ hslo hshi q hq hQ s hs hS a j hq0 hs0 htlo Extra extraErr hExtra
  let μ:=rawMarkedRetentionLaw π d hd a p kval (densities.1.trans_le densities.2.1).le
    (densities.1.trans_le densities.2.2.1).le densities.2.2.2.2.2.2.2.2 q hq hQ s hs hS
  have hip:1-χ-(Fintype.card V:ℝ)^(-Qexp)-extraErr≤μ.probability E:=by
    exact hi
  have hi':1-err≤μ.probability E:=by
    dsimp [err]
    linarith only [hip]
  have ht:=hdeep V U G D m β Q hreg hn hnT hD hρlo hρhi hb hbT hmT' π hπ hshort L hL
    Γ Color s₀ hslo hshi q hq hQ s hs hS a j hq0 hs0 htlo E err hi'
  let ET:=fun z:RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d a=>
    MarkedActualVortexBalanceProperty Q π hπ d c L a j epsBal ζ (markedVortexDeeperVertices Q) (markedVortexDeeperHubs Q) z
  have htp:1-χ-(Fintype.card V:ℝ)^(-Qexp)-err≤μ.probability (fun z=>ET z ∧ E z):=by
    exact ht
  have heq:(fun z=>ET z ∧ E z)=(fun z=>MarkedActualVortexBalanceProperty Q π hπ d c (L+1) a j epsBal ζ A B z ∧ ET z ∧ Extra z):=by
    funext z
    apply propext
    dsimp [E]
    tauto
  rw [heq] at htp
  dsimp [err] at htp
  change 1-2*χ-2*(Fintype.card V:ℝ)^(-Qexp)-extraErr≤μ.probability (fun z=>MarkedActualVortexBalanceProperty Q π hπ d c (L+1) a j epsBal ζ A B z ∧ ET z ∧ Extra z)
  linarith only [htp]
end Oberwolfach

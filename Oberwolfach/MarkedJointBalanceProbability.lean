module

public import Oberwolfach.MarkedActualJointBalanceEventsUniformFailure
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
theorem marked_actual_joint_balance_probability_uniform_failure
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
    1-2*χ-2*(Fintype.card V:ℝ)^(-Qexp)≤
      (rawMarkedRetentionLaw π d hd a p kval (densities.1.trans_le densities.2.1).le
      (densities.1.trans_le densities.2.2.1).le densities.2.2.2.2.2.2.2.2 q hq hQ s hs hS).probability
      (fun z=>MarkedActualVortexBalanceProperty Q π hπ d c (L+1) a j epsBal ζ A B z ∧
        MarkedActualVortexBalanceProperty Q π hπ d c L a j epsBal ζ
          (markedVortexDeeperVertices Q) (markedVortexDeeperHubs Q) z) := by
  obtain ⟨βmax,hβmax,hbound⟩:=marked_actual_joint_balance_events_uniform_failure c hc α ρ₀ sstar tstar epsBal Qexp ζ
    hα hρ₀ hsstar htstar hepsBal hζ
  refine ⟨βmax,hβmax,?_⟩
  intro χ hχ ε he he1 d hd
  obtain ⟨N,hN,m₀,hm₀,hNbound⟩:=hbound χ hχ ε he he1 d hd
  refine ⟨N,hN,m₀,hm₀,?_⟩
  intro V U _ _ _ _ G D m β Q hreg hn hnN hD hρlo hρhi hb hbmax hm π hπ hshort L hL W Z f g ρ A B M Dbal
  letI : Nonempty V:=Fintype.card_pos_iff.mp hn
  intro Γ Color _ _ s₀ hslo hshi dens densities p kval q hq hQ s hs hS a j hq0 hs0 htlo
  have hh:=hNbound V U G D m β Q hreg hn hnN hD hρlo hρhi hb hbmax hm π hπ hshort L hL
    Γ Color s₀ hslo hshi q hq hQ s hs hS a j hq0 hs0 htlo (fun _=>True) 0 (by simp [finiteLaw_probability_true])
  simpa only [and_true,sub_zero] using hh
end Oberwolfach

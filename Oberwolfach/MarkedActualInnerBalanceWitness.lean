module

public import Oberwolfach.MarkedActualVortexBalanceProperty

@[expose] public section
/-! A positive-mass common balance outcome with fixed numerical failure budgets. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 50000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
theorem marked_actual_inner_balance_witness
    (c:ℕ) (hc:3≤c) (α ρ₀ sstar tstar epsBal ζ:ℝ)
    (hα:0<α) (hρ₀:0<ρ₀) (hsstar:0<sstar) (htstar:0<tstar)
    (hepsBal:0<epsBal) (hζ:0<ζ):
    ∃ βmax:ℝ,0<βmax ∧ ∀ ε:ℝ,0<ε→ε≤1/4→∀ (d:ℕ) (hd:2≤d),∃ N₀:ℕ,1≤N₀ ∧
    ∃ m₀:ℕ,1≤m₀ ∧ ∀ (V U:Type) [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
      (G:SimpleGraph V) (D m:ℕ) (β:ℝ) (Q:Vortex U G D β ε m),
    G.IsRegularOfDegree D→∀ (hn:0<Fintype.card V),N₀≤Fintype.card V→
    (1/2+α)*Fintype.card V≤(D:ℝ)→∀ (hρlo:ρ₀≤ initialIndexDensity U D) (hρhi:initialIndexDensity U D≤1),
    0≤β→β≤βmax→m₀≤m→∀ (π:Equiv.Perm V)
      (hπ:∀ i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i),
    (∀ x l,0<l→l<2*d+1→(π^l) x≠x)→∀ L:ℕ,L<Q.length→
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
    ∀ (Extra:RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d a→Prop),
    (3/4:ℝ)≤(rawMarkedRetentionLaw π d hd a p kval (densities.1.trans_le densities.2.1).le
      (densities.1.trans_le densities.2.2.1).le densities.2.2.2.2.2.2.2.2 q hq hQ s hs hS).probability Extra→
    ∃ z:RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d a,
      0<(rawMarkedRetentionLaw π d hd a p kval (densities.1.trans_le densities.2.1).le
        (densities.1.trans_le densities.2.2.1).le densities.2.2.2.2.2.2.2.2 q hq hQ s hs hS).mass z ∧
      MarkedActualVortexBalanceProperty Q π hπ d c L a j epsBal ζ A B z ∧
      Extra z  :=by
  obtain ⟨βmax,hβ,hbase⟩:=marked_actual_inner_balance_event c hc α ρ₀ sstar tstar epsBal (1/100) 1 ζ
    hα hρ₀ hsstar htstar hepsBal (by norm_num) hζ
  refine ⟨βmax,hβ,?_⟩
  intro ε he he1 d hd
  obtain ⟨N,hN,m₀,hm₀,hbase⟩:=hbase ε he he1 d hd
  refine ⟨max N 16,hN.trans (le_max_left _ _),m₀,hm₀,?_⟩
  intro V U _ _ _ _ G D m β Q hreg hn hn0 hD hρlo hρhi hb hbmax hm π hπ hshort L hL W Z f g ρ A B M Dbal
  letI : Nonempty V:=Fintype.card_pos_iff.mp hn
  have hnN:N≤Fintype.card V:=(le_max_left _ _).trans hn0
  have hn16:16≤Fintype.card V:=(le_max_right _ _).trans hn0
  intro Γ Color _ _ s₀ hslo hshi dens densities p kval q hq hQ s hs hS a j hq0 hs0 htlo Extra hExtra
  let μ:=rawMarkedRetentionLaw π d hd a p kval (densities.1.trans_le densities.2.1).le
    (densities.1.trans_le densities.2.2.1).le densities.2.2.2.2.2.2.2.2 q hq hQ s hs hS
  let E:=fun z:RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d a=>
    MarkedActualVortexBalanceProperty Q π hπ d c L a j epsBal ζ A B z ∧
      Extra z
  have hExtra':1-(1/4:ℝ)≤μ.probability Extra:=by linarith only [hExtra]
  have hbnd:=hbase V U G D m β Q hreg hn hnN hD hρlo hρhi hb hbmax hm π hπ hshort L hL
    Γ Color s₀ hslo hshi q hq hQ s hs hS a j hq0 hs0 htlo Extra (1/4) hExtra'
  have hbnd':1-(1/100:ℝ)-(Fintype.card V:ℝ)^(-(1:ℝ))-(1/4:ℝ)≤μ.probability E:=by exact hbnd
  have hnpos:(0:ℝ)<Fintype.card V:=by exact_mod_cast hn
  have hn16r:(16:ℝ)≤Fintype.card V:=by exact_mod_cast hn16
  have hpow:(Fintype.card V:ℝ)^(-(1:ℝ))=1/(Fintype.card V:ℝ):=by
    rw [Real.rpow_neg hnpos.le,Real.rpow_one,one_div]
  have hinv:(1:ℝ)/(Fintype.card V:ℝ)≤1/16:=by apply (div_le_iff₀ hnpos).2;linarith
  have hp:0<μ.probability E:=by
    rw [hpow] at hbnd'
    linarith only [hbnd',hinv]
  letI : DecidablePred E := fun z => Classical.propDecidable (E z)
  unfold FiniteLaw.probability at hp
  have hnonneg:∀ z∈(Finset.univ:_),0≤(if E z then μ.mass z else 0):=by
    intro z _
    split_ifs
    · exact μ.nonneg z
    · norm_num
  obtain ⟨z,_,hz⟩:=(Finset.sum_pos_iff_of_nonneg hnonneg).mp hp
  have hEz:E z:=by
    by_contra h
    simp [h] at hz
  have hzpos:0<μ.mass z:=by simpa [hEz] using hz
  exact ⟨z,hzpos,hEz.1,hEz.2⟩
end Oberwolfach

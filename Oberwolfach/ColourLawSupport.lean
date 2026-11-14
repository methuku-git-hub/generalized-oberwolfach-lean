module

public import Oberwolfach.HypergraphColourAvoidance
public import Oberwolfach.FiniteLawSupport

@[expose] public section

/-! Every positive-mass configuration chooses its raw colours from the
specified lists. Probability identities may therefore restrict a resource
clique to edges whose lists contain the tested colour. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem finiteLaw_probability_congr_support {Ω : Type*} [Fintype Ω]
    (μ : FiniteLaw Ω) (A B : Ω → Prop)
    (h : ∀ x,0<μ.mass x → (A x ↔ B x)) : μ.probability A=μ.probability B := by
  unfold FiniteLaw.probability
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : 0<μ.mass x
  · simp only [h x hx]
  · have hz : μ.mass x=0 := le_antisymm (le_of_not_gt hx) (μ.nonneg x)
    simp [hz]

theorem finiteLaw_pi_positive_coordinate
    {I : Type*} [Fintype I] {X : I → Type*} [∀ i,Fintype (X i)]
    (μ : ∀ i,FiniteLaw (X i)) (σ : ∀ i,X i)
    (hσ : 0<(FiniteLaw.pi μ).mass σ) (i : I) : 0<(μ i).mass (σ i) := by
  classical
  have hn : (μ i).mass (σ i)≠0 := by
    intro hz
    have he : (FiniteLaw.pi μ).mass σ=0 := by
      exact Finset.prod_eq_zero (Finset.mem_univ i) hz
    rw [he] at hσ
    exact (lt_irrefl 0) hσ
  exact lt_of_le_of_ne ((μ i).nonneg _) (Ne.symm hn)

theorem uniformList_withCoin_support
    {E C : Type*} [Fintype E] [Fintype C]
    (L : E → Finset C) (hL : ∀ e,(L e).Nonempty)
    (a : E → C → ℝ) (ha : ∀ e c,0≤a e c ∧ a e c≤1)
    (σ : E → C×Bool)
    (hσ : 0<(FiniteLaw.pi (fun e=>(FiniteLaw.uniformOn (L e) (hL e)).withCoin
      (a e) (ha e))).mass σ) (e : E) : (σ e).1∈L e := by
  have hp := finiteLaw_pi_positive_coordinate _ σ hσ e
  by_contra hn
  simp only [FiniteLaw.withCoin,FiniteLaw.uniformOn,hn,ite_false,zero_mul] at hp
  exact (lt_irrefl 0) hp

theorem retainedColour_mem_list_on_support
    {E C : Type*} [Fintype E] [Fintype C]
    (G : SimpleGraph E) (L : E → Finset C) (hL : ∀ e,(L e).Nonempty)
    (a : E → C → ℝ) (ha : ∀ e c,0≤a e c ∧ a e c≤1)
    (σ : E → C×Bool)
    (hσ : 0<(FiniteLaw.pi (fun e=>(FiniteLaw.uniformOn (L e) (hL e)).withCoin
      (a e) (ha e))).mass σ) (e : E) (c : C)
    (hc : coinRetainedColour G σ e=some c) : c∈L e := by
  have h := uniformList_withCoin_support L hL a ha σ hσ e
  rw [(coinRetainedColour_eq_some G σ e c).mp hc |>.1] at h
  exact h

theorem resourceColour_avoidance_probability
    {V E C : Type*} [Fintype E] [Fintype C]
    (R : E → Finset V) (L : E → Finset C) (hL : ∀ e,(L e).Nonempty)
    (a : E → C → ℝ) (ha : ∀ e c,0≤a e c ∧ a e c≤1)
    (S : Finset V) (c : C) :
    let G := hypergraphLineGraph R
    let μ := FiniteLaw.pi (fun e=>(FiniteLaw.uniformOn (L e) (hL e)).withCoin (a e) (ha e))
    μ.probability (fun σ=>∀ v∈S,∀ e∈hypergraphVertexClique R v,
      coinRetainedColour G σ e≠some c)=
    μ.probability (fun σ=>∀ v∈S,∀ e∈hypergraphColourClique R L v c,
      coinRetainedColour G σ e≠some c) := by
  dsimp only
  apply finiteLaw_probability_congr_support
  intro σ hσ
  constructor
  · intro h v hv e he
    apply h v hv e
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp he).2.1⟩
  · intro h v hv e he hc
    have hlist := retainedColour_mem_list_on_support (hypergraphLineGraph R) L hL a ha σ hσ e c hc
    exact h v hv e (Finset.mem_filter.mpr
      ⟨Finset.mem_univ _,(Finset.mem_filter.mp he).2,hlist⟩) hc

theorem hypergraph_resource_colour_avoidance
    {V E C : Type*} [Fintype E] [Fintype C]
    (R : E → Finset V) (L : E → Finset C) (hL : ∀ e,(L e).Nonempty)
    {l k B s : ℕ} (hl : 1<l) (hcard : ∀ e,(L e).card=l)
    (hsize : ∀ e,(R e).card≤k)
    (hcodeg : ∀ v w,v≠w → (Finset.univ.filter (fun e=>v∈R e ∧ w∈R e)).card≤B)
    (c : C) (hdegree : ∀ v,(hypergraphColourClique R L v c).card≤s) (hsl : s≤l)
    (S : Finset V) (hsmall : 2*(S.card^2*(k^2*B))≤l) :
    let G := hypergraphLineGraph R
    let μ := FiniteLaw.pi (fun e=>(FiniteLaw.uniformOn (L e) (hL e)).withCoin
      (equalizationCoin G L l (k*s) e)
      (equalizationCoin_bounds G L (by omega) (k*s) e))
    let r := ((1-1/(l : ℝ))^(k*s))/(l : ℝ)
    |μ.probability (fun σ=>∀ v∈S,∀ e∈hypergraphVertexClique R v,
        coinRetainedColour G σ e≠some c)-
      (∏ v∈S,(1-((hypergraphColourClique R L v c).card : ℝ)*r))|≤
      (2 : ℝ)^S.card*((S.card^2*(2*k^2+k+2)*B : ℕ) : ℝ)/(l : ℝ) := by
  dsimp only
  rw [resourceColour_avoidance_probability]
  exact hypergraph_colour_avoidance R L hL hl hcard hsize hcodeg c hdegree hsl S hsmall

end Oberwolfach

module

public import Oberwolfach.ColourLawSupport
public import Oberwolfach.RemainingColourDegrees

@[expose] public section

/-! The expectation of the available list is a sum of the actual colour
avoidance probabilities. Fixed equal resource colour degrees give a single
comparison term, without assuming independence of the clique events. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem nibbleAvailableColours_expectation
    {V C J Ω : Type*} [Fintype Ω]
    (G : SimpleGraph V) (Q : Finset J) (T : J → Finset V)
    (hT : ∀ j∈Q,∀ u∈T j,∀ v∈T j,u≠v → G.Adj u v)
    (L : Finset C) (μ : FiniteLaw Ω) (σ : Ω → V → C×Bool) :
    μ.expectation (fun x=>((nibbleAvailableColours G Q T L (σ x)).card : ℝ))=
      ∑ c∈L,μ.probability (fun x=>∀ j∈Q,∀ v∈T j,coinRetainedColour G (σ x) v≠some c) := by
  classical
  have hh := finiteLaw_expectation_count μ L
    (fun c x=>∀ j∈Q,∀ v∈T j,coinRetainedColour G (σ x) v≠some c)
  convert hh using 1
  apply congrArg μ.expectation
  funext x
  apply congrArg (fun S : Finset C=>(S.card : ℝ))
  ext c
  rw [nibbleAvailableColours_mem_iff G Q T hT]
  simp only [Finset.mem_filter]
  exact and_congr_right (fun _=>(clique_no_retained_iff_card G Q T hT (σ x) c).symm)

theorem hypergraph_available_colour_expectation
    {V E C : Type*} [Fintype E] [Fintype C]
    (R : E → Finset V) (L : E → Finset C) (hL : ∀ e,(L e).Nonempty)
    {l k B s : ℕ} (hl : 1<l) (hcard : ∀ e,(L e).card=l)
    (hsize : ∀ e,(R e).card≤k)
    (hcodeg : ∀ v w,v≠w → (Finset.univ.filter (fun e=>v∈R e ∧ w∈R e)).card≤B)
    (hdegree : ∀ v c,(hypergraphColourClique R L v c).card≤s) (hsl : s≤l)
    (S : Finset V) (A : Finset C) (hsmall : 2*(S.card^2*(k^2*B))≤l) :
    let G := hypergraphLineGraph R
    let μ := FiniteLaw.pi (fun e=>(FiniteLaw.uniformOn (L e) (hL e)).withCoin
      (equalizationCoin G L l (k*s) e)
      (equalizationCoin_bounds G L (by omega) (k*s) e))
    let r := ((1-1/(l : ℝ))^(k*s))/(l : ℝ)
    |μ.expectation (fun σ=>((nibbleAvailableColours G S (hypergraphVertexClique R) A σ).card : ℝ))-
      ∑ c∈A,(∏ v∈S,(1-((hypergraphColourClique R L v c).card : ℝ)*r))|≤
      (A.card : ℝ)*((2 : ℝ)^S.card*((S.card^2*(2*k^2+k+2)*B : ℕ) : ℝ)/(l : ℝ)) := by
  classical
  dsimp only
  rw [nibbleAvailableColours_expectation _ _ _
    (fun v _=>hypergraphVertexClique_isClique R v)]
  rw [← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _c∈A,(2 : ℝ)^S.card*((S.card^2*(2*k^2+k+2)*B : ℕ) : ℝ)/(l : ℝ) := by
      apply Finset.sum_le_sum
      intro c _
      exact hypergraph_resource_colour_avoidance R L hL hl hcard hsize hcodeg c
        (fun v=>hdegree v c) hsl S hsmall
    _ = _ := by simp

theorem hypergraph_available_colour_expectation_equal_degrees
    {V E C : Type*} [Fintype E] [Fintype C]
    (R : E → Finset V) (L : E → Finset C) (hL : ∀ e,(L e).Nonempty)
    {l k B s : ℕ} (hl : 1<l) (hcard : ∀ e,(L e).card=l)
    (hsize : ∀ e,(R e).card≤k)
    (hcodeg : ∀ v w,v≠w → (Finset.univ.filter (fun e=>v∈R e ∧ w∈R e)).card≤B)
    (hdegree : ∀ v c,(hypergraphColourClique R L v c).card≤s) (hsl : s≤l)
    (S : Finset V) (A : Finset C) (hsmall : 2*(S.card^2*(k^2*B))≤l)
    (heq : ∀ v∈S,∀ c∈A,(hypergraphColourClique R L v c).card=s) :
    let G := hypergraphLineGraph R
    let μ := FiniteLaw.pi (fun e=>(FiniteLaw.uniformOn (L e) (hL e)).withCoin
      (equalizationCoin G L l (k*s) e)
      (equalizationCoin_bounds G L (by omega) (k*s) e))
    let r := ((1-1/(l : ℝ))^(k*s))/(l : ℝ)
    |μ.expectation (fun σ=>((nibbleAvailableColours G S (hypergraphVertexClique R) A σ).card : ℝ))-
      (A.card : ℝ)*(1-(s : ℝ)*r)^S.card|≤
      (A.card : ℝ)*((2 : ℝ)^S.card*((S.card^2*(2*k^2+k+2)*B : ℕ) : ℝ)/(l : ℝ)) := by
  have hh := hypergraph_available_colour_expectation R L hL hl hcard hsize hcodeg hdegree hsl S A hsmall
  dsimp only at hh ⊢
  have he : (∑ c∈A,(∏ v∈S,(1-((hypergraphColourClique R L v c).card : ℝ)*
      ((1-1/(l : ℝ))^(k*s)/(l : ℝ)))))=
      (A.card : ℝ)*(1-(s : ℝ)*((1-1/(l : ℝ))^(k*s)/(l : ℝ)))^S.card := by
    calc
      _ = ∑ _c∈A,(1-(s : ℝ)*((1-1/(l : ℝ))^(k*s)/(l : ℝ)))^S.card := by
        apply Finset.sum_congr rfl
        intro c hc
        rw [← Finset.prod_const]
        apply Finset.prod_congr rfl
        intro v hv
        rw [heq v hv c hc]
      _ = _ := by simp
  rw [he] at hh
  exact hh

end Oberwolfach

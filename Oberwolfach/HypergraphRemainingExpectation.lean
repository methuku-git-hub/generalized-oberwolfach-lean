module

public import Oberwolfach.ColourLawSupport
public import Oberwolfach.RemainingColourExpectation

@[expose] public section

/-! Remaining colour degrees in the actual hypergraph colouring law.
The deterministic comparison retains the original resource colour degrees. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem hypergraph_remaining_colour_expectation
    {V E C : Type*} [Fintype E] [Fintype C]
    (R : E → Finset V) (L : E → Finset C) (hL : ∀ e,(L e).Nonempty)
    {l k B s : ℕ} (hl : 1<l) (hcard : ∀ e,(L e).card=l)
    (hsize : ∀ e,(R e).card≤k)
    (hcodeg : ∀ v w,v≠w → (Finset.univ.filter (fun e=>v∈R e ∧ w∈R e)).card≤B)
    (hdegree : ∀ v c,(hypergraphColourClique R L v c).card≤s) (hsl : s≤l)
    (U : Finset E) (Q : E → Finset V) (c : C)
    (hsmall : ∀ e∈U,2*((Q e).card^2*(k^2*B))≤l) :
    let G := hypergraphLineGraph R
    let μ := FiniteLaw.pi (fun e=>(FiniteLaw.uniformOn (L e) (hL e)).withCoin
      (equalizationCoin G L l (k*s) e)
      (equalizationCoin_bounds G L (by omega) (k*s) e))
    let ρ := (1-1/(l : ℝ))^(k*s)
    let r := ρ/(l : ℝ)
    |μ.expectation (fun σ=>((remainingColourVertices G U Q (hypergraphVertexClique R) c σ).card : ℝ))-
      ∑ e∈U,(1-ρ)*(∏ v∈Q e,(1-((hypergraphColourClique R L v c).card : ℝ)*r))|≤
      (U.card : ℝ)*(1/(l : ℝ)+ρ*(2/(l : ℝ)+2*((k*s : ℕ) : ℝ)/((l : ℝ)*((l : ℝ)-1))))+
      ∑ e∈U,(2 : ℝ)^(Q e).card*((((Q e).card^2*(2*k^2+k+2)*B : ℕ)) : ℝ)/(l : ℝ) := by
  classical
  dsimp only
  let G := hypergraphLineGraph R
  let μ := FiniteLaw.pi (fun e=>(FiniteLaw.uniformOn (L e) (hL e)).withCoin
    (equalizationCoin G L l (k*s) e)
    (equalizationCoin_bounds G L (by omega : 0<l) (k*s) e))
  let ρ := (1-1/(l : ℝ))^(k*s)
  let r := ρ/(l : ℝ)
  let A := fun e σ=>∀ v∈Q e,∀ f∈hypergraphVertexClique R v,coinRetainedColour G σ f≠some c
  let p := fun e=>∏ v∈Q e,(1-((hypergraphColourClique R L v c).card : ℝ)*r)
  let ε := fun e=>(2 : ℝ)^(Q e).card*((((Q e).card^2*(2*k^2+k+2)*B : ℕ)) : ℝ)/(l : ℝ)
  have hρ := equalized_retention_rate_bounds (by omega : 0<l) (k*s)
  have hbase := remainingColourVertices_expectation G L hL hl hcard
    (fun e b=>hypergraph_colour_neighbour_degree R L hsize b (fun v=>hdegree v b) e)
    U Q (hypergraphVertexClique R) c
  have hprob (e : E) (he : e∈U) : |μ.probability (A e)-p e|≤ε e :=
    hypergraph_resource_colour_avoidance R L hL hl hcard hsize hcodeg c
      (fun v=>hdegree v c) hsl (Q e) (hsmall e he)
  have hcomp : |(∑ e∈U,(1-ρ)*μ.probability (A e))-(∑ e∈U,(1-ρ)*p e)|≤∑ e∈U,ε e := by
    rw [← Finset.sum_sub_distrib]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro e he
    rw [← mul_sub,abs_mul,abs_of_nonneg (sub_nonneg.mpr hρ.2)]
    calc
      _ ≤ (1-ρ)*ε e := mul_le_mul_of_nonneg_left (hprob e he) (sub_nonneg.mpr hρ.2)
      _ ≤ ε e := mul_le_of_le_one_left (by dsimp [ε]; positivity) (by dsimp [ρ]; linarith [hρ.1])
  calc
    _ ≤ |μ.expectation (fun σ=>((remainingColourVertices G U Q (hypergraphVertexClique R) c σ).card : ℝ))-
        (∑ e∈U,(1-ρ)*μ.probability (A e))|+
        |(∑ e∈U,(1-ρ)*μ.probability (A e))-(∑ e∈U,(1-ρ)*p e)| := abs_sub_le _ _ _
    _ ≤ _ := add_le_add hbase hcomp

end Oberwolfach

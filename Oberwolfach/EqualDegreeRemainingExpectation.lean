module

public import Oberwolfach.HypergraphRemainingExpectation

@[expose] public section

/-! The remaining colour degree has a single comparison term when the
resource colour degrees have been equalized. Root omissions are retained. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem hypergraph_remaining_colour_expectation_equal_degrees
    {V E C : Type*} [Fintype E] [Fintype C]
    (R : E → Finset V) (L : E → Finset C) (hL : ∀ e,(L e).Nonempty)
    {l k B s q : ℕ} (hl : 1<l) (hcard : ∀ e,(L e).card=l)
    (hsize : ∀ e,(R e).card≤k)
    (hcodeg : ∀ v w,v≠w → (Finset.univ.filter (fun e=>v∈R e ∧ w∈R e)).card≤B)
    (hdegree : ∀ v c,(hypergraphColourClique R L v c).card≤s) (hsl : s≤l)
    (U : Finset E) (Q : E → Finset V) (c : C)
    (hQ : ∀ e∈U,(Q e).card=q) (hsmall : 2*(q^2*(k^2*B))≤l)
    (heq : ∀ e∈U,∀ v∈Q e,(hypergraphColourClique R L v c).card=s) :
    let G := hypergraphLineGraph R
    let μ := FiniteLaw.pi (fun e=>(FiniteLaw.uniformOn (L e) (hL e)).withCoin
      (equalizationCoin G L l (k*s) e)
      (equalizationCoin_bounds G L (by omega) (k*s) e))
    let ρ := (1-1/(l : ℝ))^(k*s)
    let κ := 1-(s : ℝ)*ρ/(l : ℝ)
    |μ.expectation (fun σ=>((remainingColourVertices G U Q (hypergraphVertexClique R) c σ).card : ℝ))-
      (U.card : ℝ)*(1-ρ)*κ^q|≤
      (U.card : ℝ)*(1/(l : ℝ)+ρ*(2/(l : ℝ)+2*((k*s : ℕ) : ℝ)/((l : ℝ)*((l : ℝ)-1)))+
        (2 : ℝ)^q*((q^2*(2*k^2+k+2)*B : ℕ) : ℝ)/(l : ℝ)) := by
  classical
  dsimp only
  have hh := hypergraph_remaining_colour_expectation R L hL hl hcard hsize hcodeg hdegree hsl U Q c
    (fun e he=>by rw [hQ e he];exact hsmall)
  dsimp only at hh
  have hprod (e : E) (he : e∈U) :
      (∏ v∈Q e,(1-((hypergraphColourClique R L v c).card : ℝ)*
        ((1-1/(l : ℝ))^(k*s)/(l : ℝ))))=
      (1-(s : ℝ)*(1-1/(l : ℝ))^(k*s)/(l : ℝ))^q := by
    calc
      _ = ∏ _v∈Q e,(1-(s : ℝ)*(1-1/(l : ℝ))^(k*s)/(l : ℝ)) := by
        apply Finset.prod_congr rfl
        intro v hv
        rw [heq e he v hv,mul_div_assoc]
      _ = _ := by rw [Finset.prod_const,hQ e he]
  have hmain : (∑ e∈U,(1-(1-1/(l : ℝ))^(k*s))*
      (∏ v∈Q e,(1-((hypergraphColourClique R L v c).card : ℝ)*
        ((1-1/(l : ℝ))^(k*s)/(l : ℝ)))))=
      (U.card : ℝ)*(1-(1-1/(l : ℝ))^(k*s))*
        (1-(s : ℝ)*(1-1/(l : ℝ))^(k*s)/(l : ℝ))^q := by
    calc
      _ = ∑ _e∈U,(1-(1-1/(l : ℝ))^(k*s))*
          (1-(s : ℝ)*(1-1/(l : ℝ))^(k*s)/(l : ℝ))^q := by
        apply Finset.sum_congr rfl
        intro e he
        rw [hprod e he]
      _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul];ring
  have herr : (∑ e∈U,(2 : ℝ)^(Q e).card*
      ((((Q e).card^2*(2*k^2+k+2)*B : ℕ)) : ℝ)/(l : ℝ))=
      (U.card : ℝ)*((2 : ℝ)^q*((q^2*(2*k^2+k+2)*B : ℕ) : ℝ)/(l : ℝ)) := by
    calc
      _ = ∑ _e∈U,(2 : ℝ)^q*((q^2*(2*k^2+k+2)*B : ℕ) : ℝ)/(l : ℝ) := by
        apply Finset.sum_congr rfl
        intro e he
        rw [hQ e he]
      _ = _ := by simp
  rw [hmain,herr] at hh
  simpa only [mul_add] using hh

end Oberwolfach

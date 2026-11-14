module

public import Oberwolfach.ColourRoundConcentration
public import Oberwolfach.AvailableColourExpectation
public import Oberwolfach.EqualDegreeRemainingExpectation

@[expose] public section

/-! A single outcome of the actual colouring experiment simultaneously
approximates every real available-list size and every remaining colour degree.
The underlying product law, omitted resource, and equalized degrees are explicit. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem colour_round_realization
    {V E C : Type*} [Fintype V] [Fintype E] [Fintype C] [DecidableEq V]
    (R : E → Finset V) (L : E → Finset C) (H : Finset E)
    {k l B s d : ℕ} (hk : 0<k) (hl : 1<l) (hs : 0<s) (hsl : s≤l)
    (hsize : ∀ e,(R e).card≤k) (hreal : ∀ e∈H,(R e).card=k)
    (hcard : ∀ e,(L e).card=l)
    (hcodeg : ∀ v w,v≠w → (Finset.univ.filter (fun e=>v∈R e ∧ w∈R e)).card≤B)
    (hdegree : ∀ v c,(hypergraphColourClique R L v c).card≤s)
    (heq : ∀ e∈H,∀ v∈R e,∀ c∈L e,(hypergraphColourClique R L v c).card=s)
    (hgraph : ∀ e,(Finset.univ.filter (fun f=>(hypergraphLineGraph R).Adj e f)).card≤d)
    (hcodegsmall : 2*(k^2*(k^2*B))≤l)
    {t : ℝ} (ht : 0<t)
    (hsmall : (l : ℝ)*(4*Real.exp (-t^2/
      (12*(k : ℝ)*(l : ℝ)+4*(2+(((k+3)*(k*B) : ℕ) : ℝ))*(3+((3*k : ℕ) : ℝ))*(s : ℝ))))≤t)
    (hprob : 8*((k : ℝ)+1)*Real.exp (-t^2/
      (12*(k : ℝ)*(l : ℝ)+4*(2+(((k+3)*(k*B) : ℕ) : ℝ))*(3+((3*k : ℕ) : ℝ))*(s : ℝ)))≤
      1/(4*((s*(1+k*l)*(d+1)^4 : ℕ) : ℝ))) :
    let G := hypergraphLineGraph R
    let ρ := (1-1/(l : ℝ))^(k*s)
    let κ := 1-(s : ℝ)*ρ/(l : ℝ)
    ∃ σ : E → C×Bool,(∀ e,(σ e).1∈L e) ∧
      (∀ e∈H,|((nibbleAvailableColours G (R e) (hypergraphVertexClique R) (L e) σ).card : ℝ)-
        (l : ℝ)*κ^k|≤6*((k : ℝ)+1)*t+
          (l : ℝ)*((2 : ℝ)^k*((k^2*(2*k^2+k+2)*B : ℕ) : ℝ)/(l : ℝ))) ∧
      (∀ z c,let U := realColourClass R L H z c
        |((remainingColourVertices G U (fun e=>(R e).erase z) (hypergraphVertexClique R) c σ).card : ℝ)-
          (U.card : ℝ)*(1-ρ)*κ^(k-1)|≤6*((k : ℝ)+1)*t+
          (U.card : ℝ)*(1/(l : ℝ)+ρ*(2/(l : ℝ)+2*((k*s : ℕ) : ℝ)/((l : ℝ)*((l : ℝ)-1)))+
            (2 : ℝ)^(k-1)*(((k-1)^2*(2*k^2+k+2)*B : ℕ) : ℝ)/(l : ℝ))) := by
  classical
  dsimp only
  let G := hypergraphLineGraph R
  have hL (e : E) : (L e).Nonempty := Finset.card_pos.mp (by rw [hcard];omega)
  let μ := fun e=>(FiniteLaw.uniformOn (L e) (hL e)).withCoin
    (equalizationCoin G L l (k*s) e)
    (equalizationCoin_bounds G L (by omega : 0<l) (k*s) e)
  let ν := FiniteLaw.pi μ
  obtain ⟨σ,hσ,hdev⟩ := colour_round_common_concentration R L H hk (by omega) hs hsl hsize hreal
    hcard hcodeg hdegree hgraph μ ht hsmall hprob
  refine ⟨σ,fun e=>uniformList_withCoin_support L hL _ _ σ hσ e,?_,?_⟩
  · intro e he
    have hmean := hypergraph_available_colour_expectation_equal_degrees R L hL hl hcard hsize (fun v w hvw=>by
      convert hcodeg v w hvw using 1
      congr 1
      ext e
      simp only [Finset.mem_filter]) hdegree hsl
      (R e) (L e) (by rw [hreal e he];exact hcodegsmall)
      (fun v hv c hc=>heq e he v hv c hc)
    dsimp only at hmean
    simp only [hcard,hreal e he] at hmean
    have hd := (hdev (Sum.inl ⟨e,he⟩)).le
    change |((nibbleAvailableColours G (R e) (hypergraphVertexClique R) (L e) σ).card : ℝ)-
      ν.expectation (fun τ=>((nibbleAvailableColours G (R e) (hypergraphVertexClique R) (L e) τ).card : ℝ))|≤_ at hd
    apply (abs_sub_le _ (ν.expectation (fun τ=>
      ((nibbleAvailableColours G (R e) (hypergraphVertexClique R) (L e) τ).card : ℝ))) _).trans
    convert add_le_add hd hmean using 1 <;> simp only [mul_div_assoc,ν,μ,G]
  · intro z c
    let U := realColourClass R L H z c
    have hU (e : E) (he : e∈U) : e∈H ∧ z∈R e ∧ c∈L e := by
      simpa only [U,realColourClass,Finset.mem_filter] using he
    have hQ (e : E) (he : e∈U) : ((R e).erase z).card=k-1 := by
      rw [Finset.card_erase_of_mem (hU e he).2.1,hreal e (hU e he).1]
    have hsmall' : 2*((k-1)^2*(k^2*B))≤l := by
      apply LE.le.trans ?_ hcodegsmall
      gcongr
      exact Nat.sub_le _ _
    have hmean := hypergraph_remaining_colour_expectation_equal_degrees R L hL hl hcard hsize (fun v w hvw=>by
      convert hcodeg v w hvw using 1
      congr 1
      ext e
      simp only [Finset.mem_filter])
      hdegree hsl U (fun e=>(R e).erase z) c hQ hsmall'
      (fun e he v hv=>heq e (hU e he).1 v (Finset.mem_of_mem_erase hv) c (hU e he).2.2)
    dsimp only at hmean
    have hd := (hdev (Sum.inr (z,c))).le
    change |((remainingColourVertices G U (fun e=>(R e).erase z) (hypergraphVertexClique R) c σ).card : ℝ)-
      ν.expectation (fun τ=>((remainingColourVertices G U (fun e=>(R e).erase z)
        (hypergraphVertexClique R) c τ).card : ℝ))|≤_ at hd
    exact (abs_sub_le _ (ν.expectation (fun τ=>
      ((remainingColourVertices G U (fun e=>(R e).erase z) (hypergraphVertexClique R) c τ).card : ℝ))) _).trans
        (add_le_add hd hmean)

end Oberwolfach

module

public import Oberwolfach.ColourRoundTests
public import Oberwolfach.RemainingColourSupports
public import Oberwolfach.HypergraphRemainingConcentration
public import Oberwolfach.AvailableColourConcentration

@[expose] public section

/-! One common event for all actual available lists and remaining colour
degrees of a fixed family of real edges. Auxiliary edges are sampled in
the same product law and can influence every retained-colour condition. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def colourRoundValue {V E C : Type*} [Fintype E] [DecidableEq V]
    (R : E → Finset V) (L : E → Finset C) (H : Finset E)
    (i : ColourRoundTest V C H) (σ : E → C×Bool) : ℝ :=
  match i with
  | .inl e => (nibbleAvailableColours (hypergraphLineGraph R) (R e.val)
      (hypergraphVertexClique R) (L e.val) σ).card
  | .inr p => (remainingColourVertices (hypergraphLineGraph R) (realColourClass R L H p.1 p.2)
      (fun e=>(R e).erase p.1) (hypergraphVertexClique R) p.2 σ).card

theorem colourRoundValue_support
    {V E C : Type*} [Fintype E] [DecidableEq V] [DecidableEq E]
    (R : E → Finset V) (L : E → Finset C) (H : Finset E)
    (i : ColourRoundTest V C H) (σ τ : E → C×Bool)
    (he : ∀ u∈closedSetNeighbours (hypergraphLineGraph R)
      (closedSetNeighbours (hypergraphLineGraph R) (colourRoundBase R L H i)),σ u=τ u) :
    colourRoundValue R L H i σ=colourRoundValue R L H i τ := by
  cases i with
  | inl e =>
    exact congrArg (fun S : Finset C=>(S.card : ℝ))
      (hypergraph_nibbleAvailableColours_support R e.val (L e.val) σ τ he)
  | inr p =>
    exact congrArg (fun S : Finset E=>(S.card : ℝ))
      (hypergraph_remainingColourVertices_support R (realColourClass R L H p.1 p.2)
        (fun e=>(R e).erase p.1) (fun e _=>Finset.erase_subset _ _) p.2 σ τ he)

theorem colour_round_common_concentration
    {V E C : Type*} [Fintype V] [Fintype E] [Fintype C] [DecidableEq V]
    (R : E → Finset V) (L : E → Finset C) (H : Finset E)
    {k l B s d : ℕ} (hk : 0<k) (hl : 0<l) (hs : 0<s) (hsl : s≤l)
    (hsize : ∀ e,(R e).card≤k) (hreal : ∀ e∈H,(R e).card=k)
    (hcard : ∀ e,(L e).card=l)
    (hcodeg : ∀ v w,v≠w → (Finset.univ.filter (fun e=>v∈R e ∧ w∈R e)).card≤B)
    (hdegree : ∀ v c,(hypergraphColourClique R L v c).card≤s)
    (hgraph : ∀ e,(Finset.univ.filter (fun f=>(hypergraphLineGraph R).Adj e f)).card≤d)
    (μ : E → FiniteLaw (C×Bool)) {t : ℝ} (ht : 0<t)
    (hsmall : (l : ℝ)*(4*Real.exp (-t^2/
      (12*(k : ℝ)*(l : ℝ)+4*(2+(((k+3)*(k*B) : ℕ) : ℝ))*(3+((3*k : ℕ) : ℝ))*(s : ℝ))))≤t)
    (hprob : 8*((k : ℝ)+1)*Real.exp (-t^2/
      (12*(k : ℝ)*(l : ℝ)+4*(2+(((k+3)*(k*B) : ℕ) : ℝ))*(3+((3*k : ℕ) : ℝ))*(s : ℝ)))≤
      1/(4*((s*(1+k*l)*(d+1)^4 : ℕ) : ℝ))) :
    ∃ σ,0<(FiniteLaw.pi μ).mass σ ∧ ∀ i : ColourRoundTest V C H,
      |colourRoundValue R L H i σ-(FiniteLaw.pi μ).expectation (colourRoundValue R L H i)|<
        6*((k : ℝ)+1)*t := by
  classical
  let G := hypergraphLineGraph R
  let ν := FiniteLaw.pi μ
  let D : ℝ := 12*(k : ℝ)*(l : ℝ)+
    4*(2+(((k+3)*(k*B) : ℕ) : ℝ))*(3+((3*k : ℕ) : ℝ))*(s : ℝ)
  let q : ℝ := 8*((k : ℝ)+1)*Real.exp (-t^2/D)
  let A := fun i σ=>6*((k : ℝ)+1)*t≤
    |colourRoundValue R L H i σ-ν.expectation (colourRoundValue R L H i)|
  have hscale {a : ℝ} (ha : 0<a) (haD : a≤D) : Real.exp (-t^2/a)≤Real.exp (-t^2/D) := by
    apply Real.exp_le_exp.mpr
    rw [neg_div,neg_div]
    apply neg_le_neg
    exact div_le_div_of_nonneg_left (sq_nonneg t) ha haD
  have htail (i : ColourRoundTest V C H) : ν.probability (A i)≤q := by
    cases i with
    | inl e =>
      have hRe : (R e.val).Nonempty := Finset.card_pos.mp (by rw [hreal _ e.property];exact hk)
      have hLe : (L e.val).Nonempty := Finset.card_pos.mp (by rw [hcard];exact hl)
      have hExp := hscale (by positivity : 0<12*(k : ℝ)*(l : ℝ)) (by dsimp [D];exact le_add_of_nonneg_right (by positivity))
      have hsm : (l : ℝ)*(4*Real.exp (-t^2/(12*(k : ℝ)*(l : ℝ))))≤t := by
        apply LE.le.trans ?_ hsmall
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hExp (by norm_num)) (Nat.cast_nonneg l)
      have hh := nibbleAvailableColours_concentration G (R e.val) hRe (hypergraphVertexClique R)
        (fun v _=>hypergraphVertexClique_isClique R v) (L e.val) hLe μ ht.le
        (by simpa only [hreal _ e.property,hcard] using hsm)
      simp only [hreal _ e.property,hcard] at hh
      apply hh.trans
      exact mul_le_mul_of_nonneg_left hExp (by positivity)
    | inr p =>
      let U := realColourClass R L H p.1 p.2
      have hUs : U.card≤s := (Finset.card_le_card (realColourClass_subset R L H p.1 p.2)).trans (hdegree _ _)
      have hUz (e : E) (he : e∈U) : p.1∈R e := by
        have hm : e∈H ∧ p.1∈R e ∧ p.2∈L e := by
          simpa only [U,realColourClass,Finset.mem_filter] using he
        exact hm.2.1
      by_cases hU : U.Nonempty
      · have hUr : (0 : ℝ)<U.card := by exact_mod_cast hU.card_pos
        have hExp := hscale
          (by positivity : 0<4*(2+(((k+3)*(k*B) : ℕ) : ℝ))*(3+((3*k : ℕ) : ℝ))*(U.card : ℝ))
          (by
            have hUs' : (U.card : ℝ)≤s := by exact_mod_cast hUs
            dsimp [D]
            nlinarith [mul_nonneg (by positivity :
              0≤4*(2+(((k+3)*(k*B) : ℕ) : ℝ))*(3+((3*k : ℕ) : ℝ)))
              (sub_nonneg.mpr hUs')])
        have hsm : (U.card : ℝ)*(4*Real.exp (-t^2/
            (4*(2+(((k+3)*(k*B) : ℕ) : ℝ))*(3+((3*k : ℕ) : ℝ))*(U.card : ℝ))))≤t := by
          apply LE.le.trans ?_ hsmall
          apply mul_le_mul (by exact_mod_cast hUs.trans hsl)
            (mul_le_mul_of_nonneg_left hExp (by norm_num)) (by positivity) (Nat.cast_nonneg l)
        have hh := hypergraph_remaining_colour_concentration R hsize hcodeg p.1 U hU hUz p.2 μ ht.le hsm
        apply hh.trans
        exact mul_le_mul_of_nonneg_left hExp (by positivity)
      · have hU0 : U=∅ := Finset.not_nonempty_iff_eq_empty.mp hU
        have hval (σ : E → C×Bool) : colourRoundValue R L H (Sum.inr p) σ=0 := by
          change ((remainingColourVertices G U (fun e=>(R e).erase p.1) (hypergraphVertexClique R) p.2 σ).card : ℝ)=0
          simp only [remainingColourVertices,hU0,Finset.filter_empty,Finset.card_empty,Nat.cast_zero]
        have hmean : ν.expectation (colourRoundValue R L H (Sum.inr p))=0 := by
          simp only [FiniteLaw.expectation,hval,mul_zero,Finset.sum_const_zero]
        have hz : ν.probability (A (Sum.inr p))=0 := by
          have hpos : 0<6*((k : ℝ)+1)*t := by positivity
          simp only [FiniteLaw.probability,A,hval,hmean,sub_self,abs_zero,not_le.mpr hpos,ite_false,Finset.sum_const_zero]
        rw [hz]
        dsimp [q]
        positivity
  obtain ⟨σ,hσ,hA⟩ := finiteLaw_neighbourhood_localLemma G μ A (colourRoundBase R L H)
    hs (by positivity : 0<1+k*l) hgraph (colourRoundBase_card R L H hs hdegree)
    (colourRoundBase_incidence R L H hsize hcard)
    (fun i σ τ he=>by
      dsimp only [A]
      rw [show colourRoundValue R L H i σ=colourRoundValue R L H i τ from
      colourRoundValue_support R L H i σ τ he])
    (fun i=>(htail i).trans hprob)
  exact ⟨σ,hσ,fun i=>lt_of_not_ge (hA i)⟩

end Oberwolfach

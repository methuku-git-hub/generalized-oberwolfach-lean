module

public import Oberwolfach.HypergraphJointColourRetention
public import Oberwolfach.FiniteAvoidanceExpansion

@[expose] public section

/-! Inclusion-exclusion applied to actual resource cliques. The fixed
family of resources is retained throughout the probability calculation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem hypergraph_colour_avoidance
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
    |μ.probability (fun σ=>∀ v∈S,∀ e∈hypergraphColourClique R L v c,
        coinRetainedColour G σ e≠some c)-
      (∏ v∈S,(1-((hypergraphColourClique R L v c).card : ℝ)*r))|≤
      (2 : ℝ)^S.card*((S.card^2*(2*k^2+k+2)*B : ℕ) : ℝ)/(l : ℝ) := by
  classical
  dsimp only
  let G := hypergraphLineGraph R
  let μ := FiniteLaw.pi (fun e=>(FiniteLaw.uniformOn (L e) (hL e)).withCoin
    (equalizationCoin G L l (k*s) e)
    (equalizationCoin_bounds G L (by omega : 0<l) (k*s) e))
  let r : ℝ := ((1-1/(l : ℝ))^(k*s))/(l : ℝ)
  let A := fun v σ=>∃ e∈hypergraphColourClique R L v c,coinRetainedColour G σ e=some c
  let p := fun v=>((hypergraphColourClique R L v c).card : ℝ)*r
  let ε := ((S.card^2*(2*k^2+k+2)*B : ℕ) : ℝ)/(l : ℝ)
  have hsub (T : Finset V) (hT : T∈S.powerset) :
      |μ.probability (fun σ=>True ∧ ∀ v∈T,A v σ)-1*(∏ v∈T,p v)|≤ε := by
    have hTS : T⊆S := Finset.mem_powerset.mp hT
    have hcardT : T.card≤S.card := Finset.card_le_card hTS
    have hsmallT : 2*(T.card^2*(k^2*B))≤l := by
      apply LE.le.trans ?_ hsmall
      gcongr
    have hh := hypergraph_joint_colour_retention (J:={v // v∈T}) R L hL hl hcard
      hsize hcodeg c hdegree hsl (fun v=>v.val) Subtype.val_injective
      (by simpa only [Fintype.card_coe] using hsmallT)
    dsimp only at hh
    have hprob : μ.probability (fun σ=>∀ j : {v // v∈T},A j.val σ)=
        μ.probability (fun σ=>True ∧ ∀ v∈T,A v σ) := by
      apply finiteLaw_probability_congr
      intro σ
      simp only [true_and,Subtype.forall]
    have hprod : (∏ j : {v // v∈T},p j.val)=∏ v∈T,p v := by
      exact Finset.prod_coe_sort T p
    change |μ.probability (fun σ=>∀ j : {v // v∈T},A j.val σ)-
      (∏ j : {v // v∈T},p j.val)|≤_ at hh
    rw [hprob,hprod] at hh
    simp only [Fintype.card_coe] at hh
    simp only [one_mul]
    apply hh.trans
    apply div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg l)
    exact_mod_cast (show T.card^2*(2*k^2+k+2)*B≤S.card^2*(2*k^2+k+2)*B by gcongr)
  have hh := finiteLaw_avoidance_approximation μ S A (fun _=>True) 1 p (fun _=>ε) hsub
  have hevent (σ : E → C×Bool) : (True ∧ ∀ v∈S,¬A v σ) ↔
      ∀ v∈S,∀ e∈hypergraphColourClique R L v c,coinRetainedColour G σ e≠some c := by
    simp only [A,true_and,not_exists,not_and]
  rw [finiteLaw_probability_congr _ _ _ hevent,one_mul] at hh
  simp only [Finset.sum_const,Finset.card_powerset,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat] at hh
  change |μ.probability _-(∏ v∈S,(1-p v))|≤_
  convert hh using 1
  dsimp [ε]
  ring

end Oberwolfach

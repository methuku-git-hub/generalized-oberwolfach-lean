module

public import Oberwolfach.SimplifiedCliqueJointRetention
public import Oberwolfach.CliqueRestrictionEstimates

@[expose] public section

/-! A joint-retention estimate for overlapping cliques. The sampling law,
original lists and equalization coins are unchanged by the proof's auxiliary
restriction of the clique vertex sets. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem overlapping_clique_joint_retention
    {V C J : Type*} [Fintype V] [Fintype C] [Fintype J]
    (G : SimpleGraph V) (L : V → Finset C) (hL : ∀ v,(L v).Nonempty)
    {l K B₀ B₁ s A : ℕ} (hl : 1<l) (hcard : ∀ v,(L v).card=l)
    (T : J → Finset V) (hT : ∀ j,∀ u∈T j,∀ v∈T j,u≠v → G.Adj u v)
    (hinter : ∀ i j,i≠j → (T i∩T j).card≤B₀)
    (hsize : ∀ j,(T j).card≤s) (hsl : s≤l)
    (hcross : ∀ i j,i≠j → ∀ v∈disjointFamilyRestriction Finset.univ T i,
      ((disjointFamilyRestriction Finset.univ T j).filter (G.Adj v)).card≤A)
    (c : C) (hc : ∀ j,∀ v∈T j,c∈L v)
    (hbound : ∀ v,c∈L v → (colourNeighbourSet G L v c).card≤K)
    (hpair : ∀ u v,u≠v → ¬G.Adj u v →
      (colourNeighbourSet G L u c∩colourNeighbourSet G L v c).card≤B₁)
    (hsmall : 2*((Fintype.card J)^2*B₁)≤l) :
    let μ := FiniteLaw.pi (fun u=>(FiniteLaw.uniformOn (L u) (hL u)).withCoin
      (equalizationCoin G L l K u) (equalizationCoin_bounds G L (by omega) K u))
    let r := ((1-1/(l : ℝ))^K)/(l : ℝ)
    |μ.probability (fun σ=>∀ j,∃ v∈T j,coinRetainedColour G σ v=some c)-
      (∏ j,((T j).card : ℝ)*r)|≤
      (2*(((Fintype.card J)^2*B₁ : ℕ) : ℝ)+
        (((Fintype.card J)^2*A : ℕ) : ℝ)+2*(((Fintype.card J)^2*B₀ : ℕ) : ℝ))/(l : ℝ) := by
  classical
  dsimp only
  let μ := FiniteLaw.pi (fun u=>(FiniteLaw.uniformOn (L u) (hL u)).withCoin
    (equalizationCoin G L l K u) (equalizationCoin_bounds G L (by omega : 0<l) K u))
  let r : ℝ := ((1-1/(l : ℝ))^K)/(l : ℝ)
  let T' := disjointFamilyRestriction Finset.univ T
  let n := Fintype.card J
  have hrho := equalized_retention_rate_bounds (l:=l) (by omega) K
  have hlr : (0 : ℝ)<l := by exact_mod_cast (show 0<l by omega)
  have hr : 0≤r ∧ r≤1/(l : ℝ) :=
    ⟨div_nonneg hrho.1 hlr.le,div_le_div_of_nonneg_right hrho.2 hlr.le⟩
  have hsub (j : J) : T' j⊆T j := disjointFamilyRestriction_subset Finset.univ T j
  have hsmallT (j : J) : (T' j).card≤s := (Finset.card_le_card (hsub j)).trans (hsize j)
  have hclique (j : J) : ∀ u∈T' j,∀ v∈T' j,u≠v → G.Adj u v :=
    fun u hu v hv hne=>hT j u (hsub j hu) v (hsub j hv) hne
  have hdis (i j : J) (hij : i≠j) : Disjoint (T' i) (T' j) :=
    disjointFamilyRestriction_disjoint Finset.univ T (Finset.mem_univ i) hij
  have hloss (j : J) : ((T j)\T' j).card≤n*B₀ := by
    simpa only [Finset.card_univ] using disjointFamilyRestriction_loss Finset.univ T j
      (fun i _ hij=>hinter j i (Ne.symm hij))
  have hpoint (j : J) (v : V) (hv : v∈T j) :
      μ.probability (fun σ=>coinRetainedColour G σ v=some c)≤r := by
    exact (equalizedColour_probability_at G L hL (by omega) hcard v c (hc j v hv)
      (hbound v (hc j v hv))).le
  have hp := finiteLaw_clique_restriction_uniform_loss G μ T T' hsub c hr.1 hloss hpoint
  have hpbound : (n : ℝ)*((n*B₀ : ℕ) : ℝ)*r≤((n^2*B₀ : ℕ) : ℝ)/(l : ℝ) := by
    calc
      _ ≤ (n : ℝ)*((n*B₀ : ℕ) : ℝ)*(1/(l : ℝ)) :=
        mul_le_mul_of_nonneg_left hr.2 (by positivity)
      _ = _ := by push_cast;ring
  have hp' := hp.2.trans hpbound
  have hm (j : J) : (T j).card-(T' j).card≤n*B₀ := by
    rw [← Finset.card_sdiff_of_subset (hsub j)]
    exact hloss j
  have hprod := finiteFamily_restriction_product_loss
    (fun j=>(T j).card) (fun j=>(T' j).card) (by omega : 0<l)
    (fun j=>Finset.card_le_card (hsub j)) (fun j=>(hsize j).trans hsl) hm hr
  have hprodBound : (Fintype.card J : ℝ)*((n*B₀ : ℕ) : ℝ)/(l : ℝ)=
      ((n^2*B₀ : ℕ) : ℝ)/(l : ℝ) := by dsimp [n];push_cast;ring
  rw [hprodBound] at hprod
  have hraw := disjoint_clique_joint_retention_simple G L hL hl hcard T' hclique hdis
    hsmallT hsl hcross c (fun j v hv=>hc j v (hsub j hv)) hbound hpair hsmall
  dsimp only at hraw
  change |μ.probability _-(∏ j,((T' j).card : ℝ)*r)|≤_ at hraw
  change |μ.probability _-(∏ j,((T j).card : ℝ)*r)|≤_
  obtain ⟨hlo,hhi⟩ := abs_le.mp hraw
  have he : (2*((n^2*B₁ : ℕ) : ℝ)+((n^2*A : ℕ) : ℝ)+2*((n^2*B₀ : ℕ) : ℝ))/(l : ℝ)=
      2*((n^2*B₁ : ℕ) : ℝ)/(l : ℝ)+((n^2*A : ℕ) : ℝ)/(l : ℝ)+
        2*(((n^2*B₀ : ℕ) : ℝ)/(l : ℝ)) := by ring
  change _≤(2*((n^2*B₁ : ℕ) : ℝ)+((n^2*A : ℕ) : ℝ)+2*((n^2*B₀ : ℕ) : ℝ))/(l : ℝ)
  rw [he]
  apply abs_le.mpr
  constructor <;> linarith [hp.1,hprod.1,hprod.2]

end Oberwolfach

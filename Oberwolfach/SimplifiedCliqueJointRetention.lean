module

public import Oberwolfach.DisjointCliqueJointRetention
public import Oberwolfach.FiniteProductPerturbation

@[expose] public section

/-! Normalizing the disjoint-clique estimate when each colour occurs at
most as often in a clique as the list size. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem equalized_retention_rate_bounds {l : ℕ} (hl : 0<l) (K : ℕ) :
    0≤(1-1/(l : ℝ))^K ∧ (1-1/(l : ℝ))^K≤1 := by
  have hlr : (1 : ℝ)≤l := by exact_mod_cast hl
  have hq : 0≤1-1/(l : ℝ) := sub_nonneg.mpr ((div_le_one (by positivity)).mpr hlr)
  exact ⟨pow_nonneg hq _,pow_le_one₀ hq (sub_le_self _ (by positivity))⟩

theorem disjoint_clique_joint_retention_simple
    {V C J : Type*} [Fintype V] [Fintype C] [Fintype J]
    (G : SimpleGraph V) (L : V → Finset C) (hL : ∀ v,(L v).Nonempty)
    {l K B s A : ℕ} (hl : 1<l) (hcard : ∀ v,(L v).card=l)
    (T : J → Finset V) (hT : ∀ j,∀ u∈T j,∀ v∈T j,u≠v → G.Adj u v)
    (hdis : ∀ i j,i≠j → Disjoint (T i) (T j))
    (hsize : ∀ j,(T j).card≤s) (hsl : s≤l)
    (hcross : ∀ i j,i≠j → ∀ v∈T i,((T j).filter (G.Adj v)).card≤A)
    (c : C) (hc : ∀ j,∀ v∈T j,c∈L v)
    (hbound : ∀ v,c∈L v → (colourNeighbourSet G L v c).card≤K)
    (hpair : ∀ u v,u≠v → ¬G.Adj u v →
      (colourNeighbourSet G L u c∩colourNeighbourSet G L v c).card≤B)
    (hsmall : 2*((Fintype.card J)^2*B)≤l) :
    let μ := FiniteLaw.pi (fun u=>(FiniteLaw.uniformOn (L u) (hL u)).withCoin
      (equalizationCoin G L l K u) (equalizationCoin_bounds G L (by omega) K u))
    let r := ((1-1/(l : ℝ))^K)/(l : ℝ)
    |μ.probability (fun σ=>∀ j,∃ v∈T j,coinRetainedColour G σ v=some c)-
      (∏ j,((T j).card : ℝ)*r)|≤
      2*(((Fintype.card J)^2*B : ℕ) : ℝ)/(l : ℝ)+
        (((Fintype.card J)^2*A : ℕ) : ℝ)/(l : ℝ) := by
  classical
  dsimp only
  let r : ℝ := ((1-1/(l : ℝ))^K)/(l : ℝ)
  let b := r^(Fintype.card J)
  let N := ∏ j,((T j).card : ℝ)
  let ε := 2*(((Fintype.card J)^2*B : ℕ) : ℝ)/(l : ℝ)
  have hrho := equalized_retention_rate_bounds (l:=l) (by omega) K
  have hb : 0≤b := pow_nonneg (div_nonneg hrho.1 (Nat.cast_nonneg _)) _
  have hε : 0≤ε := by dsimp [ε];positivity
  have hN : N≤(s : ℝ)^(Fintype.card J) := by
    calc
      _ ≤ ∏ _j : J,(s : ℝ) := Finset.prod_le_prod₀
        (fun j _=>Nat.cast_nonneg _) (fun j _=>by exact_mod_cast hsize j)
      _ = _ := by simp
  have hNb : N*b≤1 := (mul_le_mul_of_nonneg_right hN hb).trans
    (normalized_tuple_mass_le_one (by omega) hsl hrho)
  have heprod : (∏ j,((T j).card : ℝ)*r)=N*b := by
    rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ]
  have hh := disjoint_clique_joint_retention G L hL hl hcard T hT hdis hsize hcross
    c hc hbound hpair hsmall
  dsimp only at hh
  change |_-N*b|≤N*ε*b+_ at hh
  change |_-(∏ j,((T j).card : ℝ)*r)|≤ε+_
  rw [heprod]
  have he : N*ε*b≤ε := by nlinarith [mul_le_mul_of_nonneg_left hNb hε]
  have hbad := normalized_tuple_conflict_le (n:=Fintype.card J) (A:=A)
    (by omega : 0<l) hsl hrho
  exact hh.trans (add_le_add he hbad)

end Oberwolfach

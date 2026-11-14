module

public import Oberwolfach.ColourRetentionCoins

@[expose] public section

/-! Uniform choices from vertex lists and explicit retention coins.
The equality of retention probabilities is derived from the product law. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def FiniteLaw.uniformOn {C : Type*} [Fintype C] (L : Finset C)
    (hL : L.Nonempty) : FiniteLaw C where
  mass c := if c∈L then 1/(L.card : ℝ) else 0
  nonneg c := by split_ifs <;> positivity
  total := by
    classical
    rw [Fintype.sum_ite_mem]
    simp only [Finset.sum_const,nsmul_eq_mul]
    have hc : (L.card : ℝ)≠0 := by exact_mod_cast hL.card_pos.ne'
    field_simp

def colourNeighbourSet {V C : Type*} [Fintype V]
    (G : SimpleGraph V) (L : V → Finset C) (v : V) (c : C) : Finset V :=
  Finset.univ.filter (fun u=>G.Adj v u ∧ c∈L u)

theorem uniformList_avoidance_product
    {V C : Type*} [Fintype V] [Fintype C]
    (G : SimpleGraph V) (L : V → Finset C) (hL : ∀ v,(L v).Nonempty)
    {l : ℕ} (hcard : ∀ v,(L v).card=l) (v : V) (c : C) :
    (∏ u∈Finset.univ.filter (fun u=>G.Adj v u),
      (1-(FiniteLaw.uniformOn (L u) (hL u)).mass c))=
      (1-1/(l : ℝ))^(colourNeighbourSet G L v c).card := by
  classical
  have hpoint (u : V) : 1-(FiniteLaw.uniformOn (L u) (hL u)).mass c=
      if c∈L u then 1-1/(l : ℝ) else 1 := by
    by_cases hc : c∈L u <;> simp [FiniteLaw.uniformOn,hc,hcard]
  simp_rw [hpoint]
  rw [← Finset.prod_filter,Finset.filter_filter]
  exact Finset.prod_const _

def equalizationCoin {V C : Type*} [Fintype V]
    (G : SimpleGraph V) (L : V → Finset C) (l K : ℕ) (v : V) (c : C) : ℝ :=
  (1-1/(l : ℝ))^(K-(colourNeighbourSet G L v c).card)

theorem equalizationCoin_bounds
    {V C : Type*} [Fintype V] (G : SimpleGraph V)
    (L : V → Finset C) {l : ℕ} (hl : 0<l) (K : ℕ) (v : V) (c : C) :
    0≤equalizationCoin G L l K v c ∧ equalizationCoin G L l K v c≤1 := by
  have hlr : (1 : ℝ)≤l := by exact_mod_cast hl
  have hp : (1 : ℝ)/(l : ℝ)≤1 := (div_le_one (by positivity)).mpr hlr
  have hq : 0≤1-1/(l : ℝ) := sub_nonneg.mpr hp
  have hq1 : 1-1/(l : ℝ)≤1 := sub_le_self _ (by positivity)
  exact ⟨pow_nonneg hq _,pow_le_one₀ hq hq1⟩

theorem equalizedColour_probability
    {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C]
    (G : SimpleGraph V) (L : V → Finset C) (hL : ∀ v,(L v).Nonempty)
    {l K : ℕ} (hl : 0<l) (hcard : ∀ v,(L v).card=l)
    (hbound : ∀ v c,c∈L v → (colourNeighbourSet G L v c).card≤K)
    (v : V) (c : C) :
    (FiniteLaw.pi (fun u=>(FiniteLaw.uniformOn (L u) (hL u)).withCoin
      (equalizationCoin G L l K u) (equalizationCoin_bounds G L hl K u))).probability
      (fun σ=>coinRetainedColour G σ v=some c)=
      if c∈L v then (1/(l : ℝ))*(1-1/(l : ℝ))^K else 0 := by
  rw [coinRetainedColour_probability,uniformList_avoidance_product G L hL hcard]
  by_cases hc : c∈L v
  · simp only [FiniteLaw.uniformOn,hc,ite_true,hcard,equalizationCoin]
    rw [mul_assoc,← pow_add,Nat.sub_add_cancel (hbound v c hc)]
  · simp only [FiniteLaw.uniformOn,hc,ite_false,zero_mul]

theorem equalizedColour_survival_probability
    {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C]
    (G : SimpleGraph V) (L : V → Finset C) (hL : ∀ v,(L v).Nonempty)
    {l K : ℕ} (hl : 0<l) (hcard : ∀ v,(L v).card=l)
    (hbound : ∀ v c,c∈L v → (colourNeighbourSet G L v c).card≤K) (v : V) :
    (FiniteLaw.pi (fun u=>(FiniteLaw.uniformOn (L u) (hL u)).withCoin
      (equalizationCoin G L l K u) (equalizationCoin_bounds G L hl K u))).probability
      (fun σ=>coinColourSurvives G σ v)=(1-1/(l : ℝ))^K := by
  let μ := FiniteLaw.pi (fun u=>(FiniteLaw.uniformOn (L u) (hL u)).withCoin
    (equalizationCoin G L l K u) (equalizationCoin_bounds G L hl K u))
  have he (c : C) : μ.probability (fun σ=>coinColourSurvives G σ v ∧ (σ v).1=c)=
      μ.probability (fun σ=>coinRetainedColour G σ v=some c) := by
    apply finiteLaw_probability_congr
    intro σ
    rw [coinRetainedColour_eq_some,and_comm]
  calc
    _ = ∑ c,μ.probability (fun σ=>coinColourSurvives G σ v ∧ (σ v).1=c) :=
      finiteLaw_probability_value_partition μ _ (fun σ=>(σ v).1)
    _ = ∑ c,μ.probability (fun σ=>coinRetainedColour G σ v=some c) :=
      Finset.sum_congr rfl (fun c _=>he c)
    _ = ∑ c,if c∈L v then (1/(l : ℝ))*(1-1/(l : ℝ))^K else 0 :=
      Finset.sum_congr rfl (fun c _=>equalizedColour_probability G L hL hl hcard hbound v c)
    _ = _ := by
      rw [Fintype.sum_ite_mem]
      simp only [Finset.sum_const,nsmul_eq_mul,hcard]
      have hl0 : (l : ℝ)≠0 := by exact_mod_cast hl.ne'
      field_simp

end Oberwolfach

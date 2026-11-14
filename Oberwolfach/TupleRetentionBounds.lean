module

public import Oberwolfach.RetentionOverlapBounds

@[expose] public section

/-! The exact root-set estimates expressed for injective tuples. Repeated
vertices must be excluded explicitly before using the tuple length. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem conflicting_retention_probability_zero
    {V C J : Type*} [Fintype V] [Fintype C]
    (G : SimpleGraph V) (μ : FiniteLaw (V → C×Bool)) (f : J → V) (c : C)
    (hbad : ∃ i j,G.Adj (f i) (f j)) :
    μ.probability (fun σ=>∀ j,coinRetainedColour G σ (f j)=some c)=0 := by
  obtain ⟨i,j,hij⟩ := hbad
  have hn (σ : V → C×Bool) : ¬∀ j,coinRetainedColour G σ (f j)=some c := by
    intro h
    exact coinRetainedColour_proper G σ hij c (h i) (h j)
  unfold FiniteLaw.probability
  simp only [hn,ite_false,Finset.sum_const_zero]

theorem equalized_tuple_retention_bounds
    {V C J : Type*} [Fintype V] [DecidableEq V] [Fintype C] [Fintype J]
    (G : SimpleGraph V) (L : V → Finset C) (hL : ∀ v,(L v).Nonempty)
    {l K B : ℕ} (hl : 1<l) (hcard : ∀ v,(L v).card=l)
    (f : J → V) (hfi : Function.Injective f)
    (hgood : ∀ i j,¬G.Adj (f i) (f j)) (c : C) (hc : ∀ j,c∈L (f j))
    (hbound : ∀ j,(colourNeighbourSet G L (f j) c).card≤K)
    (hpair : ∀ i j,i≠j →
      (colourNeighbourSet G L (f i) c∩colourNeighbourSet G L (f j) c).card≤B)
    (hsmall : 2*((Fintype.card J)^2*B)≤l) :
    let p := (FiniteLaw.pi (fun u=>(FiniteLaw.uniformOn (L u) (hL u)).withCoin
      (equalizationCoin G L l K u)
      (equalizationCoin_bounds G L (by omega) K u))).probability
      (fun σ=>∀ j,coinRetainedColour G σ (f j)=some c)
    let b := (((1-1/(l : ℝ))^K)/(l : ℝ))^(Fintype.card J)
    b≤p ∧ p≤(1+2*(((Fintype.card J)^2*B : ℕ) : ℝ)/(l : ℝ))*b := by
  classical
  let S := Finset.univ.image f
  have hSc : S.card=Fintype.card J := by
    rw [Finset.card_image_of_injective _ hfi,Finset.card_univ]
  have hS : ∀ u∈S,∀ v∈S,¬G.Adj u v := by
    intro u hu v hv
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hv
    exact hgood i j
  have hcS : ∀ v∈S,c∈L v := by
    intro v hv
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hv
    exact hc j
  have hbS : ∀ v∈S,(colourNeighbourSet G L v c).card≤K := by
    intro v hv
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hv
    exact hbound j
  have hpS : ∀ u∈S,∀ v∈S,u≠v →
      (colourNeighbourSet G L u c∩colourNeighbourSet G L v c).card≤B := by
    intro u hu v hv huv
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hv
    exact hpair i j (fun he=>huv (congrArg f he))
  have hh := equalized_joint_retention_bounds G L hL hl hcard S hS c hcS hbS hpS
    (by simpa only [hSc] using hsmall)
  have hevent (σ : V → C×Bool) :
      (∀ v∈S,coinRetainedColour G σ v=some c) ↔
        ∀ j,coinRetainedColour G σ (f j)=some c := by
    simp only [S,Finset.mem_image,Finset.mem_univ,true_and]
    constructor
    · intro h j
      exact h (f j) ⟨j,rfl⟩
    · intro h v hv
      obtain ⟨j,rfl⟩ := hv
      exact h j
  dsimp only at hh ⊢
  rw [finiteLaw_probability_congr _ _ _ hevent,hSc] at hh
  exact hh

end Oberwolfach

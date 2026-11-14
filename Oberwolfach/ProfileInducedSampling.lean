module

public import Oberwolfach.ProfileSubsetExchange
public import Oberwolfach.InducedResourceWeights
public import Oberwolfach.UniformProfileConcentration

@[expose] public section

/-! Fixed-size, classwise sampling of the original weighted resources.
An external vertex is retained explicitly in Z. The bound depends on
the sampled ground size, not the size of the ambient graph. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {s : ℕ} {V : Fin s → Type*} [∀ i,Fintype (V i)]
    {W C : Type*} [Fintype W] [DecidableEq W] [Fintype C]

theorem profile_induced_degree_exchange (e : (Σ i,V i) ↪ W)
    (R : C → Finset W) (c J : ℕ) (hc : 2 ≤ c)
    (hR : ∀ C₀,(R C₀).card=c) (hJ : ∀ A : Finset W,Fintype.card {C₀ : C // R C₀=A} ≤ J)
    (w : C → ℝ) (B : ℝ) (hB : 0 ≤ B) (hw : ∀ C₀,0 ≤ w C₀ ∧ w C₀ ≤ B)
    (Z : Finset W) (v : W) (hv : v∈Z) {m : Fin s → ℕ}
    (σ τ : ∀ i,FixedSubset (V i) (m i)) (i : Fin s)
    (hagree : ∀ j,j≠i → σ j=τ j) (x y : V i)
    (he : τ i=fixedSubsetMap (Equiv.swap x y) (σ i)) :
    |hypergraphWeightedDegree R (inducedResourceWeight R w (Z∪(profileRootSet σ).map e)) v-
      hypergraphWeightedDegree R (inducedResourceWeight R w (Z∪(profileRootSet τ).map e)) v| ≤
      2*(J:ℝ)*(Z.card+(∑ j,m j)+1:ℕ)^(c-2)*B := by
  have hh := induced_resource_degree_exchange R c J hc hR hJ w B hB hw
    (Z∪(profileRootSet σ).map e) (Z∪(profileRootSet τ).map e) v
    (Finset.mem_union_left _ hv) (Finset.mem_union_left _ hv)
  have hb := profileSample_exchange_card_bounds e Z σ τ i hagree x y he
  have hsum : (((Z∪(profileRootSet σ).map e)\(Z∪(profileRootSet τ).map e)).card+
      ((Z∪(profileRootSet τ).map e)\(Z∪(profileRootSet σ).map e)).card:ℕ) ≤ 2 := by omega
  have hr : (((Z∪(profileRootSet σ).map e)\(Z∪(profileRootSet τ).map e)).card+
      ((Z∪(profileRootSet τ).map e)\(Z∪(profileRootSet σ).map e)).card:ℝ) ≤ 2 := by exact_mod_cast hsum
  have hp : (((Z∪(profileRootSet σ).map e)∪(Z∪(profileRootSet τ).map e)).card:ℝ)^(c-2) ≤
      (Z.card+(∑ j,m j)+1:ℕ)^(c-2) := by
    apply pow_le_pow_left₀ (Nat.cast_nonneg _)
    exact_mod_cast hb.2.2
  apply hh.trans
  push_cast at hp ⊢
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul (mul_le_mul_of_nonneg_right hr (Nat.cast_nonneg _)) hp
      (by positivity) (by positivity)) hB

theorem profile_induced_degree_mgf (e : (Σ i,V i) ↪ W)
    (R : C → Finset W) (c J : ℕ) (hc : 2 ≤ c)
    (hR : ∀ C₀,(R C₀).card=c) (hJ : ∀ A : Finset W,Fintype.card {C₀ : C // R C₀=A} ≤ J)
    (w : C → ℝ) (B : ℝ) (hB : 0 ≤ B) (hw : ∀ C₀,0 ≤ w C₀ ∧ w C₀ ≤ B)
    (Z : Finset W) (v : W) (hv : v∈Z) (m : Fin s → ℕ)
    [∀ i,Nonempty (FixedSubset (V i) (m i))]
    (hm : ∀ i,m i ≤ Fintype.card (V i)) (u : ℝ) :
    let μ := FiniteLaw.pi (fun i => FiniteLaw.uniform (FixedSubset (V i) (m i)))
    let X := fun σ => hypergraphWeightedDegree R
      (inducedResourceWeight R w (Z∪(profileRootSet σ).map e)) v
    μ.expectation (fun σ => Real.exp (u*(X σ-μ.expectation X))) ≤
      Real.exp (u^2*(∑ i,(m i:ℝ))*(2*(J:ℝ)*(Z.card+(∑ j,m j)+1:ℕ)^(c-2)*B)^2/8) := by
  have hh := uniform_profile_mgf m hm
    (fun σ => hypergraphWeightedDegree R (inducedResourceWeight R w (Z∪(profileRootSet σ).map e)) v)
    (2*(J:ℝ)*(Z.card+(∑ j,m j)+1:ℕ)^(c-2)*B) (by positivity)
    (fun i σ τ ha x y he => profile_induced_degree_exchange e R c J hc hR hJ w B hB hw Z v hv σ τ i ha x y he) u
  simpa only [mul_assoc] using hh

theorem profile_induced_degree_tail (e : (Σ i,V i) ↪ W)
    (R : C → Finset W) (c J : ℕ) (hc : 2 ≤ c)
    (hR : ∀ C₀,(R C₀).card=c) (hJ : ∀ A : Finset W,Fintype.card {C₀ : C // R C₀=A} ≤ J)
    (w : C → ℝ) (B : ℝ) (hB : 0 ≤ B) (hw : ∀ C₀,0 ≤ w C₀ ∧ w C₀ ≤ B)
    (Z : Finset W) (v : W) (hv : v∈Z) (m : Fin s → ℕ)
    [∀ i,Nonempty (FixedSubset (V i) (m i))]
    (hm : ∀ i,m i ≤ Fintype.card (V i)) (t : ℝ) (ht : 0 ≤ t) :
    let μ := FiniteLaw.pi (fun i => FiniteLaw.uniform (FixedSubset (V i) (m i)))
    let X := fun σ => hypergraphWeightedDegree R
      (inducedResourceWeight R w (Z∪(profileRootSet σ).map e)) v
    μ.probability (fun σ => t ≤ |X σ-μ.expectation X|) ≤
      2*Real.exp (-2*t^2/((∑ i,(m i:ℝ))*(2*(J:ℝ)*(Z.card+(∑ j,m j)+1:ℕ)^(c-2)*B)^2)) := by
  apply finiteLaw_mgf_absolute_tail _ _ (by positivity) _ ht
  intro u
  convert profile_induced_degree_mgf e R c J hc hR hJ w B hB hw Z v hv m hm u using 1 <;> ring

end Oberwolfach

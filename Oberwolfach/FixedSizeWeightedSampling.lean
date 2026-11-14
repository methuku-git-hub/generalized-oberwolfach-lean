module

public import Oberwolfach.FixedSizeProfileConditioning
public import Oberwolfach.ProfileLinearRateConcentration
public import Oberwolfach.ProfileInducedSampling

@[expose] public section

/-! A uniform exponential conditional tail for the actual weighted
cycle sum, at the unchanged original class sample sizes. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option synthInstance.maxSize 256
set_option maxHeartbeats 4000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {s : ℕ} {V : Fin s → Type*} [∀ i,Fintype (V i)] [∀ i,DecidableEq (V i)]
    {W C : Type*} [Fintype W] [DecidableEq W] [Fintype C]

theorem profile_fixed_size_weighted_linear_tail
    (e : (Σ i,V i) ↪ W) (R : C → Finset W) (c J : ℕ) (hc : 2 ≤ c) (hJpos : 1 ≤ J)
    (hR : ∀ C₀,(R C₀).card=c)
    (hJ : ∀ Y : Finset W,Fintype.card {C₀ : C // R C₀=Y} ≤ J)
    (w : C → ℝ) (B t ξ : ℝ) (hB : 0 < B) (ht : 1 ≤ t) (hξ : 0 ≤ ξ)
    (hw : ∀ C₀,0 ≤ w C₀ ∧ w C₀ ≤ B/t^(c-1))
    (A : Finset W) (T : ∀ i,Finset (V i)) (m : Fin s → ℕ)
    (hT : ∀ i,(T i).card ≤ m i)
    [∀ i,Nonempty (FixedSubset {v : V i // v∉T i} (m i-(T i).card))]
    [∀ i,Nonempty (FixedSubset (V i) (m i))]
    (hm : ∀ i,m i-(T i).card ≤ Fintype.card {v : V i // v∉T i})
    (hsteps : ∑ i,((m i-(T i).card:ℕ):ℝ) ≤ c*t)
    (hroots : (A∪(Finset.univ.sigma T).map e).card ≤ c)
    (v : W) (hv : v∈A∪(Finset.univ.sigma T).map e) :
    let μ := FiniteLaw.pi (fun i => FiniteLaw.uniform (FixedSubset (V i) (m i)))
    let ν := FiniteLaw.pi (fun i => FiniteLaw.uniform (FixedSubset {v : V i // v∉T i} (m i-(T i).card)))
    let f := fun τ => hypergraphWeightedDegree R (inducedResourceWeight R w (A∪(profileRootSet τ).map e)) v
    let mean := ν.expectation (fun σ => f (fillProfileRootsAtSize T m hT σ))
    let L := 2*(J:ℝ)*(2*(c:ℝ)+1)^(c-2)*B
    μ.probability (fun τ => (∀ i,T i⊆(τ i).val) ∧ ξ ≤ |f τ-mean|) ≤
      μ.probability (fun τ => ∀ i,T i⊆(τ i).val)*
        (2*Real.exp (-(2*ξ^2/((c:ℝ)*L^2))*t)) := by
  let k := fun i => m i-(T i).card
  let Z := A∪(Finset.univ.sigma T).map e
  let e' := (profileRootFreeEmbedding T).trans e
  let L := 2*(J:ℝ)*(2*(c:ℝ)+1)^(c-2)*B
  let f := fun τ : ∀ i,FixedSubset (V i) (m i) =>
    hypergraphWeightedDegree R (inducedResourceWeight R w (A∪(profileRootSet τ).map e)) v
  let g := fun σ : ∀ i,FixedSubset {v : V i // v∉T i} (k i) => f (fillProfileRootsAtSize T m hT σ)
  have htpos : 0<t := by linarith
  have hcpos : (0:ℝ)<c := by exact_mod_cast (show 0<c by omega)
  have hJposR : (0:ℝ)<J := by exact_mod_cast (show 0<J by omega)
  have hL : 0<L := by dsimp [L];positivity
  have heground (σ : ∀ i,FixedSubset {v : V i // v∉T i} (k i)) :
      A∪(profileRootSet (fillProfileRootsAtSize T m hT σ)).map e=Z∪(profileRootSet σ).map e' := by
    rw [fillProfileRootsAtSize_ground,Finset.map_union,Finset.map_map]
    exact (Finset.union_assoc _ _ _).symm
  have hg (σ : ∀ i,FixedSubset {v : V i // v∉T i} (k i)) :
      g σ=hypergraphWeightedDegree R (inducedResourceWeight R w (Z∪(profileRootSet σ).map e')) v := by
    dsimp [g,f]
    rw [heground]
  have hsum : ((∑ i,k i:ℕ):ℝ) ≤ (c:ℝ)*t := by simpa only [Nat.cast_sum] using hsteps
  have hsize : (Z.card+(∑ i,k i)+1:ℕ) ≤ (2*(c:ℝ)+1)*t := by
    have hz : (Z.card:ℝ) ≤ c := by exact_mod_cast hroots
    push_cast
    nlinarith
  have hexchange : ∀ i σ τ,(∀ j,j≠i → σ j=τ j) → ∀ x y : {v : V i // v∉T i},
      τ i=fixedSubsetMap (Equiv.swap x y) (σ i) → |g σ-g τ| ≤ L/t := by
    intro i σ τ ha x y he
    rw [hg,hg]
    have hh := profile_induced_degree_exchange e' R c J hc hR hJ w (B/t^(c-1))
      (by positivity) hw Z v hv σ τ i ha x y (by convert he using 1 <;> congr!)
    convert hh.trans (degree_sample_exchange_coefficient c hc J B t (Z.card+(∑ i,k i)+1:ℕ)
      (by positivity) hB.le htpos (by positivity) hsize) using 1 <;> congr!
  have htail := uniform_profile_linear_rate_tail k hm g c L t ξ hcpos hL htpos hξ hsteps
    (fun i σ τ ha x y he => hexchange i σ τ ha x y (by convert he using 1 <;> congr!))
  have hlaw := profile_fixed_size_conditional_probability T m hT
    (fun τ => ξ ≤ |f τ-(FiniteLaw.pi (fun i => FiniteLaw.uniform (FixedSubset {v : V i // v∉T i} (k i)))).expectation g|)
  dsimp only
  rw [hlaw]
  exact mul_le_mul_of_nonneg_left htail (finiteLaw_probability_nonneg _ _)

end Oberwolfach

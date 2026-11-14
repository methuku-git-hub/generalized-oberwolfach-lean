module

public import Oberwolfach.IndexedMatchingBridge
public import Oberwolfach.HypergraphWeightMoments

@[expose] public section

/-! Exact weighted sums and injective projection for indexed integer copies.
The floor error depends on positive support, not the original index count. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem resource_copy_weight_sum {E : Type*} [Fintype E] (m : E → ℕ) (g : E → ℝ) :
    (∑ c : (Σ e,Fin (m e)),g c.1)=∑ e,(m e : ℝ)*g e := by
  simp only [Fintype.sum_sigma,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]

theorem resource_copy_matching_projection_weights
    {V E : Type*} [Fintype E] [DecidableEq V] [DecidableEq E]
    (R : E → Finset V) (m : E → ℕ) (hR : ∀ e,(R e).Nonempty)
    (M : Finset (Σ e,Fin (m e)))
    (hM : ∀ c∈M,∀ d∈M,c≠d → Disjoint (R c.1) (R d.1)) :
    (∀ e∈M.image Sigma.fst,∀ f∈M.image Sigma.fst,e≠f → Disjoint (R e) (R f)) ∧
    (∀ g : E → ℝ,(∑ e∈M.image Sigma.fst,g e)=∑ c∈M,g c.1) := by
  have hinj : Set.InjOn Sigma.fst (M : Set (Σ e,Fin (m e))) := by
    intro c hc d hd heq
    by_contra hne
    obtain ⟨v,hv⟩ := hR c.1
    have hdis := hM c hc d hd hne
    rw [← heq] at hdis
    exact Finset.disjoint_left.mp hdis hv hv
  constructor
  · intro e he f hf hef
    obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp he
    obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp hf
    exact hM c hc d hd (fun hh=>hef (congrArg Sigma.fst hh))
  · intro g
    exact Finset.sum_image hinj

theorem sum_floor_weighted_support_bounds
    {E : Type*} [Fintype E] (w g : E → ℝ) (T : ℕ) (b : ℝ)
    (hw : ∀ e,0≤w e) (hb : 0≤b) (hg : ∀ e,0≤g e ∧ g e≤b) :
    (T : ℝ)*(∑ e,g e*w e)-(Finset.univ.filter (fun e=>0<w e)).card*b≤
      ∑ e,g e*⌊(T : ℝ)*w e⌋₊ ∧
    (∑ e,g e*⌊(T : ℝ)*w e⌋₊)≤(T : ℝ)*(∑ e,g e*w e) := by
  have hlow (e : E) : (T : ℝ)*(g e*w e)-(if 0<w e then b else 0)≤g e*⌊(T : ℝ)*w e⌋₊ := by
    by_cases he : 0<w e
    · simp only [he,ite_true]
      have hf := Nat.lt_floor_add_one ((T : ℝ)*w e)
      have hm := mul_le_mul_of_nonneg_left hf.le (hg e).1
      nlinarith [(hg e).2]
    · have hz : w e=0 := le_antisymm (le_of_not_gt he) (hw e)
      simp [hz]
  have hupp (e : E) : g e*⌊(T : ℝ)*w e⌋₊≤(T : ℝ)*(g e*w e) := by
    have hf := Nat.floor_le (mul_nonneg (Nat.cast_nonneg T) (hw e))
    have hm := mul_le_mul_of_nonneg_left hf (hg e).1
    nlinarith
  constructor
  · have hs := Finset.sum_le_sum (fun e (_ : e∈Finset.univ)=>hlow e)
    simpa only [Finset.sum_sub_distrib,← Finset.mul_sum,← Finset.sum_filter,Finset.sum_const,
      nsmul_eq_mul] using hs
  · simpa only [← Finset.mul_sum] using Finset.sum_le_sum (fun e (_ : e∈Finset.univ)=>hupp e)


theorem rounded_resource_degree_bounds
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (R : E → Finset V) (w : E → ℝ) (T : ℕ) (η : ℝ)
    (hw : ∀ e,0≤w e)
    (hs : ((Finset.univ.filter (fun e=>0<w e)).card : ℝ)≤η*T)
    (hdegree : ∀ v,1-η≤hypergraphWeightedDegree R w v ∧
      hypergraphWeightedDegree R w v≤1+η) :
    ∀ v,(1-2*η)*(T : ℝ)≤
        ((∑ e,if v∈R e then ⌊(T : ℝ)*w e⌋₊ else 0 : ℕ) : ℝ) ∧
      ((∑ e,if v∈R e then ⌊(T : ℝ)*w e⌋₊ else 0 : ℕ) : ℝ)≤(1+η)*T := by
  intro v
  obtain ⟨hl,hu⟩ := sum_floor_weighted_support_bounds w (fun e=>if v∈R e then 1 else 0) T 1 hw (by norm_num)
    (fun e=>by split_ifs <;> norm_num)
  simp only [ite_mul,one_mul,zero_mul,mul_one] at hl hu
  have ht := Nat.cast_nonneg (α:=ℝ) T
  have hlo := mul_le_mul_of_nonneg_left (hdegree v).1 ht
  have hhi := mul_le_mul_of_nonneg_left (hdegree v).2 ht
  unfold hypergraphWeightedDegree at hlo hhi
  have heq : ((∑ e,if v∈R e then ⌊(T : ℝ)*w e⌋₊ else 0 : ℕ) : ℝ)=
      ∑ e,if v∈R e then (⌊(T : ℝ)*w e⌋₊ : ℝ) else 0 := by
    push_cast
    rfl
  rw [heq]
  constructor <;> nlinarith

theorem rounded_resource_test_bounds
    {E : Type*} [Fintype E] (w g : E → ℝ) (T : ℕ) (η b W : ℝ)
    (hw : ∀ e,0≤w e) (hb : 0≤b) (hg : ∀ e,0≤g e ∧ g e≤b)
    (hW : ∑ e,g e*w e=W)
    (hs : ((Finset.univ.filter (fun e=>0<w e)).card : ℝ)*b≤η*T*W) :
    (1-η)*(T : ℝ)*W≤(∑ c : (Σ e,Fin ⌊(T : ℝ)*w e⌋₊),g c.1) ∧
    (∑ c : (Σ e,Fin ⌊(T : ℝ)*w e⌋₊),g c.1)≤(T : ℝ)*W := by
  obtain ⟨hl,hu⟩ := sum_floor_weighted_support_bounds w g T b hw hb hg
  rw [hW] at hl hu
  have he : (∑ c : (Σ e,Fin ⌊(T : ℝ)*w e⌋₊),g c.1)=∑ e,g e*⌊(T : ℝ)*w e⌋₊ := by
    rw [resource_copy_weight_sum]
    apply Finset.sum_congr rfl
    intro e _
    ring
  rw [he]
  constructor <;> nlinarith

end Oberwolfach

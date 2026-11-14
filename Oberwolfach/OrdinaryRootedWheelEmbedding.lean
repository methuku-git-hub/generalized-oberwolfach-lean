module

public import Oberwolfach.FixedPathCycles
public import Oberwolfach.DenseCommonNeighbourBounds
public import Oberwolfach.OrdinaryWheelResources

@[expose] public section

/-! A wheel through a specified rim vertex, avoiding prescribed finite
sets. The relative spoke density is fixed before the forbidden-set size. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U : Type*} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem common_spoke_hub_avoiding (H : V → U → Prop) (A : Finset V) (B : Finset U)
    (r : ℕ) (hr : 0 < r) (hA : A.card ≤ r)
    (hH : ∀ v∈A,(1-1/(2*(r:ℝ)))*(Fintype.card U:ℝ) ≤ (Finset.univ.filter (fun u => H v u)).card)
    (hB : 2*B.card < Fintype.card U) :
    ∃ u,u∉B ∧ ∀ v∈A,H v u := by
  let N (v : V) := Finset.univ.filter (fun u => H v u)
  have hcommon := common_neighbour_card_lower (Finset.univ : Finset U) A N
    (1-1/(2*(r:ℝ))) (by
      intro v hv
      simpa only [Finset.card_univ,Finset.univ_inter,N] using hH v hv)
  have hrR : (0:ℝ) < r := by exact_mod_cast hr
  have hAR : (A.card:ℝ) ≤ r := by exact_mod_cast hA
  have hfrac : (A.card:ℝ)*(1-(1-1/(2*(r:ℝ)))) ≤ 1/2 := by
    have hh := mul_le_mul_of_nonneg_right hAR (by positivity : (0:ℝ) ≤ 1/(2*(r:ℝ)))
    have he : (r:ℝ)*(1/(2*(r:ℝ)))=1/2 := by field_simp
    rw [he] at hh
    convert hh using 1 <;> ring
  simp only [Finset.card_univ] at hcommon
  have hU : (0:ℝ) ≤ Fintype.card U := Nat.cast_nonneg _
  have hhalf : (1/2)*(Fintype.card U:ℝ) ≤ ((common Finset.univ A N).card:ℝ) := by
    nlinarith
  have hBR : 2*(B.card:ℝ) < Fintype.card U := by exact_mod_cast hB
  have hsize : B.card < (common Finset.univ A N).card := by
    have hh : (B.card:ℝ) < (common Finset.univ A N).card := by linarith
    exact_mod_cast hh
  obtain ⟨u,hu,hout⟩ := Finset.exists_mem_notMem_of_card_lt_card hsize
  refine ⟨u,hout,?_⟩
  simpa only [common,N,Finset.mem_filter,Finset.mem_univ,true_and] using hu

theorem ordinary_rooted_wheel_embedding (β : ℝ) (hβ : 0 < β) (r b : ℕ) (hr : 3 ≤ r) :
    ∃ n₀ : ℕ,∀ n : ℕ,n₀ ≤ n →
    ∀ (V U : Type*) [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U],Fintype.card V ≤ n →
    ∀ (G : SimpleGraph V) (H : V → U → Prop),
    (∀ v,(1/2+β)*(n:ℝ) ≤ G.degree v) →
    (∀ v,(1-1/(2*(r:ℝ)))*(Fintype.card U:ℝ) ≤ (Finset.univ.filter (fun u => H v u)).card) →
    ∀ (x : V) (S : Finset V) (B : Finset U),S.card ≤ b → x∉S → 2*B.card < Fintype.card U →
    ∃ W : OrdinaryWheel G ⊥ H r,
      x∈(ordinaryWheelRim W).support ∧ ordinaryWheelHub W∉B ∧
      ∀ v∈(ordinaryWheelRim W).support,v∉S := by
  obtain ⟨n₀,hn₀⟩ := fixed_cycle_through_vertex β hβ r b hr
  refine ⟨n₀,?_⟩
  intro n hn V U _ _ _ _ hV G H hdeg hH x S B hS hx hB
  obtain ⟨C,hC,hCG,hxC,havoid⟩ := hn₀ n hn V hV G hdeg x S hS hx
  obtain ⟨u,hu,hall⟩ := common_spoke_hub_avoiding H C.support.toFinset B r (by omega)
    (by rw [hC.support_card]) (fun v _ => hH v) hB
  let W : OrdinaryWheel G ⊥ H r := ⟨(⟨⟨C,hC⟩,hCG⟩,u),
    (fun v hv => hall v (Set.mem_toFinset.mpr hv)),fun _ _ _ _ => not_false⟩
  exact ⟨W,hxC,hu,havoid⟩

end Oberwolfach

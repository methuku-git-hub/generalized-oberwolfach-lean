module

public import Oberwolfach.EdgeRetention

@[expose] public section

/-! A fixed dense induced graph remains dense after independent retention.
The union bound runs over its fixed vertex set, before either sample is used. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem retained_neighbour_count_low {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V) (μ : Sym2 V → FiniteLaw Bool) (v : V)
    (δ α : ℝ) (hα : 0<α) (hS : 0<S.card)
    (hμ : ∀ e,1-α/8≤(μ e).mass true)
    (hdeg : (δ+α/2)*S.card≤((G.neighborFinset v∩S).card:ℝ)) :
    (FiniteLaw.pi μ).probability (fun σ =>
      (retainedNeighbourCount G S σ v:ℝ)≤(δ+α/4)*S.card)≤
      2*Real.exp (-α^2*S.card/32) := by
  have hm : (0:ℝ)<S.card := Nat.cast_pos.mpr hS
  have hc : ((G.neighborFinset v∩S).card:ℝ)≤S.card := by
    exact_mod_cast Finset.card_le_card (Finset.inter_subset_right (s₁:=G.neighborFinset v) (s₂:=S))
  have hmean : (δ+3*α/8)*S.card≤∑ x∈G.neighborFinset v∩S,(μ s(v,x)).mass true := by
    have hh : (1-α/8)*((G.neighborFinset v∩S).card:ℝ)≤
        ∑ x∈G.neighborFinset v∩S,(μ s(v,x)).mass true := by
      calc
        _ = ∑ _x∈G.neighborFinset v∩S,(1-α/8) := by simp;ring
        _ ≤ _ := Finset.sum_le_sum (fun x _ => hμ s(v,x))
    have hc' := mul_le_mul_of_nonneg_left hc hα.le
    nlinarith
  apply le_trans (finiteLaw_probability_mono _ _ _ ?_)
    (le_trans (retained_neighbour_count_tail G S μ v (α*S.card/8) (by positivity)) ?_)
  · intro σ hσ
    have hh := le_abs_self ((∑ x∈G.neighborFinset v∩S,(μ s(v,x)).mass true)-
      (retainedNeighbourCount G S σ v:ℝ))
    rw [abs_sub_comm] at hh
    linarith
  · have he : -2*(α*S.card/8)^2/S.card = -α^2*S.card/32 := by field_simp;ring
    rw [he]

theorem retained_induced_min_degree_failure {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V) (μ : Sym2 V → FiniteLaw Bool)
    (δ α : ℝ) (hα : 0<α) (hS : 0<S.card)
    (hμ : ∀ e,1-α/8≤(μ e).mass true)
    (hdeg : ∀ v∈S,(δ+α/2)*S.card≤((G.neighborFinset v∩S).card:ℝ)) :
    (FiniteLaw.pi μ).probability (fun σ => ∃ v∈S,
      (retainedNeighbourCount G S σ v:ℝ)≤(δ+α/4)*S.card)≤
      2*S.card*Real.exp (-α^2*S.card/32) := by
  apply (finiteLaw_union_bound (FiniteLaw.pi μ) S
    (fun v σ => (retainedNeighbourCount G S σ v:ℝ)≤(δ+α/4)*S.card)).trans
  calc
    _ ≤ ∑ _v∈S,2*Real.exp (-α^2*S.card/32) :=
      Finset.sum_le_sum (fun v hv => retained_neighbour_count_low G S μ v δ α hα hS hμ (hdeg v hv))
    _ = _ := by simp;ring

end Oberwolfach

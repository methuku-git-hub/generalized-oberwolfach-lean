module

public import Oberwolfach.SparseAlternatingCorrection

@[expose] public section

/-! Uniform constants for alternating corrections, depending only on the
lower density bound and preceding both graph classes and all other data. -/
set_option autoImplicit false
set_option maxHeartbeats 1400000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem sparse_alternating_correction (p₀ : ℝ) (hp₀ : 0<p₀) :
    ∃ δ₀ C : ℝ,0<δ₀ ∧ 0<C ∧
      ∀ (A B : Type) [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B],
      ∀ (H : A → B → Prop) (p : B → ℝ) (δ D : ℝ),
      0<Fintype.card A → 0<Fintype.card B → 0≤δ → 0≤D →
      (∀ u,p₀≤p u ∧ p u≤1) →
      (∀ u,|bipColumnDegree H u-(Fintype.card A:ℝ)*p u|≤δ*Fintype.card A) →
      (∀ u v,u≠v → |bipPairIntersection H v u-(Fintype.card A:ℝ)*p v*p u|≤δ*Fintype.card A) →
      (∀ u v t,u≠v → u≠t → v≠t →
        |bipTripleIntersection H u v t-(Fintype.card A:ℝ)*p u*p v*p t|≤δ*Fintype.card A) →
      (∀ x,∃ E : Finset A,(E.card:ℝ)≤D ∧
        ∀ y,y∉E → |bipWeightedCodegree H (fun u=>1/p u) x y-(Fintype.card B:ℝ)|≤δ*Fintype.card B) →
      δ+D/(Fintype.card A:ℝ)+1/(Fintype.card B:ℝ)≤δ₀ →
      ∀ z : A×B → ℝ,z∈zeroMarginalSpace H →
        ∃ t : BipartiteFourCycle H → ℝ,
          (∀ e,z e=∑ Q,t Q*bipartiteFourCycleVector Q e) ∧
          (∀ e,(∑ Q,if FourCycleIncident Q e then |t Q| else 0)≤C*‖z‖) := by
  let L := max 1 (1/p₀)
  have hL1 : 1≤L := le_max_left _ _
  have hL0 : 0<L := lt_of_lt_of_le zero_lt_one hL1
  refine ⟨1/(200*L^6),8*L^3*(1+9*L^3),by positivity,by positivity,?_⟩
  intro A B _ _ _ _ H p δ D ha hb hδ hD hp hdeg hpair htriple hcodeg hsmall z hz
  let q (u : B) := 1/p u
  have hp0 (u : B) : 0<p u := hp₀.trans_le (hp u).1
  have hq (u : B) : 0≤q u ∧ q u≤L := by
    constructor
    · exact div_nonneg zero_le_one (hp0 u).le
    · exact (one_div_le_one_div_of_le hp₀ (hp u).1).trans (le_max_right _ _)
  have hdata : SparseIntersectionData H p q L δ D :=
    { one_le_L := hL1
      delta_nonneg := hδ
      D_nonneg := hD
      density := fun u=>⟨(hp0 u).le,(hp u).2⟩
      inverse_bounds := hq
      inverse_identity := fun u=>by dsimp only [q];exact div_mul_cancel₀ 1 (hp0 u).ne'
      degree_error := hdeg
      pair_error := hpair
      triple_error := htriple
      exceptions := hcodeg }
  exact sparse_alternating_correction_inverse_profile H p q L δ D hdata ha hb hsmall z hz

end Oberwolfach

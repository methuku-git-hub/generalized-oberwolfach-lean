module

public import Oberwolfach.TransferGreedyConfigurations
public import Oberwolfach.DivisibilityRepairScales

@[expose] public section

/-! The transfer lower count is derived by extending the explicit ordered
configuration, with the conflict loss and its order threshold displayed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V U : Type*} [Fintype V] [DecidableEq V]

theorem transferConfigurationOfPattern_injective (P F : SimpleGraph V) (A : Finset V)
    (r : ℕ) (hr : 3 ≤ r) (v : V) (H : V → U → Prop) (u u' : U)
    (hroot : H v u ∧ H v u') (hA : ∀ z∈A,H z u ∧ H z u') :
    Function.Injective (fun f : {f : Fin (r^2) → V // RootedPatternGood P F A (transferConstructionGraph r hr) v f}=>
      transferConfigurationOfPattern P F A r hr v f.val f.property H u u' hroot hA) := by
  intro f g he
  apply Subtype.ext
  funext i
  obtain ⟨a,ha⟩ := (transferPositionEquiv r hr).surjective i
  change transferFreePosition r hr a=i at ha
  have hh := congrArg (fun T : OrdinaryTransferConfiguration hr P F H v u u'=>T.labels a) he
  change transferLabelsOfPattern P F A r hr v f.val f.property a=
    transferLabelsOfPattern P F A r hr v g.val g.property a at hh
  rw [transferLabelsOfPattern_apply,transferLabelsOfPattern_apply,ha] at hh
  exact hh

theorem ordinary_transfer_greedy_count (P F : SimpleGraph V) (A : Finset V)
    (r : ℕ) (hr : 3 ≤ r) (v : V) (H : V → U → Prop) (u u' : U)
    (hroot : H v u ∧ H v u') (hA : ∀ z∈A,H z u ∧ H z u')
    (δ L a : ℝ) (hδ : δ≤1) (hL : 0≤L) (ha : 0≤a)
    (hbudget : a≤(1-((if r=3 then 3 else 2:ℕ):ℝ)*(1-δ))*(A.card:ℝ)-
      ((r:ℝ)^2+1)*(L+1))
    (hP : ∀ z∈A∪{v},δ*(A.card:ℝ)≤((A∩P.neighborFinset z).card:ℝ))
    (hF : ∀ z,(F.degree z:ℝ)≤L) :
    a^(r^2)≤(Fintype.card (OrdinaryTransferConfiguration hr P F H v u u'):ℝ) := by
  have hh := rooted_pattern_embedding_count P F A (transferConstructionGraph r hr) v
    (r^2) (if r=3 then 3 else 2) δ L a hδ hL ha (by simpa only [Nat.cast_pow] using hbudget)
    hP hF (fun n _=>by rw [predecessorGraph_back_card];exact transferPredecessors_card r (n+1) hr)
  have hc := Fintype.card_le_of_injective _ (transferConfigurationOfPattern_injective P F A r hr v H u u' hroot hA)
  exact hh.trans (by exact_mod_cast hc)

theorem ordinary_transfer_configurations_many (r : ℕ) (hr : 3 ≤ r)
    (δ β : ℝ) (hδ : δ≤1) (hβ : 0<β)
    (hmargin : 0<1-((if r=3 then 3 else 2:ℕ):ℝ)*(1-δ)) :
    ∃ c : ℝ,0<c ∧ ∀ L : ℝ,0≤L → ∃ N : ℕ,
    ∀ (V U : Type) [Fintype V] [DecidableEq V],N≤Fintype.card V →
    ∀ (P F : SimpleGraph V) (A : Finset V) (v : V) (H : V → U → Prop) (u u' : U),
      β*Fintype.card V≤(A.card:ℝ) →
      (∀ z∈A∪{v},δ*(A.card:ℝ)≤((A∩P.neighborFinset z).card:ℝ)) →
      (∀ z,(F.degree z:ℝ)≤L) → (H v u ∧ H v u') → (∀ z∈A,H z u ∧ H z u') →
      c*(Fintype.card V:ℝ)^(r^2)≤Fintype.card (OrdinaryTransferConfiguration hr P F H v u u') := by
  let γ := 1-((if r=3 then 3 else 2:ℕ):ℝ)*(1-δ)
  let c := (γ*β/2)^(r^2)
  have hγ : 0<γ := hmargin
  refine ⟨c,by dsimp [c];positivity,?_⟩
  intro L hL
  obtain ⟨N,hN⟩ := eventually_constant_le_linear (((r:ℝ)^2+1)*(L+1)) (γ*β/2) (by positivity)
  refine ⟨N,?_⟩
  intro V U _ _ hn P F A v H u u' hsize hP hF hroot hA
  have hbudget : γ*β/2*Fintype.card V≤γ*(A.card:ℝ)-((r:ℝ)^2+1)*(L+1) := by
    have hs := mul_le_mul_of_nonneg_left hsize hγ.le
    have hh := hN (Fintype.card V) hn
    nlinarith only [hs,hh]
  have hh := ordinary_transfer_greedy_count P F A r hr v H u u' hroot hA δ L
    (γ*β/2*Fintype.card V) hδ hL (by positivity) hbudget hP hF
  simpa only [mul_pow,c] using hh

end Oberwolfach

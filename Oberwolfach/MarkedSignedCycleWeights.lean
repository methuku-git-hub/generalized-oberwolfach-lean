module

public import Oberwolfach.SignedWeightsFromCapacities

@[expose] public section

/-! The signed marked-cycle response is derived from the proved numerical
capacity theorem, with its original length and separation quantifiers. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
universe u v w
attribute [local instance] Classical.propDecidable

theorem marked_signed_cycle_weights_uniform_length (α p₀ : ℝ)
    (hα : 0<α) (hαmax : α≤1) (hp₀ : 0<p₀) (hp₀max : p₀≤1/2) :
    ∃ c₀ : ℕ,∀ k : ℕ,c₀≤k+2 →
    ∃ ε C : ℝ,0<ε ∧ 0<C ∧
    ∀ b : ℕ,∃ n₀ : ℕ,
    ∀ (V : Type u) (E : Type v) (K : Type w)
      [Fintype V] [Fintype E] [Fintype K] [DecidableEq V],
    ∀ (tail head : E → V) (ktail khead : K → V),
    Function.Injective (fun e => (tail e,head e)) →
    Function.Injective (fun e => (ktail e,khead e)) →
    ∀ (p D : ℝ),p₀≤p → p≤1/2 → n₀≤Fintype.card V →
    (Fintype.card V:ℝ)/2≤D → D≤2*Fintype.card V →
    (∀ x,|occurrenceDegree tail x-p*D|≤ε*Fintype.card V) →
    (∀ x,|occurrenceDegree head x-p*D|≤ε*Fintype.card V) →
    (∀ x,|occurrenceDegree ktail x-p*D/(k+1:ℝ)|≤ε*Fintype.card V) →
    (∀ x,|occurrenceDegree khead x-p*D/(k+1:ℝ)|≤ε*Fintype.card V) →
    (∀ x y,x≠y → α*p^2*Fintype.card V≤
      ((Finset.univ.filter (fun z => (∃ e,tail e=x ∧ head e=z) ∧ (∃ e,tail e=z ∧ head e=y))).card:ℝ)) →
    (∀ S T : Finset V,(1-2*min (α/16) (p/128))*Fintype.card V<(S.card:ℝ)+T.card →
      (α*p/16)*Fintype.card V*min (S.card:ℝ) T.card≤
      ((Finset.univ.filter (fun e => tail e∈S ∧ head e∈T)).card:ℝ)) →
    ∀ π : Equiv.Perm V,
    (∀ e,¬PermutationClose π b (tail e) (head e)) →
    (∀ e,¬PermutationClose π b (ktail e) (khead e)) →
    (fun _ : E⊕K => (1:ℝ))∈markedBalanceSubspace tail head ktail khead (k+1) →
    ∀ z : E⊕K → ℝ,z∈markedBalanceSubspace tail head ktail khead (k+1) →
    ∀ η : ℝ,0≤η → ‖z‖≤η →
    ∃ q : MarkedCycleTuple tail head ktail khead (k+1) π b → ℝ,
      (∀ C',|q C'|≤C*η/(Fintype.card V:ℝ)^k) ∧
      (∑ C',q C' • markedCycleIncidence tail head ktail khead (k+1) C'.val)=z := by
  obtain ⟨c₀,hc₀⟩ := marked_capacity_cycle_weights_uniform_length.{u,v,w} α p₀ hα hαmax hp₀ hp₀max
  refine ⟨c₀,?_⟩
  intro k hk
  obtain ⟨ε,κ,a,A,hε,hκ,ha,hA,hcap⟩ := hc₀ k hk
  refine ⟨ε,2*A/κ,hε,by positivity,?_⟩
  intro b
  obtain ⟨n₀,hn₀⟩ := hcap b
  refine ⟨n₀,?_⟩
  intro V E K _ _ _ _ tail head ktail khead hinj hkinj p D hp hpmax hn hDlo hDhi hdo hdi hdko hdki htwo hcut π hsep hksep hunit z hz η hη hnorm
  have hrep := hn₀ V E K tail head ktail khead hinj hkinj p D hp hpmax hn hDlo hDhi
    hdo hdi hdko hdki htwo hcut π hsep hksep
  have hcap' (w : E⊕K → ℝ) (hw : w∈markedBalanceSubspace tail head ktail khead (k+1))
      (hclose : ‖w-(fun _ => (1:ℝ))‖≤κ) :
      ∃ q : MarkedCycleTuple tail head ktail khead (k+1) π b → ℝ,
        (∀ C',0≤q C' ∧ q C'≤A/(Fintype.card V:ℝ)^k) ∧
        (∑ C',q C' • markedCycleIncidence tail head ktail khead (k+1) C'.val)=w := by
    obtain ⟨q,hq,he⟩ := hrep w hw hclose
    exact ⟨q,(fun C' => ⟨(hq C').1.le,(hq C').2.2⟩),he⟩
  obtain ⟨q,hq,he⟩ := signed_weights_from_capacities
    (fun C' : MarkedCycleTuple tail head ktail khead (k+1) π b => markedCycleIncidence tail head ktail khead (k+1) C'.val)
    (markedBalanceSubspace tail head ktail khead (k+1)) (fun _ => 1) hunit κ
    (A/(Fintype.card V:ℝ)^k) hκ (by positivity) hcap' z hz η hη hnorm
  refine ⟨q,?_,he⟩
  intro C'
  calc
    _ ≤ (2*(A/(Fintype.card V:ℝ)^k)/κ)*η := hq C'
    _ = _ := by ring

end Oberwolfach

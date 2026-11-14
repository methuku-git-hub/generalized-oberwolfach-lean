module

public import Oberwolfach.MarkedSignedCycleWeights
public import Oberwolfach.MarkedWheelLifts
public import Oberwolfach.MarkedSpokeResiduals

@[expose] public section

/-! The first two stages of marked wheel correction, with the actual
numerical capacity theorem and compatible-hub lift. The unit balance and
arc separation conditions are derived, not inserted as additional inputs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
universe u v w z
attribute [local instance] Classical.propDecidable

theorem marked_rim_correction_uniform_parameters (α p₀ : ℝ)
    (hα : 0<α) (hαmax : α≤1) (hp₀ : 0<p₀) (hp₀max : p₀≤1/2) :
    ∃ c₀ : ℕ,∀ k : ℕ,c₀≤k+2 → ∀ β : ℝ,0<β →
    ∃ ε C : ℝ,0<ε ∧ 0<C ∧
    ∀ b : ℕ,∃ n₀ : ℕ,
    ∀ (V : Type u) (E : Type v) (K : Type w) (U : Type z)
      [Fintype V] [Fintype E] [Fintype K] [Fintype U] [DecidableEq V] [DecidableEq U],
    ∀ (tail head : E → V) (ktail khead : K → V) (π : Equiv.Perm V),
    Function.Injective (markedPhysicalEdge tail head ktail khead π) →
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
    ∀ H₀ Hₖ : V → U → Prop,
    (∀ C' : MarkedCycleTuple tail head ktail khead (k+1) π b,
      β*Fintype.card V≤(Fintype.card {u // MarkedHubCompatible H₀ Hₖ C'.val u}:ℝ)) →
    (∀ v,occurrenceDegree (Sum.elim tail ktail) v=occurrenceDegree (Sum.elim head khead) v) →
    (∀ v,occurrenceDegree khead v=∑ u,if Hₖ v u then (1:ℝ) else 0) →
    (∀ v,occurrenceDegree (Sum.elim tail ktail) v=
      (∑ u,if H₀ v u then (1:ℝ) else 0)+(∑ u,if Hₖ v u then (1:ℝ) else 0)) →
    (∀ u,(∑ v,if H₀ v u then (1:ℝ) else 0)=(k+1:ℝ)*(∑ v,if Hₖ v u then (1:ℝ) else 0)) →
    ∀ η : ℝ,0≤η → η<1 →
    ∀ ψ : MarkedWheel tail head ktail khead (k+1) π b H₀ Hₖ → ℝ,
    (∀ e,|markedWheelRimLoad ψ e-1|≤η) →
    ∃ R : MarkedWheel tail head ktail khead (k+1) π b H₀ Hₖ → ℝ,
      (∀ e,markedWheelRimLoad R e=1-markedWheelRimLoad ψ e) ∧
      (∀ W',|R W'|≤C*η/(Fintype.card V:ℝ)^(k+1)) ∧
      (∀ j v u,|markedWheelSpokeLoad R j v u|≤(k+2)*C*η) := by
  obtain ⟨c₀,hc₀⟩ := marked_signed_cycle_weights_uniform_length.{u,v,w} α p₀ hα hαmax hp₀ hp₀max
  refine ⟨c₀,?_⟩
  intro k hk β hβ
  obtain ⟨ε,C,hε,hC,hcap⟩ := hc₀ k hk
  refine ⟨ε,C/β,hε,by positivity,?_⟩
  intro b
  obtain ⟨n₀,hn₀⟩ := hcap b
  refine ⟨max 1 n₀,?_⟩
  intro V E K U _ _ _ _ _ _ tail head ktail khead π hphys p D hp hpmax hn hDlo hDhi hdo hdi hdko hdki htwo hcut H₀ Hₖ hhub hdir hK hout hcol η hη hηmax ψ herr
  have hnpos : 0<Fintype.card V := (show 0<max 1 n₀ by omega).trans_le hn
  have hn' : (0:ℝ)<Fintype.card V := Nat.cast_pos.mpr hnpos
  obtain ⟨hinj,hkinj⟩ := markedPhysicalEdge_endpoint_injections tail head ktail khead π hphys
  have hunit := marked_unit_balance_of_spoke_degrees tail head ktail khead (k+1) H₀ Hₖ hdir hK hout (by simpa only [Nat.cast_add,Nat.cast_one] using hcol)
  have hsep (e : E⊕K) : ¬PermutationClose π b (Sum.elim tail ktail e) (Sum.elim head khead e) := by
    apply markedWheelRimLoad_nonzero_separated (by omega : 1≤k+1) ψ e
    intro he
    have hh := herr e
    rw [he] at hh
    norm_num at hh
    linarith
  let zR : E⊕K → ℝ := (fun _ => 1)-markedWheelRimLoad ψ
  have hzR : zR∈markedBalanceSubspace tail head ktail khead (k+1) :=
    Submodule.sub_mem _ hunit (markedWheelRimLoad_balanced hinj hkinj ψ)
  have hzNorm : ‖zR‖≤η := by
    apply (pi_norm_le_iff_of_nonneg hη).mpr
    intro e
    simpa only [zR,Pi.sub_apply,Real.norm_eq_abs,abs_sub_comm] using herr e
  obtain ⟨q,hq,he⟩ := hn₀ V E K tail head ktail khead hinj hkinj p D hp hpmax
    ((le_max_right _ _).trans hn) hDlo hDhi hdo hdi hdko hdki htwo hcut π
    (fun e => hsep (Sum.inl e)) (fun e => hsep (Sum.inr e)) hunit zR hzR η hη hzNorm
  have hhubpos (C' : MarkedCycleTuple tail head ktail khead (k+1) π b) :
      0<Fintype.card {u // MarkedHubCompatible H₀ Hₖ C'.val u} := by
    have hh : (0:ℝ)<β*Fintype.card V := by positivity
    exact_mod_cast hh.trans_le (hhub C')
  let R := markedWheelLift H₀ Hₖ q
  have hRb (W' : MarkedWheel tail head ktail khead (k+1) π b H₀ Hₖ) :
      |R W'|≤(C/β)*η/(Fintype.card V:ℝ)^(k+1) := by
    have hh := markedWheelLift_bound (by omega : 1≤k+1) H₀ Hₖ q β (C*η) hβ (by positivity) hnpos
      hhub (fun C' => by simpa only [Nat.add_sub_cancel] using hq C') W'
    calc
      _ ≤ (C*η/β)/(Fintype.card V:ℝ)^(k+1) := hh
      _ = _ := by ring
  refine ⟨R,?_,hRb,?_⟩
  · intro e
    rw [show R=markedWheelLift H₀ Hₖ q from rfl,markedWheelLift_rim H₀ Hₖ q hhubpos e]
    have hh := congrFun he e
    simpa only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,zR,Pi.sub_apply] using hh
  · intro j v u
    have hh := markedWheelSpokeLoad_coefficient_bound R ((C/β)*η/(Fintype.card V:ℝ)^(k+1))
      (by positivity) hRb j v u
    calc
      _ ≤ ((C/β)*η/(Fintype.card V:ℝ)^(k+1))*((k+1+1)*(Fintype.card V:ℝ)^(k+1)) := by simpa only [Nat.cast_add,Nat.cast_one] using hh
      _ = _ := by field_simp;ring

theorem marked_rim_correction_uniform_length (α p₀ β : ℝ)
    (hα : 0<α) (hαmax : α≤1) (hp₀ : 0<p₀) (hp₀max : p₀≤1/2) (hβ : 0<β) :
    ∃ c₀ : ℕ,∀ k : ℕ,c₀≤k+2 →
    ∃ ε C : ℝ,0<ε ∧ 0<C ∧
    ∀ b : ℕ,∃ n₀ : ℕ,
    ∀ (V : Type u) (E : Type v) (K : Type w) (U : Type z)
      [Fintype V] [Fintype E] [Fintype K] [Fintype U] [DecidableEq V] [DecidableEq U],
    ∀ (tail head : E → V) (ktail khead : K → V) (π : Equiv.Perm V),
    Function.Injective (markedPhysicalEdge tail head ktail khead π) →
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
    ∀ H₀ Hₖ : V → U → Prop,
    (∀ C' : MarkedCycleTuple tail head ktail khead (k+1) π b,
      β*Fintype.card V≤(Fintype.card {u // MarkedHubCompatible H₀ Hₖ C'.val u}:ℝ)) →
    (∀ v,occurrenceDegree (Sum.elim tail ktail) v=occurrenceDegree (Sum.elim head khead) v) →
    (∀ v,occurrenceDegree khead v=∑ u,if Hₖ v u then (1:ℝ) else 0) →
    (∀ v,occurrenceDegree (Sum.elim tail ktail) v=
      (∑ u,if H₀ v u then (1:ℝ) else 0)+(∑ u,if Hₖ v u then (1:ℝ) else 0)) →
    (∀ u,(∑ v,if H₀ v u then (1:ℝ) else 0)=(k+1:ℝ)*(∑ v,if Hₖ v u then (1:ℝ) else 0)) →
    ∀ η : ℝ,0≤η → η<1 →
    ∀ ψ : MarkedWheel tail head ktail khead (k+1) π b H₀ Hₖ → ℝ,
    (∀ e,|markedWheelRimLoad ψ e-1|≤η) →
    ∃ R : MarkedWheel tail head ktail khead (k+1) π b H₀ Hₖ → ℝ,
      (∀ e,markedWheelRimLoad R e=1-markedWheelRimLoad ψ e) ∧
      (∀ W',|R W'|≤C*η/(Fintype.card V:ℝ)^(k+1)) ∧
      (∀ j v u,|markedWheelSpokeLoad R j v u|≤(k+2)*C*η) := by
  obtain ⟨c₀,hc₀⟩ := marked_rim_correction_uniform_parameters.{u,v,w,z} α p₀ hα hαmax hp₀ hp₀max
  exact ⟨c₀,fun k hk=>hc₀ k hk β hβ⟩

end Oberwolfach

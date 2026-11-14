module

public import Oberwolfach.IsolatorConfigurationCounts
public import Oberwolfach.FiniteSignedAverages

@[expose] public section

/-! Averaging signed rim isolators at all admissible hubs and k-sets.
The denominator is the actual number of configurations. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem root_configuration_quotient (n γ : ℝ) (hn : n≠0) {k s : ℕ}
    (hs : 1≤s) (hsk : s≤k) :
    n^(k-s)/(γ*n^(k-1))=1/(γ*n^(s-1)) := by
  have he : k-1=(k-s)+(s-1) := by omega
  rw [he,pow_add]
  field_simp

theorem averaged_rim_isolator_loads {V U : Type*} [Fintype V] [DecidableEq V]
    [Fintype U] [DecidableEq U] {r k : ℕ} {P Q F : SimpleGraph V}
    {H : V → U → Prop} {θ α : ℝ} {x y : V}
    (ψ : OrdinaryIsolatorConfiguration P Q F H k θ α x y → OrdinaryWheel Q F H r → ℝ)
    (hT : 0<Fintype.card (OrdinaryIsolatorConfiguration P Q F H k θ α x y))
    (he : ∀ T a b,ordinaryRimLoad (ψ T) a b=if (SimpleGraph.edge x y).Adj a b then 1 else 0)
    (hv : ∀ T z h,ordinarySpokeLoad (ψ T) z h=
      (if h=T.hub then (1:ℝ) else 0)*(1/2)*(if z=x ∨ z=y then 1 else 0)) :
    (∀ a b,ordinaryRimLoad (finiteSignedAverage ψ) a b=
      if (SimpleGraph.edge x y).Adj a b then 1 else 0) ∧
    (∀ z h,ordinarySpokeLoad (finiteSignedAverage ψ) z h=
      ((1/2:ℝ)*(if z=x ∨ z=y then 1 else 0))*
        (∑ T : OrdinaryIsolatorConfiguration P Q F H k θ α x y,if T.hub=h then (1:ℝ) else 0)/
        (Fintype.card (OrdinaryIsolatorConfiguration P Q F H k θ α x y):ℝ)) := by
  constructor
  · intro a b
    exact finiteSignedAverage_indicator_constant hT ψ
      (fun D => (ordinaryWheelRim D).Adj a b)
      (if (SimpleGraph.edge x y).Adj a b then 1 else 0) (fun T => he T a b)
  · intro z h
    let t (D : OrdinaryWheel Q F H r) : ℝ :=
      if ordinaryWheelHub D=h ∧ z∈(ordinaryWheelRim D).support then 1 else 0
    have htest (T : OrdinaryIsolatorConfiguration P Q F H k θ α x y) :
        (∑ D,ψ T D*t D)=(if h=T.hub then (1:ℝ) else 0)*(1/2)*(if z=x ∨ z=y then 1 else 0) := by
      calc
        _ = ordinarySpokeLoad (ψ T) z h := by
          unfold ordinarySpokeLoad
          apply Finset.sum_congr rfl
          intro D _
          dsimp only [t]
          split_ifs <;> simp
        _ = _ := hv T z h
    calc
      _ = ∑ D,finiteSignedAverage ψ D*t D := by
        unfold ordinarySpokeLoad
        apply Finset.sum_congr rfl
        intro D _
        dsimp only [t]
        split_ifs <;> simp
      _ = (∑ T,∑ D,ψ T D*t D)/(Fintype.card (OrdinaryIsolatorConfiguration P Q F H k θ α x y):ℝ) :=
        finiteSignedAverage_test ψ t
      _ = _ := by
        simp only [htest]
        congr 1
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro T _
        simp only [eq_comm]
        ring

theorem averaged_rim_isolator_coefficient_bound {V U : Type*} [Fintype V] [DecidableEq V]
    [Fintype U] {r k : ℕ} (hr : 3≤r) (hk : r+2≤k)
    {P Q F : SimpleGraph V} {H : V → U → Prop} {θ α : ℝ} {x y : V}
    (ψ : OrdinaryIsolatorConfiguration P Q F H k θ α x y → OrdinaryWheel Q F H r → ℝ)
    (hb : ∀ T D,|ψ T D|≤1)
    (hs : ∀ T D,ψ T D≠0 → ordinaryWheelHub D=T.hub ∧ (ordinaryWheelRim D).support⊆(T.vertices.val:Set V))
    (γ : ℝ) (hγ : 0<γ) (hn : 0<Fintype.card V)
    (hT : γ*(Fintype.card V:ℝ)^(k-1)≤
      (Fintype.card (OrdinaryIsolatorConfiguration P Q F H k θ α x y):ℝ))
    (D : OrdinaryWheel Q F H r) :
    |finiteSignedAverage ψ D|≤1/(γ*(Fintype.card V:ℝ)^
      (((ordinaryWheelRim D).support.toFinset∪{x,y}).card-1)) := by
  let R := (ordinaryWheelRim D).support.toFinset∪{x,y}
  have hc : (ordinaryWheelRim D).support.toFinset.card=r := D.val.1.val.property.support_card
  have hR1 : 1≤R.card := by
    have hx : x∈R := by simp [R]
    exact Finset.card_pos.mpr ⟨x,hx⟩
  have hRk : R.card≤k := by
    have hh := Finset.card_union_le (ordinaryWheelRim D).support.toFinset ({x,y}:Finset V)
    have hp : ({x,y}:Finset V).card≤2 := by
      by_cases hxy : x=y <;> simp [hxy]
    rw [hc] at hh
    dsimp [R]
    omega
  have hcoeff (T : OrdinaryIsolatorConfiguration P Q F H k θ α x y) :
      |ψ T D| ≤ if T.hub=ordinaryWheelHub D ∧ R⊆T.vertices.val then (1:ℝ) else 0 := by
    by_cases hz : ψ T D=0
    · rw [hz,abs_zero]
      split_ifs <;> norm_num
    · have hh := hs T D hz
      have hsub : R⊆T.vertices.val := by
        apply Finset.union_subset
        · intro z hz
          exact hh.2 (Set.mem_toFinset.mp hz)
        · simpa only [Finset.insert_subset_iff,Finset.singleton_subset_iff] using T.endpoints
      rw [if_pos ⟨hh.1.symm,hsub⟩]
      exact hb T D
  have hn' : (0:ℝ)<Fintype.card V := Nat.cast_pos.mpr hn
  have hden : 0<γ*(Fintype.card V:ℝ)^(k-1) := by positivity
  calc
    _ ≤ (∑ T,|ψ T D|)/(Fintype.card (OrdinaryIsolatorConfiguration P Q F H k θ α x y):ℝ) :=
      finiteSignedAverage_abs_le ψ D
    _ ≤ (∑ T,|ψ T D|)/(γ*(Fintype.card V:ℝ)^(k-1)) :=
      div_le_div_of_nonneg_left (Finset.sum_nonneg (fun _ _ => abs_nonneg _)) hden hT
    _ ≤ (Fintype.card V:ℝ)^(k-R.card)/(γ*(Fintype.card V:ℝ)^(k-1)) := by
      apply div_le_div_of_nonneg_right _ hden.le
      exact (Finset.sum_le_sum (fun T _ => hcoeff T)).trans
        (isolator_configuration_hub_root_count (ordinaryWheelHub D) R hRk)
    _ = _ := root_configuration_quotient _ γ hn'.ne' hR1 hRk

theorem averaged_rim_isolator_spoke_bound {V U : Type*} [Fintype V] [DecidableEq V]
    [Fintype U] [DecidableEq U] {r k : ℕ} (hk : 2≤k)
    {P Q F : SimpleGraph V} {H : V → U → Prop} {θ α : ℝ} {x y : V} (hxy : x≠y)
    (ψ : OrdinaryIsolatorConfiguration P Q F H k θ α x y → OrdinaryWheel Q F H r → ℝ)
    (he : ∀ T a b,ordinaryRimLoad (ψ T) a b=if (SimpleGraph.edge x y).Adj a b then 1 else 0)
    (hv : ∀ T z h,ordinarySpokeLoad (ψ T) z h=
      (if h=T.hub then (1:ℝ) else 0)*(1/2)*(if z=x ∨ z=y then 1 else 0))
    (γ : ℝ) (hγ : 0<γ) (hn : 0<Fintype.card V)
    (hT : γ*(Fintype.card V:ℝ)^(k-1)≤
      (Fintype.card (OrdinaryIsolatorConfiguration P Q F H k θ α x y):ℝ))
    (z : V) (h : U) :
    |ordinarySpokeLoad (finiteSignedAverage ψ) z h|≤
      (if z=x ∨ z=y then (1:ℝ) else 0)/(2*γ*Fintype.card V) := by
  have hn' : (0:ℝ)<Fintype.card V := Nat.cast_pos.mpr hn
  have hd : 0<γ*(Fintype.card V:ℝ)^(k-1) := by positivity
  have hpos : 0<Fintype.card (OrdinaryIsolatorConfiguration P Q F H k θ α x y) := by
    exact_mod_cast hd.trans_le hT
  have heq := (averaged_rim_isolator_loads ψ hpos he hv).2 z h
  rw [heq]
  by_cases hz : z=x ∨ z=y
  · rw [if_pos hz,mul_one]
    have hc : 0≤∑ T : OrdinaryIsolatorConfiguration P Q F H k θ α x y,
        if T.hub=h then (1:ℝ) else 0 := Finset.sum_nonneg (fun _ _ => by split_ifs <;> norm_num)
    have hcount : (∑ T : OrdinaryIsolatorConfiguration P Q F H k θ α x y,
        if T.hub=h then (1:ℝ) else 0)≤(Fintype.card V:ℝ)^(k-2) := by
      have hh := isolator_configuration_hub_count (P:=P) (Q:=Q) (F:=F) (H:=H)
        (θ:=θ) (α:=α) h hxy hk
      convert hh using 1
      apply Finset.sum_congr rfl
      intro T _
      split_ifs <;> rfl
    rw [abs_of_nonneg (by positivity)]
    calc
      _ = (1/2:ℝ)*((∑ T : OrdinaryIsolatorConfiguration P Q F H k θ α x y,
          if T.hub=h then (1:ℝ) else 0)/(Fintype.card (OrdinaryIsolatorConfiguration P Q F H k θ α x y):ℝ)) := by ring
      _ ≤ (1/2:ℝ)*((∑ T : OrdinaryIsolatorConfiguration P Q F H k θ α x y,
          if T.hub=h then (1:ℝ) else 0)/(γ*(Fintype.card V:ℝ)^(k-1))) := by
        exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left hc hd hT) (by norm_num)
      _ ≤ (1/2:ℝ)*((Fintype.card V:ℝ)^(k-2)/(γ*(Fintype.card V:ℝ)^(k-1))) := by
        exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right
          hcount hd.le) (by norm_num)
      _ = _ := by
        rw [root_configuration_quotient _ γ hn'.ne' (by norm_num : 1≤2) hk]
        norm_num
        ring
  · simp [hz]

end Oberwolfach

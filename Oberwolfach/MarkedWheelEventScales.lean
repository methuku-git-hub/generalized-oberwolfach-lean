module

public import Oberwolfach.MarkedWheelEventBounds
public import Oberwolfach.OrdinaryRimPairCodegrees

@[expose] public section

/-! Normalising the counts of canonical wheels without changing their
weights. A fixed spoke fixes the hub, while a rim edge does not. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V U E K : Type*} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
  {tail head : E → V} {ktail khead : K → V} {m : ℕ} {π : Equiv.Perm V} {b : ℕ}
  {H₀ Hₖ : V → U → Prop}

theorem marked_wheel_normalized_event (hn : 0<Fintype.card V)
    (w : MarkedWheel tail head ktail khead m π b H₀ Hₖ → ℝ) (B : ℝ) (hB : 0≤B)
    (hw : ∀ W,w W≤B/(Fintype.card V:ℝ)^m)
    (S : Finset V) (hS : 1≤S.card) (hSm : S.card≤m+1) (T : Finset U)
    (P : MarkedWheel tail head ktail khead m π b H₀ Hₖ → Prop)
    (hP : ∀ W,P W → (∀ v∈S,v∈Set.range W.1.val) ∧ W.2.val∈T) :
    (∑ W,if P W then w W else 0)≤
      (T.card:ℝ)*((m:ℝ)+1)^S.card*B/(Fintype.card V:ℝ)^(S.card-1) := by
  have hnR : (0:ℝ)<Fintype.card V := by exact_mod_cast hn
  have hh := marked_wheel_event_weight_bound tail head ktail khead m π b H₀ Hₖ w
    (B/(Fintype.card V:ℝ)^m) (by positivity) hw S T P hP
  have he : (Fintype.card V:ℝ)^(m+1-S.card)*(B/(Fintype.card V:ℝ)^m)=
      B/(Fintype.card V:ℝ)^(S.card-1) := by
    have hm : m=(m+1-S.card)+(S.card-1) := by omega
    conv_lhs => arg 2;arg 2;rw [hm,pow_add]
    field_simp
  calc
    _ ≤ _ := hh
    _ = (T.card:ℝ)*((m:ℝ)+1)^S.card*
      ((Fintype.card V:ℝ)^(m+1-S.card)*(B/(Fintype.card V:ℝ)^m)) := by ring
    _ = _ := by rw [he];ring

theorem marked_wheel_fixed_hub_event (hn : 0<Fintype.card V)
    (w : MarkedWheel tail head ktail khead m π b H₀ Hₖ → ℝ) (B : ℝ) (hB : 0≤B)
    (hw : ∀ W,w W≤B/(Fintype.card V:ℝ)^m)
    (S : Finset V) (hS : 1≤S.card) (hSm : S.card≤m+1) (u : U)
    (P : MarkedWheel tail head ktail khead m π b H₀ Hₖ → Prop)
    (hP : ∀ W,P W → (∀ v∈S,v∈Set.range W.1.val) ∧ W.2.val=u) :
    (∑ W,if P W then w W else 0)≤((m:ℝ)+1)^S.card*B/(Fintype.card V:ℝ)^(S.card-1) := by
  have hh := marked_wheel_normalized_event hn w B hB hw S hS hSm {u} P
    (by intro W h;exact ⟨(hP W h).1,Finset.mem_singleton.mpr (hP W h).2⟩)
  simpa only [Finset.card_singleton,Nat.cast_one,one_mul] using hh

theorem marked_wheel_free_hub_event (hn : 0<Fintype.card V) (hu : Fintype.card U≤Fintype.card V)
    (w : MarkedWheel tail head ktail khead m π b H₀ Hₖ → ℝ) (B : ℝ) (hB : 0≤B)
    (hw : ∀ W,w W≤B/(Fintype.card V:ℝ)^m)
    (S : Finset V) (hS : 2≤S.card) (hSm : S.card≤m+1)
    (P : MarkedWheel tail head ktail khead m π b H₀ Hₖ → Prop)
    (hP : ∀ W,P W → ∀ v∈S,v∈Set.range W.1.val) :
    (∑ W,if P W then w W else 0)≤((m:ℝ)+1)^S.card*B/(Fintype.card V:ℝ)^(S.card-2) := by
  have hnR : (0:ℝ)<Fintype.card V := by exact_mod_cast hn
  have hh := marked_wheel_normalized_event hn w B hB hw S (by omega) hSm Finset.univ P
    (by intro W h;exact ⟨hP W h,Finset.mem_univ _⟩)
  simp only [Finset.card_univ] at hh
  calc
    _ ≤ _ := hh
    _ ≤ (Fintype.card V:ℝ)*((m:ℝ)+1)^S.card*B/(Fintype.card V:ℝ)^(S.card-1) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_right _ hB
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast hu
    _ = _ := by
      have hp : (Fintype.card V:ℝ)^(S.card-1)=(Fintype.card V:ℝ)^(S.card-2)*Fintype.card V := by
        rw [← pow_succ];congr 1;omega
      rw [hp];field_simp

end Oberwolfach

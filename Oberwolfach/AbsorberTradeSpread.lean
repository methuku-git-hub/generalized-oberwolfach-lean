module

public import Oberwolfach.AbsorberFamilyTrades
public import Oberwolfach.PowerCountRatios

@[expose] public section

/-! The signed trade spread follows from labelled absorber counts and
bounded multiplicity of indexed cycles on a given vertex set. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V C T : Type*} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C] [Fintype T] {c : ℕ}

def absorberTradeCountConstant (c J N : ℕ) : ℕ := (2*c+1)*N*c^(2*c)*J^(2*c+1)

theorem labelled_family_trade_spread (hc : 1 ≤ c) (R : C → Finset V)
    (S : T → VertexAbsorberTemplate c) (X : Finset V) (hX : X.card=c) (J : ℕ)
    (hJ : ∀ Y : Finset V,Fintype.card {C₀ : C // R C₀=Y} ≤ J)
    (A : Finset (LabelledAbsorberFamily R S X))
    (a k : ℝ) (ha : 0 < a) (hk : 0 < k) (hn : (Fintype.card V:ℝ)=c*k)
    (hA : a*k^(c*c) ≤ A.card) (C₀ : C) (hC : (R C₀).card=c) :
    let K := (absorberTradeCountConstant c J (Fintype.card T):ℝ)*(c:ℝ)^(c*c)/a
    |labelledFamilyTrade R S X A C₀| ≤ K/k^c+
      (if (R C₀∩X).Nonempty then K/k^(c-1) else 0) := by
  let N := absorberTradeCountConstant c J (Fintype.card T)
  let K := (N:ℝ)*(c:ℝ)^(c*c)/a
  have hc0 : (0:ℝ)<c := by exact_mod_cast (show 0<c by omega)
  have hc1 : (1:ℝ) ≤ c := by exact_mod_cast hc
  have hh : c ≤ c*c := by nlinarith
  have hK : 0 ≤ K := by dsimp [K];positivity
  have step (s : ℕ) (hs : s ≤ c*c)
      (hcount : Fintype.card {D : A // ∃ o,(D.val.2.2 o).val=C₀} ≤ N*Fintype.card V^(c*c-s)) :
      |labelledFamilyTrade R S X A C₀| ≤ K/k^s := by
    have hz : (Fintype.card {D : A // ∃ o,(D.val.2.2 o).val=C₀}:ℝ) ≤ (N:ℝ)*((c:ℝ)*k)^(c*c-s) := by
      rw [← hn]
      exact_mod_cast hcount
    exact (labelled_family_trade_bound R S X A C₀).trans
      (power_count_ratio_bound (c*c) s hs a k c N A.card _ ha hk hc1 (Nat.cast_nonneg _) hA hz)
  change |labelledFamilyTrade R S X A C₀| ≤ K/k^c+(if (R C₀∩X).Nonempty then K/k^(c-1) else 0)
  by_cases hhit : (R C₀∩X).Nonempty
  · rw [if_pos hhit]
    have hcount := labelled_absorber_subfamily_occurrence_count R S X C₀
      (c^(2*c)*Fintype.card V^(c*c-c+1)*J^(2*c+1))
      (fun t o => labelled_absorber_occurrence_general hc R (S t) X hX J hJ o C₀ hC) A
    have hc' : Fintype.card {D : A // ∃ o,(D.val.2.2 o).val=C₀} ≤ N*Fintype.card V^(c*c-(c-1)) := by
      have he : c*c-(c-1)=c*c-c+1 := by omega
      rw [he]
      convert hcount using 1 <;> dsimp [N,absorberTradeCountConstant] <;> ring
    exact (step (c-1) (by omega) hc').trans (le_add_of_nonneg_left (by positivity))
  · rw [if_neg hhit,add_zero]
    have hd : Disjoint (R C₀) X := Finset.disjoint_left.mpr (by
      intro v hv hx;exact hhit ⟨v,Finset.mem_inter.mpr ⟨hv,hx⟩⟩)
    have hcount := labelled_absorber_subfamily_occurrence_count R S X C₀
      (c^(2*c)*Fintype.card V^(c*c-c)*J^(2*c+1))
      (fun t o => labelled_absorber_occurrence_disjoint hc R (S t) X hX J hJ o C₀ hC hd) A
    apply step c hh
    convert hcount using 1 <;> dsimp [N,absorberTradeCountConstant] <;> ring

end Oberwolfach

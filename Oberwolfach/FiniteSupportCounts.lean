module

public import Oberwolfach.FiniteExistentialCounts

@[expose] public section

/-! Counts of fixed objects supported on a selected vertex set.
Comparing two sets is a deterministic finite union bound. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V D : Type*} [Fintype V] [DecidableEq V] [Fintype D]

theorem finite_support_loss_count (F : D → Finset V) (A B : Finset V) (K : ℕ)
    (hK : ∀ v,Fintype.card {d : D // F d⊆A∪B ∧ v∈F d} ≤ K) :
    Fintype.card {d : D // F d⊆A ∧ ¬F d⊆B} ≤ (A\B).card*K := by
  classical
  let Q (v : V) := Finset.univ.filter (fun d : D => F d⊆A∪B ∧ v∈F d)
  have hs : Finset.univ.filter (fun d : D => F d⊆A ∧ ¬F d⊆B) ⊆ (A\B).biUnion Q := by
    intro d hd
    have hd' := (Finset.mem_filter.mp hd).2
    obtain ⟨v,hv,hvB⟩ := Finset.not_subset.mp hd'.2
    exact Finset.mem_biUnion.mpr ⟨v,Finset.mem_sdiff.mpr ⟨hd'.1 hv,hvB⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,hd'.1.trans Finset.subset_union_left,hv⟩⟩
  simp only [Fintype.card_subtype]
  calc
    _ ≤ ((A\B).biUnion Q).card := Finset.card_le_card hs
    _ ≤ ∑ v∈A\B,(Q v).card := Finset.card_biUnion_le
    _ ≤ ∑ _v∈A\B,K := Finset.sum_le_sum (fun v _ => by simpa only [Fintype.card_subtype,Q] using hK v)
    _ = _ := by simp

theorem finite_support_count_difference (F : D → Finset V) (A B : Finset V) (K : ℕ)
    (hK : ∀ v,Fintype.card {d : D // F d⊆A∪B ∧ v∈F d} ≤ K) :
    |(Fintype.card {d : D // F d⊆A}:ℝ)-Fintype.card {d : D // F d⊆B}| ≤
      ((A\B).card+(B\A).card:ℕ)*(K:ℝ) := by
  let SA := Finset.univ.filter (fun d : D => F d⊆A)
  let SB := Finset.univ.filter (fun d : D => F d⊆B)
  have ha : (SA\SB).card ≤ (A\B).card*K := by
    have hh := finite_support_loss_count F A B K hK
    have he : SA\SB=Finset.univ.filter (fun d : D => F d⊆A ∧ ¬F d⊆B) := by ext d;simp [SA,SB]
    simpa only [Fintype.card_subtype,← he] using hh
  have hb : (SB\SA).card ≤ (B\A).card*K := by
    have hh := finite_support_loss_count F B A K (fun v => by simpa only [Finset.union_comm] using hK v)
    have he : SB\SA=Finset.univ.filter (fun d : D => F d⊆B ∧ ¬F d⊆A) := by ext d;simp [SA,SB]
    simpa only [Fintype.card_subtype,← he] using hh
  have h₁ : SA.card ≤ SB.card+(A\B).card*K := by
    have hh := Finset.card_le_card_sdiff_add_card (s:=SA) (t:=SB)
    omega
  have h₂ : SB.card ≤ SA.card+(B\A).card*K := by
    have hh := Finset.card_le_card_sdiff_add_card (s:=SB) (t:=SA)
    omega
  have h₁r : (SA.card:ℝ) ≤ SB.card+(A\B).card*K := by exact_mod_cast h₁
  have h₂r : (SB.card:ℝ) ≤ SA.card+(B\A).card*K := by exact_mod_cast h₂
  have hn₁ : 0 ≤ ((A\B).card:ℝ)*K := by positivity
  have hn₂ : 0 ≤ ((B\A).card:ℝ)*K := by positivity
  simp only [Fintype.card_subtype]
  change |(SA.card:ℝ)-SB.card| ≤ _
  push_cast
  apply abs_le.mpr
  constructor <;> nlinarith

end Oberwolfach

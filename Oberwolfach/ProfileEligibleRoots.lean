module

public import Oberwolfach.ProfileRootCounts
public import Oberwolfach.EligibleCommonEvents

@[expose] public section

/-! The number of profile roots inside one sampled set depends only on
that set's size. Weighting conditional failure probabilities by root
inclusion probabilities therefore gives a common event without an
ambient-order factor. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I : Type*} [Fintype I] [DecidableEq I]
    {V : I → Type*} [∀ i,Fintype (V i)] [∀ i,DecidableEq (V i)]

theorem profile_roots_inside_card (a : I → ℕ) (c : ℕ) (ha : ∑ i,a i=c)
    (Y : Finset (Σ i,V i)) :
    Fintype.card {ρ : ∀ i,FixedSubset (V i) (a i) // profileRootSet ρ⊆Y} ≤ Y.card^c := by
  let A := {ρ : ∀ i,FixedSubset (V i) (a i) // profileRootSet ρ⊆Y}
  let B := {X : Finset (Σ i,V i) // X∈Y.powersetCard c}
  let f (ρ : A) : B := ⟨profileRootSet ρ.val,Finset.mem_powersetCard.mpr
    ⟨ρ.property,(profileRootSet_card ρ.val).trans ha⟩⟩
  have hi : Function.Injective f := by
    intro ρ τ he
    apply Subtype.ext
    exact profileRootSet_injective a (congrArg (fun x : B => x.val) he)
  have hh := Fintype.card_le_of_injective f hi
  have hb : Fintype.card B=Y.card.choose c := by simp only [B,Fintype.card_coe,Finset.card_powersetCard]
  rw [hb] at hh
  exact hh.trans (Nat.choose_le_pow _ _)

theorem profile_roots_common_event {Ω : Type*} [Fintype Ω]
    (μ : FiniteLaw Ω) (a : I → ℕ) (c : ℕ) (ha : ∑ i,a i=c)
    (Y : Ω → Finset (Σ i,V i)) (M : ℕ) (hM : ∀ ω,(Y ω).card ≤ M)
    (Bad : (∀ i,FixedSubset (V i) (a i)) → Ω → Prop) (ε : ℝ) (hε : 0 ≤ ε)
    (h : ∀ ρ,μ.probability (fun ω => profileRootSet ρ⊆Y ω ∧ Bad ρ ω) ≤
      ε*μ.probability (fun ω => profileRootSet ρ⊆Y ω)) :
    1-ε*(M:ℝ)^c ≤ μ.probability (fun ω => ∀ ρ,profileRootSet ρ⊆Y ω → ¬Bad ρ ω) := by
  have hb (ω : Ω) :
      ((Finset.univ.filter (fun ρ : ∀ i,FixedSubset (V i) (a i) => profileRootSet ρ⊆Y ω)).card:ℝ) ≤ (M:ℝ)^c := by
    have hh := (profile_roots_inside_card a c ha (Y ω)).trans (Nat.pow_le_pow_left (hM ω) c)
    simp only [Fintype.card_subtype] at hh
    exact_mod_cast hh
  have hh := finiteLaw_eligible_common_event μ Finset.univ
    (fun ρ ω => profileRootSet ρ⊆Y ω) Bad ((M:ℝ)^c) ε hε (fun ω => by convert hb ω using 1 <;> congr!) (fun ρ _ => h ρ)
  simpa only [Finset.mem_univ,forall_const] using hh

end Oberwolfach

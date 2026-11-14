module

public import Oberwolfach.CoinConflictCertificates
public import Oberwolfach.NibbleColourCounts
public import Oberwolfach.BoundedCertificateConcentration

@[expose] public section

/-! Concentration bounds for the actual uncoloured-vertex and
assignment/rejection counts in one tentative-colouring round. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem coinConflict_expectation
    {V C : Type*} [Fintype V] [Fintype C]
    (G : SimpleGraph V) (T : Finset V) (μ : V → FiniteLaw (C×Bool)) (ρ : ℝ)
    (hρ : ∀ v∈T,(FiniteLaw.pi μ).probability (fun σ=>coinColourSurvives G σ v)=ρ) :
    (FiniteLaw.pi μ).expectation (fun σ=>((coinConflictSet G T σ).card : ℝ))=
      (T.card : ℝ)*(1-ρ) := by
  have hp (v : V) (hv : v∈T) :
      (FiniteLaw.pi μ).probability (fun σ=>¬coinColourSurvives G σ v)=1-ρ := by
    have h := finiteLaw_probability_compl (FiniteLaw.pi μ) (fun σ=>coinColourSurvives G σ v)
    rw [hρ v hv] at h
    linarith
  calc
    _ = ∑ v∈T,(FiniteLaw.pi μ).probability (fun σ=>¬coinColourSurvives G σ v) := by
      convert finiteLaw_expectation_count (FiniteLaw.pi μ) T
        (fun v σ=>¬coinColourSurvives G σ v) using 1
      apply congrArg (FiniteLaw.pi μ).expectation
      funext σ
      apply congrArg (fun n : ℕ=>(n : ℝ))
      apply congrArg Finset.card
      ext v
      simp [coinConflictSet]
    _ = ∑ _v∈T,(1-ρ) := Finset.sum_congr rfl hp
    _ = _ := by simp;ring

theorem coinConflict_concentration
    {V C : Type*} [Fintype V] [Fintype C]
    (G : SimpleGraph V) (T : Finset V) (hT : T.Nonempty)
    (hclique : ∀ u∈T,∀ v∈T,u≠v → G.Adj u v)
    (μ : V → FiniteLaw (C×Bool)) {t : ℝ} (ht : 0≤t)
    (hsmall : (T.card : ℝ)*(4*Real.exp (-t^2/(24*(T.card : ℝ))))≤t) :
    (FiniteLaw.pi μ).probability
      (fun σ=>3*t≤|((coinConflictSet G T σ).card : ℝ)-
        (FiniteLaw.pi μ).expectation (fun σ=>((coinConflictSet G T σ).card : ℝ))|)≤
      4*Real.exp (-t^2/(24*(T.card : ℝ))) := by
  classical
  have hpos : (0 : ℝ)<T.card := by exact_mod_cast hT.card_pos
  have he : (4 : ℝ)*2*(3*(T.card : ℝ))=24*(T.card : ℝ) := by ring
  have hs : (T.card : ℝ)*(4*Real.exp (-t^2/(4*2*(3*(T.card : ℝ)))))≤t := by
    rw [he]
    exact hsmall
  have hh := finiteLaw_bounded_certificate_tail μ
    (fun σ=>((coinConflictSet G T σ).card : ℝ)) (by norm_num : (0 : ℝ)<2)
    (show 0<3*(T.card : ℝ) by positivity) ht (coinConflict_certificate G T hclique)
    (fun σ=>⟨Nat.cast_nonneg _,by
      exact_mod_cast (Finset.card_le_card
        (show coinConflictSet G T σ⊆T from Finset.filter_subset _ _))⟩) hs
  simpa only [he] using hh

theorem nibbleColourCount_concentration
    {V C J : Type*} [Fintype V] [Fintype C] [Fintype J]
    (G : SimpleGraph V) (Q : Finset J) (hQ : Q.Nonempty) (T : J → Finset V)
    (L : Finset C) (hL : L.Nonempty) (a b : ℕ) (μ : V → FiniteLaw (C×Bool))
    {t : ℝ} (ht : 0≤t)
    (hsmall : (L.card : ℝ)*
      (4*Real.exp (-t^2/(12*(Q.card : ℝ)*(L.card : ℝ))))≤t) :
    (FiniteLaw.pi μ).probability (fun σ=>
      3*t≤|nibbleColourCount G Q T L a b σ-
        (FiniteLaw.pi μ).expectation (nibbleColourCount G Q T L a b)|)≤
      4*Real.exp (-t^2/(12*(Q.card : ℝ)*(L.card : ℝ))) := by
  classical
  have hQpos : (0 : ℝ)<Q.card := by exact_mod_cast hQ.card_pos
  have hLpos : (0 : ℝ)<L.card := by exact_mod_cast hL.card_pos
  have he : (4 : ℝ)*1*((3*(Q.card : ℝ))*(L.card : ℝ))=
      12*(Q.card : ℝ)*(L.card : ℝ) := by ring
  have hs : (L.card : ℝ)*
      (4*Real.exp (-t^2/(4*1*((3*(Q.card : ℝ))*(L.card : ℝ)))))≤t := by
    rw [he]
    exact hsmall
  have hh := finiteLaw_bounded_certificate_tail μ (nibbleColourCount G Q T L a b)
    (by norm_num : (0 : ℝ)<1) (show 0<(3*(Q.card : ℝ))*(L.card : ℝ) by positivity)
    ht (nibbleColourCount_certificate G Q T L a b)
    (fun σ=>⟨Nat.cast_nonneg _,by
      unfold nibbleColourCount
      exact_mod_cast (Finset.card_le_card (show L.filter
        (fun c=>a≤(assignedSetIndices Q T σ c).card ∧
          b≤(rejectedSetIndices G Q T σ c).card)⊆L from Finset.filter_subset _ _))⟩) hs
  simpa only [he] using hh

end Oberwolfach

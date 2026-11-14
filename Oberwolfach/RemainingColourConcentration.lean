module

public import Oberwolfach.RemainingColourDegrees
public import Oberwolfach.BoundedCertificateConcentration
public import Oberwolfach.FiniteLinearTails

@[expose] public section

/-! Concentration of the actual colour degrees after a tentative round.
No independence between survival events or overlapping cliques is used. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem neighbourColourCount_concentration
    {V C J : Type*} [Fintype V] [Fintype C]
    (G : SimpleGraph V) (U : Finset V) (hU : U.Nonempty)
    (hclique : ∀ u∈U,∀ v∈U,u≠v → G.Adj u v)
    (Q : V → Finset J) (T : J → Finset V) {k d : ℕ}
    (hQ : ∀ v∈U,(Q v).card≤k)
    (hlocal : ∀ (w : V) (S : Finset V),(∀ v∈S,G.Adj w v) →
      (∀ u∈S,∀ v∈S,u≠v → ¬G.Adj u v) → S.card≤k)
    (hinc : ∀ w,(U.filter (fun v=>∃ j∈Q v,w∈T j)).card≤d)
    (c : C) (a b : ℕ) (μ : V → FiniteLaw (C×Bool)) {t : ℝ} (ht : 0≤t)
    (hsmall : (U.card : ℝ)*(4*Real.exp
      (-t^2/(4*(2+(((k+3)*d : ℕ) : ℝ))*(3+((3*k : ℕ) : ℝ))*(U.card : ℝ))))≤t) :
    (FiniteLaw.pi μ).probability (fun σ=>3*t≤|neighbourColourCount G U Q T c a b σ-
      (FiniteLaw.pi μ).expectation (neighbourColourCount G U Q T c a b)|)≤
      4*Real.exp (-t^2/(4*(2+(((k+3)*d : ℕ) : ℝ))*(3+((3*k : ℕ) : ℝ))*(U.card : ℝ))) := by
  classical
  have hpos : (0 : ℝ)<U.card := by exact_mod_cast hU.card_pos
  have he : (4 : ℝ)*(2+(((k+3)*d : ℕ) : ℝ))*
      ((3+((3*k : ℕ) : ℝ))*(U.card : ℝ))=
      4*(2+(((k+3)*d : ℕ) : ℝ))*(3+((3*k : ℕ) : ℝ))*(U.card : ℝ) := by ring
  have hs : (U.card : ℝ)*(4*Real.exp
      (-t^2/(4*(2+(((k+3)*d : ℕ) : ℝ))*((3+((3*k : ℕ) : ℝ))*(U.card : ℝ)))))≤t := by
    rw [he]
    exact hsmall
  have hh := finiteLaw_bounded_certificate_tail μ (neighbourColourCount G U Q T c a b)
    (show 0<(2 : ℝ)+(((k+3)*d : ℕ) : ℝ) by positivity)
    (show 0<((3 : ℝ)+((3*k : ℕ) : ℝ))*(U.card : ℝ) by positivity) ht
    (neighbourColourCount_certificate G U hclique Q T hQ hlocal hinc c a b)
    (fun σ=>⟨Nat.cast_nonneg _,by
      unfold neighbourColourCount
      exact_mod_cast (Finset.card_le_card (show filteredCoinConflictSet G U
        (neighbourColourPredicate G Q T c a b) σ⊆U from
          (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)))⟩) hs
  simpa only [he] using hh

theorem remainingColourVertices_concentration
    {V C J : Type*} [Fintype V] [Fintype C]
    (G : SimpleGraph V) (U : Finset V) (hU : U.Nonempty)
    (hclique : ∀ u∈U,∀ v∈U,u≠v → G.Adj u v)
    (Q : V → Finset J) (T : J → Finset V) {k d : ℕ}
    (hQ : ∀ v∈U,(Q v).card≤k)
    (hT : ∀ v∈U,∀ j∈Q v,∀ u∈T j,∀ w∈T j,u≠w → G.Adj u w)
    (hlocal : ∀ (w : V) (S : Finset V),(∀ v∈S,G.Adj w v) →
      (∀ u∈S,∀ v∈S,u≠v → ¬G.Adj u v) → S.card≤k)
    (hinc : ∀ w,(U.filter (fun v=>∃ j∈Q v,w∈T j)).card≤d)
    (c : C) (μ : V → FiniteLaw (C×Bool)) {t : ℝ} (ht : 0≤t)
    (hsmall : (U.card : ℝ)*(4*Real.exp
      (-t^2/(4*(2+(((k+3)*d : ℕ) : ℝ))*(3+((3*k : ℕ) : ℝ))*(U.card : ℝ))))≤t) :
    (FiniteLaw.pi μ).probability (fun σ=>6*((k : ℝ)+1)*t≤
      |((remainingColourVertices G U Q T c σ).card : ℝ)-
        (FiniteLaw.pi μ).expectation (fun σ=>((remainingColourVertices G U Q T c σ).card : ℝ))|)≤
      8*((k : ℝ)+1)*Real.exp
        (-t^2/(4*(2+(((k+3)*d : ℕ) : ℝ))*(3+((3*k : ℕ) : ℝ))*(U.card : ℝ))) := by
  classical
  let ν := FiniteLaw.pi μ
  let tests : Finset (ℕ×Bool) := (Finset.range (k+1))×ˢFinset.univ
  let b : ℕ×Bool → ℝ := fun p=>if p.2 then -1 else 1
  let X : ℕ×Bool → (V → C×Bool) → ℝ := fun p σ=>
    if p.2 then neighbourColourCount G U Q T c (p.1+1) p.1 σ
      else neighbourColourCount G U Q T c p.1 p.1 σ
  let Y : (V → C×Bool) → ℝ := fun σ=>∑ p∈tests,b p*X p σ
  have hY (σ : V → C×Bool) : Y σ=((remainingColourVertices G U Q T c σ).card : ℝ) := by
    calc
      _ = ∑ a∈Finset.range (k+1),
          (neighbourColourCount G U Q T c a a σ-neighbourColourCount G U Q T c (a+1) a σ) := by
        dsimp only [Y,tests]
        rw [Finset.sum_product]
        apply Finset.sum_congr rfl
        intro a _
        simp only [Fintype.sum_bool,b,X,Bool.false_eq_true,ite_false,ite_true]
        ring
      _ = _ := (remainingColourVertices_card G U Q T hQ hT σ c).symm
  have hnonempty : tests.Nonempty := ⟨(0,false),by simp [tests]⟩
  have hb (p : ℕ×Bool) (_hp : p∈tests) : |b p|≤1 := by
    cases h : p.2 <;> norm_num [b,h]
  let p₀ := 4*Real.exp
    (-t^2/(4*(2+(((k+3)*d : ℕ) : ℝ))*(3+((3*k : ℕ) : ℝ))*(U.card : ℝ)))
  have hp (p : ℕ×Bool) (_hp : p∈tests) :
      ν.probability (fun σ=>3*t≤|X p σ-ν.expectation (X p)|)≤p₀ := by
    cases h : p.2
    · simpa only [X,h,Bool.false_eq_true,ite_false] using
        neighbourColourCount_concentration G U hU hclique Q T hQ hlocal hinc c p.1 p.1 μ ht hsmall
    · simpa only [X,h,ite_true] using
        neighbourColourCount_concentration G U hU hclique Q T hQ hlocal hinc c (p.1+1) p.1 μ ht hsmall
  have htail := finiteLaw_linear_tail ν tests hnonempty b X hb (3*t) (fun _=>p₀) hp
  have hcard : tests.card=2*(k+1) := by simp [tests,mul_comm]
  have hYfun : Y=(fun σ=>((remainingColourVertices G U Q T c σ).card : ℝ)) := funext hY
  change ν.probability (fun σ=>(tests.card : ℝ)*(3*t)≤|Y σ-ν.expectation Y|)≤
    ∑ _p∈tests,p₀ at htail
  rw [hYfun] at htail
  simp only [Finset.sum_const,nsmul_eq_mul,hcard,Nat.cast_mul,Nat.cast_add,
    Nat.cast_ofNat,Nat.cast_one] at htail
  have hleft : ((2 : ℝ)*((k : ℝ)+1))*(3*t)=6*((k : ℝ)+1)*t := by ring
  have hright : ((2 : ℝ)*((k : ℝ)+1))*p₀=
      8*((k : ℝ)+1)*Real.exp
        (-t^2/(4*(2+(((k+3)*d : ℕ) : ℝ))*(3+((3*k : ℕ) : ℝ))*(U.card : ℝ))) := by
    dsimp [p₀]
    ring
  rw [hleft,hright] at htail
  exact htail

end Oberwolfach

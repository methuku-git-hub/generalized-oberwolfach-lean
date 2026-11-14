module

public import Oberwolfach.NibbleCountConcentration
public import Oberwolfach.NibbleAvailableColours
public import Oberwolfach.FiniteLinearTails

@[expose] public section

/-! Mean-centred concentration for the number of available colours,
derived from the exact assignment/rejection identity. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem nibbleAvailableColours_concentration
    {V C J : Type*} [Fintype V] [Fintype C] [Fintype J]
    (G : SimpleGraph V) (Q : Finset J) (hQ : Q.Nonempty) (T : J → Finset V)
    (hT : ∀ j∈Q,∀ u∈T j,∀ v∈T j,u≠v → G.Adj u v)
    (L : Finset C) (hL : L.Nonempty) (μ : V → FiniteLaw (C×Bool))
    {t : ℝ} (ht : 0≤t)
    (hsmall : (L.card : ℝ)*
      (4*Real.exp (-t^2/(12*(Q.card : ℝ)*(L.card : ℝ))))≤t) :
    (FiniteLaw.pi μ).probability (fun σ=>
      6*((Q.card : ℝ)+1)*t≤|((nibbleAvailableColours G Q T L σ).card : ℝ)-
        (FiniteLaw.pi μ).expectation (fun σ=>((nibbleAvailableColours G Q T L σ).card : ℝ))|)≤
      8*((Q.card : ℝ)+1)*Real.exp (-t^2/(12*(Q.card : ℝ)*(L.card : ℝ))) := by
  classical
  let ν := FiniteLaw.pi μ
  let tests : Finset (ℕ×Bool) := (Finset.range (Q.card+1))×ˢFinset.univ
  let b : ℕ×Bool → ℝ := fun p=>if p.2 then -1 else 1
  let X : ℕ×Bool → (V → C×Bool) → ℝ := fun p σ=>
    if p.2 then nibbleColourCount G Q T L (p.1+1) p.1 σ
      else nibbleColourCount G Q T L p.1 p.1 σ
  let Y : (V → C×Bool) → ℝ := fun σ=>∑ p∈tests,b p*X p σ
  have hY (σ : V → C×Bool) : Y σ=((nibbleAvailableColours G Q T L σ).card : ℝ) := by
    calc
      _ = ∑ a∈Finset.range (Q.card+1),
          (nibbleColourCount G Q T L a a σ-nibbleColourCount G Q T L (a+1) a σ) := by
        dsimp only [Y,tests]
        rw [Finset.sum_product]
        apply Finset.sum_congr rfl
        intro a _
        simp only [Fintype.sum_bool,b,X,Bool.false_eq_true,ite_false,ite_true]
        ring
      _ = _ := (nibbleAvailableColours_card G Q T hT L σ).symm
  have hnonempty : tests.Nonempty := ⟨(0,false),by simp [tests]⟩
  have hb (p : ℕ×Bool) (_hp : p∈tests) : |b p|≤1 := by
    cases h : p.2 <;> norm_num [b,h]
  let p₀ := 4*Real.exp (-t^2/(12*(Q.card : ℝ)*(L.card : ℝ)))
  have hp (p : ℕ×Bool) (_hp : p∈tests) :
      ν.probability (fun σ=>3*t≤|X p σ-ν.expectation (X p)|)≤p₀ := by
    cases h : p.2
    · simpa only [X,h,Bool.false_eq_true,ite_false] using
        nibbleColourCount_concentration G Q hQ T L hL p.1 p.1 μ ht hsmall
    · simpa only [X,h,ite_true] using
        nibbleColourCount_concentration G Q hQ T L hL (p.1+1) p.1 μ ht hsmall
  have htail := finiteLaw_linear_tail ν tests hnonempty b X hb (3*t) (fun _=>p₀) hp
  have hcard : tests.card=2*(Q.card+1) := by simp [tests,mul_comm]
  have hYfun : Y=(fun σ=>((nibbleAvailableColours G Q T L σ).card : ℝ)) := funext hY
  change ν.probability (fun σ=>(tests.card : ℝ)*(3*t)≤|Y σ-ν.expectation Y|)≤
    ∑ _p∈tests,p₀ at htail
  rw [hYfun] at htail
  simp only [Finset.sum_const,nsmul_eq_mul,hcard,Nat.cast_mul,Nat.cast_add,
    Nat.cast_ofNat,Nat.cast_one] at htail
  have hleft : ((2 : ℝ)*((Q.card : ℝ)+1))*(3*t)=6*((Q.card : ℝ)+1)*t := by ring
  have hright : ((2 : ℝ)*((Q.card : ℝ)+1))*p₀=
      8*((Q.card : ℝ)+1)*Real.exp (-t^2/(12*(Q.card : ℝ)*(L.card : ℝ))) := by
    dsimp [p₀]
    ring
  rw [hleft,hright] at htail
  exact htail

end Oberwolfach

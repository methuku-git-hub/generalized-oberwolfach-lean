module

public import Oberwolfach.RawMarkedNeighbourhoodTails

@[expose] public section

/-! One raw event controls hub degrees and every intersection of at most h
distinct hub neighbourhoods. The vertex domain and both spoke marginals
are fixed before the interval variables are sampled. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V U Γ Color : Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [DecidableEq V] [DecidableEq U]

theorem rawMarkedSmallIntersections_event
    (π : Equiv.Perm V) (d : ℕ) (hd : 2≤d)
    (q : U→Γ→ℝ) (hq : ∀ u g,0≤q u g) (hQ : ∀ u,∑ g,q u g≤1/8)
    (s : U→Color→ℝ) (hs : ∀ u j,0≤s u j)
    (hS : ∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
    (hnoshort : ∀ x l,0<l → l<2*d+1 → (π^l) x≠x)
    (hn : 0<Fintype.card V) (hm : 1≤Fintype.card U)
    (g : Γ) (j : Color) (s₀ t₀ : ℝ) (hg : ∀ u,q u g=t₀) (hj : ∀ u,s u j=s₀)
    (h : ℕ) (hh : 0<h) (t : ℝ) (ht : 0<t) :
    1-4*h*(Fintype.card U:ℝ)^h*Real.exp (-2*t^2/((4*(d:ℝ)+3)^2*((h:ℝ)*Fintype.card V)))≤
    (FiniteLaw.pi (rawIntervalFamilyLaw (V:=V) d hd q hq hQ s hs hS)).probability
      (fun σ=>∀ k : ℕ,1≤k → k≤h → ∀ (b : Bool) (u : Fin k→U),Function.Injective u →
        |((Finset.univ.filter (fun v=>∀ i,rawMarkedSpokes π d σ g j b v (u i))).card:ℝ)-
          (if b then t₀ else s₀)^k*Fintype.card V|<t) := by
  let μ := FiniteLaw.pi (rawIntervalFamilyLaw (V:=V) d hd q hq hQ s hs hS)
  let Good (i : Fin h) (σ : RawIntervalFamilyOutcome V U Γ Color) :=
    ∀ (b : Bool) (u : Fin (i.val+1)→U),Function.Injective u →
      |((Finset.univ.filter (fun v=>∀ j',rawMarkedSpokes π d σ g j b v (u j'))).card:ℝ)-
        (if b then t₀ else s₀)^(i.val+1)*Fintype.card V|<t
  let f : ℝ := 4*(Fintype.card U:ℝ)^h*Real.exp (-2*t^2/((4*(d:ℝ)+3)^2*((h:ℝ)*Fintype.card V)))
  have hnR : (0:ℝ)<Fintype.card V := by exact_mod_cast hn
  have hmR : (1:ℝ)≤Fintype.card U := by exact_mod_cast hm
  have hhR : (0:ℝ)<h := by exact_mod_cast hh
  have hGood (i : Fin h) : 1-f≤μ.probability (Good i) := by
    have hi : i.val+1≤h := by omega
    have hiR : (0:ℝ)< (i.val:ℝ)+1 := by positivity
    have hiR' : (i.val:ℝ)+1≤h := by exact_mod_cast hi
    have hiP : (Fintype.card U:ℝ)^(i.val+1)≤(Fintype.card U:ℝ)^h := by
      exact pow_le_pow_right₀ hmR hi
    have hiE : Real.exp (-2*t^2/((4*(d:ℝ)+3)^2*(((i.val:ℝ)+1)*Fintype.card V)))≤
        Real.exp (-2*t^2/((4*(d:ℝ)+3)^2*((h:ℝ)*Fintype.card V))) := by
      apply Real.exp_le_exp.mpr
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      apply mul_le_mul_of_nonpos_left _ (by nlinarith only [sq_nonneg t])
      gcongr
    have hb : 4*(Fintype.card U:ℝ)^(i.val+1)*
        Real.exp (-2*t^2/((4*(d:ℝ)+3)^2*((i.val+1:ℕ)*Fintype.card V)))≤f := by
      simp only [Nat.cast_add,Nat.cast_one]
      exact mul_le_mul (mul_le_mul_of_nonneg_left hiP (by norm_num)) hiE (by positivity) (by positivity)
    exact (sub_le_sub_left hb 1).trans
      (rawMarkedNeighbourhood_exponential_event π d hd q hq hQ s hs hS hnoshort hn
        g j s₀ t₀ hg hj (i.val+1) (by omega) t ht)
  have hjoint := finiteLaw_common_event_lower μ (Finset.univ : Finset (Fin h))
    (fun i σ=>¬Good i σ) (fun _=>f) (by
      intro i _
      have hc := finiteLaw_probability_compl μ (Good i)
      linarith only [hc,hGood i])
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
    Finset.mem_univ,true_implies,not_not] at hjoint
  have he : 1-(h:ℝ)*f=1-4*h*(Fintype.card U:ℝ)^h*
      Real.exp (-2*t^2/((4*(d:ℝ)+3)^2*((h:ℝ)*Fintype.card V))) := by dsimp [f];ring
  rw [he] at hjoint
  apply hjoint.trans
  apply finiteLaw_probability_mono
  intro σ hσ k hk1 hkh
  cases k with
  | zero=>omega
  | succ k=>exact hσ ⟨k,by omega⟩

end Oberwolfach

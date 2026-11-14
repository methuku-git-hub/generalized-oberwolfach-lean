module

public import Oberwolfach.ColouredTwoPaths
public import Oberwolfach.AsymptoticMargins

@[expose] public section

/-! One independent edge-colouring simultaneously controls all colour degrees
and all ordered two-path candidate sets used in the divisibility repair. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
universe u
attribute [local instance] Classical.propDecidable

theorem divisibility_colour_common_event {V : Type*} [Fintype V] [DecidableEq V]
    {R : ℕ} (G : SimpleGraph V) (ρ : Fin R → ℝ) (hρ : ∀ a,0≤ρ a)
    (hsum : ∑ a,ρ a=1) (b : Fin R) (η : ℝ) (hη : 0≤η) (hn : 0<Fintype.card V) :
    1-4*R*(Fintype.card V:ℝ)^2*Real.exp (-η^2*Fintype.card V)≤
      (FiniteLaw.pi (fun _ : Sym2 V => FiniteLaw.categorical ρ hρ hsum)).probability
        (fun σ => (∀ a v,|(sampledColourDegree G σ a v:ℝ)-ρ a*G.degree v|<η*Fintype.card V) ∧
          (∀ a u v,u≠v → |(colouredTwoPathCount G σ u v a b:ℝ)-
            ((G.neighborFinset u∩G.neighborFinset v).card:ℝ)*ρ a*ρ b|<η*Fintype.card V)) := by
  let n : ℝ := Fintype.card V
  have hnp : 0<n := Nat.cast_pos.mpr hn
  have hn1 : 1≤n := by
    dsimp only [n]
    exact_mod_cast (show 1≤Fintype.card V by omega)
  let μ := FiniteLaw.pi (fun _ : Sym2 V => FiniteLaw.categorical ρ hρ hsum)
  let J := (Fin R×V)⊕(Fin R×{p : V×V // p.1≠p.2})
  let X (j : J) (σ : Sym2 V → Fin R) : ℝ :=
    match j with
    | Sum.inl (a,v) => (sampledColourDegree G σ a v:ℝ)-ρ a*G.degree v
    | Sum.inr (a,p) => (colouredTwoPathCount G σ p.1.1 p.1.2 a b:ℝ)-
        ((G.neighborFinset p.1.1∩G.neighborFinset p.1.2).card:ℝ)*ρ a*ρ b
  let B := 2*Real.exp (-η^2*n)
  have hbad (j : J) : μ.probability (fun σ => η*n≤|X j σ|)≤B := by
    rcases j with ⟨a,v⟩ | ⟨a,p⟩
    · have hh := sampledColourDegree_tail G ρ hρ hsum a v (t:=η*n) (by positivity)
      have he : -2*(η*n)^2/n = -2*η^2*n := by field_simp <;> ring
      change μ.probability (fun σ => η*n≤|X (Sum.inl (a,v)) σ|)≤2*Real.exp (-2*(η*n)^2/n) at hh
      rw [he] at hh
      apply hh.trans
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Real.exp_le_exp.mpr
      have hh0 : 0≤η^2*n := by positivity
      nlinarith
    · have hh := colouredTwoPathCount_tail G ρ hρ hsum p.1.1 p.1.2 p.2 a b (t:=η*n) (by positivity)
      have he : -(η*n)^2/n = -η^2*n := by field_simp <;> ring
      change μ.probability (fun σ => η*n≤|X (Sum.inr (a,p)) σ|)≤2*Real.exp (-(η*n)^2/n) at hh
      rw [he] at hh
      exact hh
  have hcard : (Fintype.card J:ℝ)≤2*R*n^2 := by
    have hpair : (Fintype.card {p : V×V // p.1≠p.2}:ℝ)≤n^2 := by
      have hh := Fintype.card_subtype_le (fun p : V×V => p.1≠p.2)
      simpa only [Fintype.card_prod,Nat.cast_mul,n,pow_two] using (Nat.cast_le (α:=ℝ)).mpr hh
    have hR : (0:ℝ)≤R := Nat.cast_nonneg _
    have hh := mul_le_mul_of_nonneg_left hpair hR
    simp only [J,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin,Nat.cast_add,Nat.cast_mul]
    change (R:ℝ)*n+R*(Fintype.card {p : V×V // p.1≠p.2}:ℝ)≤2*R*n^2
    have hh2 := mul_le_mul_of_nonneg_left (show n≤n^2 by nlinarith) hR
    nlinarith
  have hbound : (∑ _ : J,B)≤4*R*n^2*Real.exp (-η^2*n) := by
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    have hh := mul_le_mul_of_nonneg_right hcard (show 0≤B by dsimp [B];positivity)
    dsimp only [B] at *
    nlinarith
  have hh := finiteLaw_common_event_lower μ Finset.univ (fun j σ => η*n≤|X j σ|)
    (fun _ => B) (fun j _ => hbad j)
  apply (sub_le_sub_left hbound 1).trans (hh.trans _)
  apply finiteLaw_probability_mono
  intro σ hσ
  constructor
  · intro a v
    exact not_le.mp (hσ (Sum.inl (a,v)) (Finset.mem_univ _))
  · intro a u v huv
    exact not_le.mp (hσ (Sum.inr (a,⟨(u,v),huv⟩)) (Finset.mem_univ _))

theorem divisibility_colour_sample (R : ℕ) (η : ℝ) (hη : 0<η) :
    ∃ N : ℕ,∀ (V : Type u) [Fintype V] [DecidableEq V],N≤Fintype.card V →
    ∀ (G : SimpleGraph V) (ρ : Fin R → ℝ) (hρ : ∀ a,0≤ρ a) (hsum : ∑ a,ρ a=1)
      (b : Fin R),∃ σ : Sym2 V → Fin R,
      (∀ a v,|(sampledColourDegree G σ a v:ℝ)-ρ a*G.degree v|<η*Fintype.card V) ∧
      (∀ a u v,u≠v → |(colouredTwoPathCount G σ u v a b:ℝ)-
        ((G.neighborFinset u∩G.neighborFinset v).card:ℝ)*ρ a*ρ b|<η*Fintype.card V) := by
  obtain ⟨N,hN⟩ := eventually_stretchedExp_le_inv_pow (4*R) 2 (c:=η^2) (p:=1)
    (sq_pos_of_pos hη) (by norm_num) 1
  refine ⟨max N 2,?_⟩
  intro V instV instDec hn G ρ hρ hsum b
  have hn2 : 2≤Fintype.card V := (le_max_right _ _).trans hn
  have hn2r : (2:ℝ)≤Fintype.card V := by exact_mod_cast hn2
  have hh := divisibility_colour_common_event G ρ hρ hsum b η hη.le (by omega)
  have hb := hN (Fintype.card V) ((le_max_left _ _).trans hn)
  simp only [Real.rpow_two,Real.rpow_one,pow_one] at hb
  have hp : 0<1-4*R*(Fintype.card V:ℝ)^2*Real.exp (-η^2*Fintype.card V) := by
    have hi : 1/(Fintype.card V:ℝ)<1 := (div_lt_one (by positivity)).mpr (by linarith)
    linarith
  have hprob := hp.trans_le hh
  by_contra hnone
  have hall (σ : Sym2 V → Fin R) : ¬((∀ a v,|(sampledColourDegree G σ a v:ℝ)-ρ a*G.degree v|<η*Fintype.card V) ∧
      (∀ a u v,u≠v → |(colouredTwoPathCount G σ u v a b:ℝ)-
        ((G.neighborFinset u∩G.neighborFinset v).card:ℝ)*ρ a*ρ b|<η*Fintype.card V)) :=
    fun h => hnone ⟨σ,h⟩
  simp only [FiniteLaw.probability,hall,ite_false,Finset.sum_const_zero] at hprob
  exact (lt_irrefl 0) hprob

end Oberwolfach

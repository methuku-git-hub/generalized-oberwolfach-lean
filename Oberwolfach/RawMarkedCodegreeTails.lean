module

public import Oberwolfach.RawMarkedHubCounts

@[expose] public section

/-! Both marked spoke codegrees on the original raw interval experiment.
The two labels are excluded only when their permutation windows can overlap. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V U Γ Color : Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [DecidableEq V] [DecidableEq U]

theorem rawMarkedCodegree_exponential_event
    (π : Equiv.Perm V) (d : ℕ) (hd : 2≤d)
    (q : U→Γ→ℝ) (hq : ∀ u g,0≤q u g) (hQ : ∀ u,∑ g,q u g≤1/8)
    (s : U→Color→ℝ) (hs : ∀ u j,0≤s u j)
    (hS : ∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
    (hnoshort : ∀ x l,0<l → l<2*d+1 → (π^l) x≠x)
    (hm : 0<Fintype.card U) (g : Γ) (j : Color) (s₀ t₀ : ℝ)
    (hg : ∀ u,q u g=t₀) (hj : ∀ u,s u j=s₀)
    (t : ℝ) (ht : 0<t) :
    1-4*(Fintype.card V:ℝ)^2*Real.exp (-2*t^2/((4*(d:ℝ)+3)^2*(2*Fintype.card U)))≤
    (FiniteLaw.pi (rawIntervalFamilyLaw (V:=V) d hd q hq hQ s hs hS)).probability
      (fun σ=>∀ (b : Bool) (x y : V),¬PermutationClose π (3*d) x y →
        |(∑ u : U,if rawMarkedSpokes π d σ g j b x u ∧ rawMarkedSpokes π d σ g j b y u then (1:ℝ) else 0)-
          Fintype.card U*(if b then t₀ else s₀)^2|<t) := by
  let I := Bool×{z : V×V // ¬PermutationClose π (3*d) z.1 z.2}
  let T (i : I) : Finset V := {i.2.val.1,i.2.val.2}
  let col (i : I) (_ : V) : Γ⊕Color := if i.1 then Sum.inl g else Sum.inr j
  have hsep (i : I) : ∀ x∈T i,∀ y∈T i,x≠y → ¬PermutationClose π (3*d) x y := by
    intro x hx y hy hxy
    simp only [T,Finset.mem_insert,Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact (hxy rfl).elim
    · exact i.2.property
    · simpa only [permutationClose_symm π (3*d)] using i.2.property
    · exact (hxy rfl).elim
  have hnonempty (i : I) : (T i).Nonempty := ⟨i.2.val.1,Finset.mem_insert_self _ _⟩
  have hsize (i : I) : (T i).card≤2 := by
    simpa [T] using (Finset.card_insert_le i.2.val.1 {i.2.val.2})
  have hh := rawIntervalSelectedLabelCount_common_event π d hd q hq hQ s hs hS hnoshort hm
    col T hsep hnonempty 2 (by omega) hsize t ht
  have hi : Fintype.card I≤2*Fintype.card V^2 := by
    simp only [I,Fintype.card_prod,Fintype.card_bool]
    apply Nat.mul_le_mul_left
    exact (Fintype.card_subtype_le _).trans_eq (by simp [pow_two])
  have hiR : (Fintype.card I:ℝ)≤2*(Fintype.card V:ℝ)^2 := by exact_mod_cast hi
  have hbudget : (Fintype.card I:ℝ)*(2*Real.exp (-2*t^2/((4*(d:ℝ)+3)^2*(2*Fintype.card U))))≤
      4*(Fintype.card V:ℝ)^2*Real.exp (-2*t^2/((4*(d:ℝ)+3)^2*(2*Fintype.card U))) := by
    nlinarith only [mul_le_mul_of_nonneg_right hiR
      (show 0≤2*Real.exp (-2*t^2/((4*(d:ℝ)+3)^2*(2*Fintype.card U))) by positivity)]
  simp only [Nat.cast_ofNat] at hh
  apply ((sub_le_sub_left hbudget 1).trans hh).trans
  apply finiteLaw_probability_mono
  intro σ hσ b x y hxy
  have hne : x≠y := fun h=>hxy (Or.inl h)
  have hcount := hσ (b,⟨(x,y),hxy⟩)
  have hprob (u : U) : Sum.elim (q u) (s u) (if b then Sum.inl g else Sum.inr j)=
      if b then t₀ else s₀ := by cases b <;> simp [hg,hj]
  simp only [col,T,Finset.prod_insert,Finset.mem_singleton,hne,not_false_eq_true,Finset.prod_singleton,
    hprob,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,← pow_two] at hcount
  convert hcount using 1
  unfold rawIntervalSelectedLabelCount
  congr 2
  apply Finset.sum_congr rfl
  intro u _
  cases b <;> simp [rawMarkedSpokes]

theorem rawMarkedCodegree_normalized_event
    (π : Equiv.Perm V) (d : ℕ) (hd : 2≤d)
    (q : U→Γ→ℝ) (hq : ∀ u g,0≤q u g) (hQ : ∀ u,∑ g,q u g≤1/8)
    (s : U→Color→ℝ) (hs : ∀ u j,0≤s u j)
    (hS : ∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
    (hnoshort : ∀ x l,0<l → l<2*d+1 → (π^l) x≠x)
    (hm : 0<Fintype.card U) (g : Γ) (j : Color) (s₀ t₀ : ℝ)
    (hg : ∀ u,q u g=t₀) (hj : ∀ u,s u j=s₀)
    (δ sstar : ℝ) (hδ : 0<δ) (hsstar : 0<sstar) (hslo : sstar≤s₀) (htlo : sstar≤t₀) :
    1-4*(Fintype.card V:ℝ)^2*Real.exp
      (-2*(δ*sstar^2*Fintype.card U)^2/((4*(d:ℝ)+3)^2*(2*Fintype.card U)))≤
    (FiniteLaw.pi (rawIntervalFamilyLaw (V:=V) d hd q hq hQ s hs hS)).probability
      (fun σ=>∀ (b : Bool) (x y : V),¬PermutationClose π (3*d) x y →
        |(Fintype.card U:ℝ)⁻¹*(∑ u : U,(if b then t₀ else s₀)⁻¹^2*
          (if rawMarkedSpokes π d σ g j b x u ∧ rawMarkedSpokes π d σ g j b y u then (1:ℝ) else 0))-1|≤δ) := by
  have hmR : (0:ℝ)<Fintype.card U := by exact_mod_cast hm
  have hh := rawMarkedCodegree_exponential_event π d hd q hq hQ s hs hS hnoshort hm
    g j s₀ t₀ hg hj (δ*sstar^2*Fintype.card U) (by positivity)
  apply hh.trans
  apply finiteLaw_probability_mono
  intro σ hσ b x y hxy
  let w : ℝ := if b then t₀ else s₀
  let X : ℝ := ∑ u : U,if rawMarkedSpokes π d σ g j b x u ∧ rawMarkedSpokes π d σ g j b y u then 1 else 0
  have hwlo : sstar≤w := by cases b <;> assumption
  have hw : 0<w := hsstar.trans_le hwlo
  have hc : |X-Fintype.card U*w^2|<δ*sstar^2*Fintype.card U := hσ b x y hxy
  have he : (Fintype.card U:ℝ)⁻¹*(∑ u : U,w⁻¹^2*
      (if rawMarkedSpokes π d σ g j b x u ∧ rawMarkedSpokes π d σ g j b y u then (1:ℝ) else 0))-1=
      (X-Fintype.card U*w^2)/((Fintype.card U:ℝ)*w^2) := by
    rw [← Finset.mul_sum]
    change (Fintype.card U:ℝ)⁻¹*(w⁻¹^2*X)-1=_
    field_simp [ne_of_gt hmR,ne_of_gt hw]
    <;> ring
  change |(Fintype.card U:ℝ)⁻¹*(∑ u : U,w⁻¹^2*
      (if rawMarkedSpokes π d σ g j b x u ∧ rawMarkedSpokes π d σ g j b y u then (1:ℝ) else 0))-1|≤δ
  rw [he,abs_div,abs_of_pos (by positivity : 0<(Fintype.card U:ℝ)*w^2)]
  apply (div_le_iff₀ (by positivity : 0<(Fintype.card U:ℝ)*w^2)).mpr
  have hw2 : sstar^2≤w^2 := by nlinarith only [hsstar,hwlo]
  have hscale := mul_le_mul_of_nonneg_left hw2 (show 0≤δ*(Fintype.card U:ℝ) by positivity)
  linarith only [hc,hscale]

end Oberwolfach

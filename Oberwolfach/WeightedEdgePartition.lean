module

public import Oberwolfach.WeightedColorCommonUpper

@[expose] public section

/-! A single random edge partition controls all vertex degrees, all
codegrees and all supplied nonnegative weights simultaneously. -/
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem weighted_edge_partition_exists
    {V E I C A : Type} [Fintype V] [Fintype E] [Fintype I] [Fintype C] [Fintype A]
    [Nonempty C] (R : E → Finset V) (part : E → I)
    (w : A → E → ℝ) (b : A → ℝ) (W : I → A → ℝ)
    (d β : ℝ) (D B : ℕ) (T : I → A → ℝ) (s₀ s₁ s₂ : ℝ)
    (hb : ∀ a,0<b a) (hw : ∀ a e,0≤w a e ∧ w a e≤b a)
    (hdegree : ∀ i v,((Finset.univ.filter (fun e=>part e=i ∧ v∈R e)).card : ℝ)≤d)
    (hcodeg : ∀ i v u,v≠u →
      ((Finset.univ.filter (fun e=>part e=i ∧ v∈R e ∧ u∈R e)).card : ℝ)≤β)
    (hβ : 0≤β) (hW : ∀ i a,(∑ e,if part e=i then w a e else 0)≤W i a)
    (hs₀ : 0≤s₀) (hs₁ : 0≤s₁) (hs₂ : 0≤s₂)
    (hsmall :
      (∑ _i : I,∑ _v : V,∑ _c : C,Real.exp (d/Fintype.card C*(Real.exp s₀-1)-s₀*((D : ℝ)+1)))+
      ((∑ _i : I,∑ _v : V,∑ _u : V,∑ _c : C,Real.exp (β/Fintype.card C*(Real.exp s₁-1)-s₁*((B : ℝ)+1)))+
      (∑ i : I,∑ a : A,∑ _c : C,Real.exp ((W i a/Fintype.card C*(Real.exp s₂-1)-s₂*T i a)/b a)))<1) :
    ∃ split : E → C,
      (∀ i c v,(Finset.univ.filter (fun e=>part e=i ∧ split e=c ∧ v∈R e)).card≤D) ∧
      (∀ i c v u,v≠u →
        (Finset.univ.filter (fun e=>part e=i ∧ split e=c ∧ v∈R e ∧ u∈R e)).card≤B) ∧
      (∀ i a c,(∑ e,if part e=i ∧ split e=c then w a e else 0)<T i a) := by
  classical
  let J := (I×V)⊕((I×(V×V))⊕(I×A))
  let f : J → E → ℝ := Sum.elim
    (fun iv e=>if part e=iv.1 ∧ iv.2∈R e then 1 else 0)
    (Sum.elim
      (fun ivu e=>if ivu.2.1≠ivu.2.2 ∧ part e=ivu.1 ∧ ivu.2.1∈R e ∧ ivu.2.2∈R e then 1 else 0)
      (fun ia e=>if part e=ia.1 then w ia.2 e else 0))
  let bound : J → ℝ := Sum.elim (fun _=>1) (Sum.elim (fun _=>1) (fun ia=>b ia.2))
  let mean : J → ℝ := Sum.elim (fun _=>d/Fintype.card C)
    (Sum.elim (fun _=>β/Fintype.card C) (fun ia=>W ia.1 ia.2/Fintype.card C))
  let rate : J → ℝ := Sum.elim (fun _=>s₀) (Sum.elim (fun _=>s₁) (fun _=>s₂))
  let cutoff : J → ℝ := Sum.elim (fun _=>(D : ℝ)+1)
    (Sum.elim (fun _=>(B : ℝ)+1) (fun ia=>T ia.1 ia.2))
  have hbound : ∀ j,0<bound j := by
    intro j
    rcases j with iv|ivu|ia <;> simp only [bound,Sum.elim_inl,Sum.elim_inr]
    · norm_num
    · norm_num
    · exact hb ia.2
  have hf : ∀ j e,0≤f j e ∧ f j e≤bound j := by
    intro j e
    rcases j with iv|ivu|ia <;> simp only [f,bound,Sum.elim_inl,Sum.elim_inr]
    · split_ifs <;> norm_num
    · split_ifs <;> norm_num
    · split_ifs
      · exact hw ia.2 e
      · exact ⟨le_refl _,(hb ia.2).le⟩
  have hmean : ∀ j,(∑ e,f j e)/Fintype.card C≤mean j := by
    intro j
    rcases j with iv|ivu|ia <;> simp only [f,mean,Sum.elim_inl,Sum.elim_inr]
    · apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      simpa only [Finset.sum_boole] using hdegree iv.1 iv.2
    · apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      by_cases h : ivu.2.1=ivu.2.2
      · simpa only [h,ne_eq,not_true_eq_false,false_and,ite_false,Finset.sum_const_zero] using hβ
      · simpa only [ne_eq,h,not_false_eq_true,true_and,Finset.sum_boole] using hcodeg ivu.1 ivu.2.1 ivu.2.2 h
    · exact div_le_div_of_nonneg_right (hW ia.1 ia.2) (Nat.cast_nonneg _)
  have hrate : ∀ j,0≤rate j := by
    intro j;rcases j with iv|ivu|ia
    · exact hs₀
    · exact hs₁
    · exact hs₂
  obtain ⟨split,hsplit⟩ := weightedColor_common_upper (C:=C) f bound mean rate cutoff hbound hf hrate hmean
    (by simpa only [J,Fintype.sum_sum_type,Fintype.sum_prod_type,bound,mean,rate,cutoff,
      Sum.elim_inl,Sum.elim_inr,div_one] using hsmall)
  refine ⟨split,?_,?_,?_⟩
  · intro i c v
    have hh := hsplit (Sum.inl (i,v)) c
    have heq : (∑ e,if split e=c then f (Sum.inl (i,v)) e else 0)=
        ((Finset.univ.filter (fun e=>part e=i ∧ split e=c ∧ v∈R e)).card : ℝ) := by
      rw [← Finset.sum_boole]
      apply Finset.sum_congr rfl
      intro e _
      dsimp [f]
      by_cases hp : part e=i <;> by_cases hc : split e=c <;> by_cases hv : v∈R e <;> simp [hp,hc,hv]
    rw [heq] at hh
    dsimp only [cutoff,Sum.elim_inl,Sum.elim_inr] at hh
    have hnat : (Finset.univ.filter (fun e=>part e=i ∧ split e=c ∧ v∈R e)).card<D+1 := by
      exact_mod_cast hh
    omega
  · intro i c v u hvu
    have hh := hsplit (Sum.inr (Sum.inl (i,(v,u)))) c
    have heq : (∑ e,if split e=c then f (Sum.inr (Sum.inl (i,(v,u)))) e else 0)=
        ((Finset.univ.filter (fun e=>part e=i ∧ split e=c ∧ v∈R e ∧ u∈R e)).card : ℝ) := by
      rw [← Finset.sum_boole]
      apply Finset.sum_congr rfl
      intro e _
      dsimp [f]
      by_cases hp : part e=i <;> by_cases hc : split e=c <;> by_cases hv : v∈R e <;> by_cases hu : u∈R e <;>
        simp [hp,hc,hv,hu,hvu]
    rw [heq] at hh
    dsimp only [cutoff,Sum.elim_inl,Sum.elim_inr] at hh
    have hnat : (Finset.univ.filter (fun e=>part e=i ∧ split e=c ∧ v∈R e ∧ u∈R e)).card<B+1 := by
      exact_mod_cast hh
    omega
  · intro i a c
    have hh := hsplit (Sum.inr (Sum.inr (i,a))) c
    dsimp only [cutoff,Sum.elim_inl,Sum.elim_inr] at hh
    convert hh using 1
    apply Finset.sum_congr rfl
    intro e _
    dsimp [f]
    by_cases hp : part e=i <;> by_cases hc : split e=c <;> simp [hp,hc]

end Oberwolfach

module

public import Oberwolfach.ColourDegrees
public import Oberwolfach.UndirectedTwoPathPacking

@[expose] public section

/-! The candidate paths used by the parity repair have disjoint physical
sampling coordinates for fixed endpoints. This proves their concentration
under the original independent edge-colour law. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem finiteLaw_fixed_size_patterns_tail_at_scale
    {E I : Type*} [Fintype E] [DecidableEq E]
    {State : E → Type*} [∀ e,Fintype (State e)]
    (μ : ∀ e,FiniteLaw (State e)) (C : Finset I) (F : I → Finset E)
    (s : I → ∀ e,State e) (k : ℕ) (hk : 0<k)
    (hsize : ∀ i∈C,(F i).card=k)
    (hdisj : ∀ i∈C,∀ j∈C,i≠j → Disjoint (F i) (F j))
    {n t : ℝ} (hcard : (C.card:ℝ)≤n) (ht : 0≤t) :
    (FiniteLaw.pi μ).probability (fun σ =>
      t≤|(∑ i∈C,patternValue (F i) (s i) σ)-(∑ i∈C,∏ e∈F i,(μ e).mass (s i e))|)≤
      2*Real.exp (-2*t^2/(n*k)) := by
  classical
  by_cases hC : C=∅
  · subst C
    by_cases ht0 : t=0
    · subst t;norm_num [FiniteLaw.probability,(FiniteLaw.pi μ).total]
    · have htp : 0<t := lt_of_le_of_ne ht (Ne.symm ht0)
      simp only [Finset.sum_empty,sub_self,abs_zero,not_le.mpr htp]
      rw [finiteLaw_probability_false]
      positivity
  · have hh := finiteLaw_disjoint_patterns_tail μ C F s hdisj ht
    have hsum : (∑ i∈C,((F i).card:ℝ))=(C.card:ℝ)*k := by
      simp_rw [Finset.sum_congr rfl (fun i hi => congrArg (fun j : ℕ => (j:ℝ)) (hsize i hi))]
      simp
    rw [hsum] at hh
    apply hh.trans
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply Real.exp_le_exp.mpr
    have hp : (0:ℝ)<C.card := by exact_mod_cast Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hC)
    have hkp : (0:ℝ)<k := Nat.cast_pos.mpr hk
    have hden := mul_le_mul_of_nonneg_right hcard hkp.le
    have hd := div_le_div_of_nonneg_left (show 0≤(2:ℝ)*t^2 by positivity) (mul_pos hp hkp) hden
    simpa only [neg_div,neg_mul] using neg_le_neg hd

theorem common_two_path_edges_disjoint {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (u v : V) (huv : u≠v) :
    ∀ x∈G.neighborFinset u∩G.neighborFinset v,
    ∀ y∈G.neighborFinset u∩G.neighborFinset v,x≠y →
      Disjoint (twoPathEdges u v x) (twoPathEdges u v y) := by
  intro x hx y hy hxy
  have hux : u≠x := ((G.mem_neighborFinset _ _).mp (Finset.mem_inter.mp hx).1).ne
  have hvx : v≠x := ((G.mem_neighborFinset _ _).mp (Finset.mem_inter.mp hx).2).ne
  have huy : u≠y := ((G.mem_neighborFinset _ _).mp (Finset.mem_inter.mp hy).1).ne
  have hvy : v≠y := ((G.mem_neighborFinset _ _).mp (Finset.mem_inter.mp hy).2).ne
  apply Finset.disjoint_left.mpr
  intro e he hey
  simp only [twoPathEdges,Finset.mem_insert,Finset.mem_singleton] at he hey
  rcases he with rfl | rfl <;> rcases hey with he | he <;>
    rw [Sym2.eq_iff] at he <;> aesop

def colouredTwoPathCount {V : Type*} [Fintype V] [DecidableEq V] {R : ℕ}
    (G : SimpleGraph V) (σ : Sym2 V → Fin R) (u v : V) (a b : Fin R) : ℕ :=
  ((G.neighborFinset u∩G.neighborFinset v).filter
    (fun w => σ s(u,w)=a ∧ σ s(w,v)=b)).card

theorem colouredTwoPathCount_patterns {V : Type*} [Fintype V] [DecidableEq V] {R : ℕ}
    (G : SimpleGraph V) (σ : Sym2 V → Fin R) (u v : V) (huv : u≠v) (a b : Fin R) :
    (colouredTwoPathCount G σ u v a b:ℝ)=
      ∑ w∈G.neighborFinset u∩G.neighborFinset v,
        patternValue (twoPathEdges u v w) (fun e => if e=s(u,w) then a else b) σ := by
  unfold colouredTwoPathCount
  rw [Finset.card_filter,Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro w _
  have he : s(u,w)≠s(w,v) := by
    intro h;rcases Sym2.eq_iff.mp h with ⟨h1,h2⟩ | ⟨h1,h2⟩ <;> exact huv (by aesop)
  simp only [patternValue,twoPathEdges,Finset.prod_insert,Finset.prod_singleton,Finset.mem_singleton,he,Ne.symm he,not_false_eq_true,ite_true,ite_false,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  split_ifs <;> simp_all

theorem colouredTwoPathCount_tail {V : Type*} [Fintype V] [DecidableEq V] {R : ℕ}
    (G : SimpleGraph V) (ρ : Fin R → ℝ) (hρ : ∀ a,0≤ρ a) (hsum : ∑ a,ρ a=1)
    (u v : V) (huv : u≠v) (a b : Fin R) {t : ℝ} (ht : 0≤t) :
    (FiniteLaw.pi (fun _ : Sym2 V => FiniteLaw.categorical ρ hρ hsum)).probability
      (fun σ => t≤|(colouredTwoPathCount G σ u v a b:ℝ)-
        ((G.neighborFinset u∩G.neighborFinset v).card:ℝ)*ρ a*ρ b|)≤
      2*Real.exp (-t^2/Fintype.card V) := by
  let C := G.neighborFinset u∩G.neighborFinset v
  have he (w : V) : s(u,w)≠s(w,v) := by
    intro h;rcases Sym2.eq_iff.mp h with ⟨h1,h2⟩ | ⟨h1,h2⟩ <;> exact huv (by aesop)
  have hsize (w : V) (_ : w∈C) : (twoPathEdges u v w).card=2 := by
    simp [twoPathEdges,he w]
  have hh := finiteLaw_fixed_size_patterns_tail_at_scale
    (fun _ : Sym2 V => FiniteLaw.categorical ρ hρ hsum) C (twoPathEdges u v)
    (fun w e => if e=s(u,w) then a else b) 2 (by omega) hsize
    (common_two_path_edges_disjoint G u v huv)
    (n:=(Fintype.card V:ℝ)) (by exact_mod_cast Finset.card_le_univ C) ht
  have hmean : (∑ w∈C,∏ e∈twoPathEdges u v w,
      (FiniteLaw.categorical ρ hρ hsum).mass (if e=s(u,w) then a else b))=
      (C.card:ℝ)*ρ a*ρ b := by
    simp only [FiniteLaw.categorical]
    have hprod (w : V) : (∏ e∈twoPathEdges u v w,ρ (if e=s(u,w) then a else b))=ρ a*ρ b := by
      simp [twoPathEdges,he w,Ne.symm (he w)]
    simp only [hprod,Finset.sum_const,nsmul_eq_mul,mul_assoc]
  rw [hmean] at hh
  dsimp only [C] at hh
  have hexp : -2*t^2/((Fintype.card V:ℝ)*2) = -t^2/Fintype.card V := by ring
  simpa only [← colouredTwoPathCount_patterns G _ u v huv a b,hexp,Nat.cast_ofNat] using hh

end Oberwolfach

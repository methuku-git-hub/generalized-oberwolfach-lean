module

public import Oberwolfach.CliqueRetentionExpansion
public import Oberwolfach.FiniteTupleConflicts
public import Oberwolfach.GoodTupleSummation
public import Oberwolfach.TupleRetentionBounds

@[expose] public section

/-! Passing from root-tuple retention estimates to simultaneous retention
in cliques. Conflicting tuples contribute zero, with their number bounded
by actual cross-neighbour counts. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem clique_tuple_approximation
    {V C J : Type*} [Fintype V] [Fintype C] [Fintype J]
    (G : SimpleGraph V) (T : J → Finset V)
    (hT : ∀ j,∀ u∈T j,∀ v∈T j,u≠v → G.Adj u v)
    (μ : FiniteLaw (V → C×Bool)) (c : C) {s A : ℕ}
    (hsize : ∀ j,(T j).card≤s)
    (hcross : ∀ i j,i≠j → ∀ v∈T i,((T j).filter (G.Adj v)).card≤A)
    {b ε : ℝ} (hb : 0≤b) (hε : 0≤ε)
    (hgood : ∀ f : (j : J) → {v // v∈T j},
      (∀ i j,¬G.Adj (f i).val (f j).val) →
      b≤μ.probability (fun σ=>∀ j,coinRetainedColour G σ (f j).val=some c) ∧
      μ.probability (fun σ=>∀ j,coinRetainedColour G σ (f j).val=some c)≤(1+ε)*b) :
    |μ.probability (fun σ=>∀ j,∃ v∈T j,coinRetainedColour G σ v=some c)-
      (∏ j,((T j).card : ℝ))*b|≤
      (∏ j,((T j).card : ℝ))*ε*b+
        (((Fintype.card J)^2*A*s^(Fintype.card J-1) : ℕ) : ℝ)*b := by
  classical
  let X := fun j : J=>{v // v∈T j}
  let bad := fun f : ∀ j,X j=>∃ i j,i≠j ∧ G.Adj (f i).val (f j).val
  letI : DecidablePred bad := fun f=>Classical.propDecidable (bad f)
  let p := fun f : ∀ j,X j=>μ.probability (fun σ=>∀ j,coinRetainedColour G σ (f j).val=some c)
  have hp (f : ∀ j,X j) (hf : ¬bad f) : b≤p f ∧ p f≤(1+ε)*b := by
    apply hgood f
    intro i j hadj
    exact hf ⟨i,j,fun he=>G.irrefl (he ▸ hadj),hadj⟩
  have hz (f : ∀ j,X j) (hf : bad f) : p f=0 := by
    obtain ⟨i,j,_,hij⟩ := hf
    exact conflicting_retention_probability_zero G μ (fun j=>(f j).val) c ⟨i,j,hij⟩
  have hX (j : J) : Fintype.card (X j)≤s := by simpa only [X,Fintype.card_coe] using hsize j
  have hpairCount (i j : J) (hij : i≠j) (a : X i) :
      (Finset.univ.filter (fun b : X j=>G.Adj a.val b.val)).card≤A := by
    apply (Finset.card_le_card_of_injOn
      (s:=Finset.univ.filter (fun b : X j=>G.Adj a.val b.val))
      (t:=(T j).filter (G.Adj a.val)) (fun x : X j=>x.val) ?_ ?_).trans
      (hcross i j hij a.val a.property)
    · intro x hx
      exact Finset.mem_filter.mpr ⟨x.property,(Finset.mem_filter.mp hx).2⟩
    · intro x _ y _ he
      exact Subtype.ext he
  have hB : (Finset.univ.filter bad).card≤(Fintype.card J)^2*A*s^(Fintype.card J-1) := by
    have hh := finite_tuple_conflict_count (fun i j a b=>G.Adj a.val b.val) hpairCount hX
    convert hh using 1
    apply congrArg Finset.card
    ext f
    simp only [Finset.mem_filter,bad]
  have hN : (Fintype.card (∀ j,X j) : ℝ)=∏ j,((T j).card : ℝ) := by
    simp only [Fintype.card_pi,X,Fintype.card_coe,Nat.cast_prod]
  have hh := finite_sum_good_approximation bad p hb hε hp hz
  rw [hN] at hh
  have hBR : ((Finset.univ.filter bad).card : ℝ)≤
      (((Fintype.card J)^2*A*s^(Fintype.card J-1) : ℕ) : ℝ) := by exact_mod_cast hB
  rw [clique_joint_retention_expansion G T hT μ c]
  exact hh.trans (add_le_add (le_refl _) (mul_le_mul_of_nonneg_right hBR hb))

end Oberwolfach

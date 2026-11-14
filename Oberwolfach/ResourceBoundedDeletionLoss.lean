module

public import Oberwolfach.UniformResourceCounts
public import Oberwolfach.ResourceVertexDeletion
public import Oberwolfach.CandidateResourceRestriction

@[expose] public section

/-! A realised deletion costs the supplied pair weight for each deleted
vertex or forbidden endpoint pair. No sampling probability enters this bound. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]

theorem ambient_resource_pair_weight (R : C → Finset V) (r J : ℕ) (hr : 2≤r)
    (hR : ∀ C₀,(R C₀).card=r) (hJ : ∀ Y : Finset V,Fintype.card {C₀ : C // R C₀=Y}≤J)
    (w : C → ℝ) (B : ℝ) (hB : 0≤B) (hn : 0<Fintype.card V)
    (hw : ∀ C₀,w C₀≤B/(Fintype.card V:ℝ)^(r-1))
    (x y : V) (hxy : x≠y) :
    (∑ C₀,if x∈R C₀ ∧ y∈R C₀ then w C₀ else 0)≤J*B/Fintype.card V := by
  have hc := uniform_resources_pair_count R r J hr hR hJ x y hxy
  have hnR : (0:ℝ)<Fintype.card V := Nat.cast_pos.mpr hn
  calc
    _ ≤ ∑ C₀,if x∈R C₀ ∧ y∈R C₀ then B/(Fintype.card V:ℝ)^(r-1) else 0 := by
      apply Finset.sum_le_sum
      intro C₀ _;split_ifs <;> first | exact hw C₀ | exact le_rfl
    _ = (Fintype.card {C₀ : C // x∈R C₀ ∧ y∈R C₀}:ℝ)*(B/(Fintype.card V:ℝ)^(r-1)) := by
      simp only [Fintype.card_subtype,←Finset.sum_filter,Finset.sum_const,nsmul_eq_mul]
    _ ≤ (J*(Fintype.card V:ℝ)^(r-2))*(B/(Fintype.card V:ℝ)^(r-1)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast hc
    _ = _ := by
      rw [show r-1=(r-2)+1 by omega,pow_succ]
      field_simp

 theorem candidate_degree_restriction_loss (R : C → Finset V) (w : C → ℝ)
    (hw : ∀ C₀,0≤w C₀) (P : C → Prop) [DecidablePred P]
    (Z : Finset V) (E : Finset (V×V))
    (hE : ∀ e∈E,e.1≠e.2) (K : ℝ)
    (hpair : ∀ x y,x≠y→(∑ C₀,if x∈R C₀ ∧ y∈R C₀ then w C₀ else 0)≤K)
    (hgood : ∀ C₀,Disjoint (R C₀) Z→(∀ e∈E,¬(e.1∈R C₀ ∧ e.2∈R C₀))→P C₀)
    (x : V) (hx : x∉Z) :
    0≤hypergraphWeightedDegree R w x-
      hypergraphWeightedDegree R (fun C₀=>if P C₀ then w C₀ else 0) x ∧
    hypergraphWeightedDegree R w x-
      hypergraphWeightedDegree R (fun C₀=>if P C₀ then w C₀ else 0) x≤(Z.card+E.card:ℕ)*K := by
  let hit := fun C₀ (j : Z⊕E)=>match j with
    | .inl z=>z.val∈R C₀
    | .inr e=>e.val.1∈R C₀ ∧ e.val.2∈R C₀
  have he : hypergraphWeightedDegree R w x-
      hypergraphWeightedDegree R (fun C₀=>if P C₀ then w C₀ else 0) x=
      ∑ C₀,if x∈R C₀ ∧ ¬P C₀ then w C₀ else 0 := by
    unfold hypergraphWeightedDegree
    rw [←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro C₀ _
    by_cases hv : x∈R C₀ <;> by_cases hp : P C₀ <;> simp [hv,hp]
  rw [he]
  constructor
  · exact Finset.sum_nonneg (fun C₀ _=>by split_ifs;exact hw C₀;exact le_rfl)
  · have hh := finite_weighted_union_bound w hw (fun C₀=>x∈R C₀) hit
    calc
      _ ≤ ∑ C₀,if x∈R C₀ ∧ ∃ j,hit C₀ j then w C₀ else 0 := by
        apply Finset.sum_le_sum
        intro C₀ _
        by_cases ha : x∈R C₀ ∧ ¬P C₀
        · have hh' : ∃ j,hit C₀ j := by
            by_contra hn
            apply ha.2
            apply hgood C₀
            · apply Finset.disjoint_left.mpr
              intro z hz hzZ
              exact hn ⟨.inl ⟨z,hzZ⟩,hz⟩
            · intro e heE heR
              exact hn ⟨.inr ⟨e,heE⟩,heR⟩
          rw [if_pos ha,if_pos ⟨ha.1,hh'⟩]
        · rw [if_neg ha];split_ifs;exact hw C₀;exact le_rfl
      _ ≤ ∑ j : Z⊕E,∑ C₀,if x∈R C₀ ∧ hit C₀ j then w C₀ else 0 := by convert hh using 1 <;> congr!
      _ ≤ ∑ _j : Z⊕E,K := by
        apply Finset.sum_le_sum
        intro j _
        cases j with
        | inl z=>
          convert hpair x z.val (fun he=>hx (he ▸ z.property)) using 1 <;> congr!
        | inr e=>
          apply le_trans _ (hpair e.val.1 e.val.2 (hE e.val e.property))
          apply Finset.sum_le_sum
          intro C₀ _
          by_cases hp : e.val.1∈R C₀ ∧ e.val.2∈R C₀
          · simp only [hit,hp,and_true,ite_true];split_ifs;exact le_rfl;exact hw C₀
          · simp only [hit,hp,and_false,ite_false,le_refl]
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_sum,Fintype.card_coe,nsmul_eq_mul,Nat.cast_add]

end Oberwolfach

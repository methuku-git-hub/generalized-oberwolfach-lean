module

public import Oberwolfach.FractionalResourceMatching
public import Oberwolfach.UniformResourceWeights
public import Oberwolfach.SigmaClassCounts
public import Oberwolfach.ResourceClassCounts

@[expose] public section

/-! Round exact vertex weights to an almost spanning vertex-disjoint
family, retaining the integer class proportions of the uncovered set.
The matching resources are vertices, not graph edges. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3600000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]

theorem profile_fractional_factor (a : I → ℕ) (c J : ℕ) (hc : 2 ≤ c)
    (ha : ∀ i,1 ≤ a i) (hsize : ∑ i,a i=c) (B γ : ℝ) (hB : 0 ≤ B) (hγ : 0 < γ) :
    ∃ k₀ : ℕ,∀ k : ℕ,k₀ ≤ k →
      ∀ (V : I → Type) [∀ i,Fintype (V i)] [∀ i,DecidableEq (V i)]
        (C : Type) [Fintype C] [DecidableEq C],
      (∀ i,Fintype.card (V i)=a i*k) →
      ∀ (R : C → Finset (Σ i,V i)) (w : C → ℝ),
      (∀ C₀ i,(Finset.univ.filter (fun v : V i => (⟨i,v⟩ : Σ i,V i)∈R C₀)).card=a i) →
      (∀ Y : Finset (Σ i,V i),Fintype.card {C₀ : C // R C₀=Y} ≤ J) →
      (∀ C₀,0 ≤ w C₀ ∧ w C₀ ≤ B/(k:ℝ)^(c-1)) →
      (∀ v,hypergraphWeightedDegree R w v=1) →
      ∃ M : Finset C,
        (∀ C₀∈M,∀ D∈M,C₀≠D → Disjoint (R C₀) (R D)) ∧
        ((Finset.univ\M.biUnion R).card:ℝ) ≤ γ*k ∧ M.card ≤ k ∧
        ∀ i,(Finset.univ.filter (fun v : V i => (⟨i,v⟩ : Σ i,V i)∈Finset.univ\M.biUnion R)).card=
          a i*(k-M.card) := by
  let K := B*J*(c:ℝ)^(c-2)+1
  have hK : 0 < K := by dsimp [K];positivity
  have hcR : (0:ℝ) < c := by exact_mod_cast (show 0<c by omega)
  obtain ⟨η,hη,n₀,hn₀⟩ := fractional_resource_matching c 2 hc (by omega) K 1 (γ/c)
    hK (by norm_num) (by positivity)
  refine ⟨max n₀ c,?_⟩
  intro k hk V _ _ C _ _ hn R w hR hJ hw hload
  have hkn : n₀ ≤ k := (le_max_left _ _).trans hk
  have hkc : c ≤ k := (le_max_right _ _).trans hk
  have hk0 : 0 < k := by omega
  have hkR : (0:ℝ)<k := by exact_mod_cast hk0
  let U := Σ i,V i
  have hnall : Fintype.card U=c*k := by
    simp only [U,Fintype.card_sigma,hn,← Finset.sum_mul,hsize]
  have hRC (C₀ : C) : (R C₀).card=c := by rw [sigma_finset_card];simp only [hR];exact hsize
  have hpair (u v : U) (huv : u≠v) :
      (∑ C₀,if u∈R C₀ ∧ v∈R C₀ then w C₀ else 0) ≤ K/k := by
    have hh := uniform_resource_pair_weight R c J hc hRC hJ w B k hB hkR
      (by exact_mod_cast hnall) (fun C₀ => (hw C₀).2) u v huv
    exact hh.trans (div_le_div_of_nonneg_right (by dsimp [K];linarith) hkR.le)
  obtain ⟨M,hMM,hleft,_,_⟩ := hn₀ k hkn U C Empty Unit R w
    (fun x => nomatch x) (fun _ => Finset.univ)
    (by rw [hnall,pow_two];exact Nat.mul_le_mul_right k hkc)
    (by simp) (by simp only [Fintype.card_unit];have hh : 0 < k^2 := pow_pos hk0 _;omega)
    (fun C₀ => by rw [hRC];exact ⟨hc,le_rfl⟩) (fun C₀ => (hw C₀).1)
    (fun v => by rw [hload];constructor <;> linarith) hpair
    (fun _ => by
      simp only [Finset.card_univ,hnall,Nat.cast_mul,one_mul]
      have hc1 : (1:ℝ) ≤ c := by exact_mod_cast (show 1≤c by omega)
      nlinarith)
    (fun x => nomatch x) (fun x => nomatch x)
  have hMcard : M.card ≤ k := by
    obtain ⟨i⟩ := (inferInstance : Nonempty I)
    have hcount := resource_biUnion_class_card R M Sigma.fst a hMM
      (fun C₀ _ i => (sigma_finset_class_card (R C₀) i).trans (hR C₀ i)) i
    rw [sigma_finset_class_card] at hcount
    have hbound := Finset.card_le_univ (Finset.univ.filter (fun v : V i => (⟨i,v⟩ : U)∈M.biUnion R))
    rw [hcount,hn] at hbound
    nlinarith [ha i]
  refine ⟨M,hMM,?_,hMcard,?_⟩
  · have hh := hleft ()
    simp only [Finset.card_univ,hnall,Nat.cast_mul] at hh
    have he : (γ/(c:ℝ))*((c:ℝ)*k)=γ*k := by field_simp
    rwa [he] at hh
  · intro i
    rw [← sigma_finset_class_card]
    exact resource_leftover_class_card R M Finset.univ Sigma.fst a k hMM
      (fun C₀ _ i => (sigma_finset_class_card (R C₀) i).trans (hR C₀ i))
      (fun i => by rw [sigma_finset_class_card];simp only [Finset.mem_univ,Finset.filter_true,Finset.card_univ,hn])
      (Finset.subset_univ _) hMcard i

end Oberwolfach

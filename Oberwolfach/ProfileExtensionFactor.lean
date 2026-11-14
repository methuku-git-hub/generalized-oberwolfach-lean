module

public import Oberwolfach.ProfileInducedFactor
public import Oberwolfach.AbsorberExtensionRestriction
public import Oberwolfach.ExtensionResourceWeights

@[expose] public section

/-! Deterministic factor extraction on the enlarged ground set. The
sampled root sums and the counted absorbers are explicit caller inputs;
the restriction at the additional vertices is derived, not assumed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option synthInstance.maxSize 256
set_option maxHeartbeats 4200000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I T : Type} [Fintype I] [DecidableEq I] [Nonempty I] [Fintype T] [DecidableEq T]

theorem profile_extension_factor (a : I → ℕ) (c J : ℕ) (hc : 3 ≤ c)
    (ha : ∀ i,1 ≤ a i) (hsize : ∑ i,a i=c)
    (S : T → VertexAbsorberTemplate c) (a₀ b B : ℝ)
    (ha₀ : 0 < a₀) (hb : 0 < b) (hB : 0 ≤ B) :
    ∃ η : ℝ,0 < η ∧ ∀ q : ℕ,∃ k₀ : ℕ,∀ k : ℕ,k₀ ≤ k →
      ∀ (V : I → Type) [∀ i,Fintype (V i)] [∀ i,DecidableEq (V i)]
        (C : Type) [Fintype C] [DecidableEq C],
      ∀ (R : C → Finset (Σ i,V i)) (w : C → ℝ) (A Z : Finset (Σ i,V i)),
      Disjoint A Z → Z.card ≤ q →
      (∀ i,(Finset.univ.filter (fun v : V i => (⟨i,v⟩ : Σ i,V i)∈A∪Z)).card=a i*k) →
      (∀ C₀ i,(Finset.univ.filter (fun v : V i => (⟨i,v⟩ : Σ i,V i)∈R C₀)).card=a i) →
      (∀ U : Finset (Σ i,V i),Fintype.card {C₀ : C // R C₀=U} ≤ J) →
      (∀ C₀,b/(k:ℝ)^(c-1) ≤ w C₀ ∧ w C₀ ≤ B/(k:ℝ)^(c-1)) →
      (∀ v∈A∪Z,|1-hypergraphWeightedDegree R (inducedResourceWeight R w (insert v A)) v| ≤ η) →
      (∀ σ : ∀ i,FixedSubset (V i) (a i),profileRootSet σ⊆A∪Z →
        a₀*(k:ℝ)^(c*c) ≤ absorberGroundCount R S (profileRootSet σ) A) →
      ∃ D : Finset C,((∀ x∈D,∀ y∈D,x≠y → Disjoint (R x) (R y)) ∧ D.biUnion R=A∪Z) ∧
        ∀ C₀∈D,(R C₀∩Z).card ≤ 1 := by
  obtain ⟨ηf,hηf,kf,hf⟩ := profile_factor_on_subset a c J hc ha hsize S a₀ b B ha₀ hb hB
  refine ⟨ηf/2,by positivity,?_⟩
  intro q
  let K := (q:ℝ)*J*(c:ℝ)^(c-2)*B
  obtain ⟨N,hN⟩ := exists_nat_ge (2*K/ηf)
  refine ⟨max kf (max N 1),?_⟩
  intro k hk V _ _ C _ _ R w A Z hAZ hZ hY hR hJ hw herr habs
  have hkf : kf ≤ k := (le_max_left _ _).trans hk
  have hkN : N ≤ k := (le_max_left N 1).trans ((le_max_right _ _).trans hk)
  have hk1 : 1 ≤ k := (le_max_right N 1).trans ((le_max_right _ _).trans hk)
  have hkpos : (0:ℝ)<k := by exact_mod_cast (show 0<k by omega)
  have hsmall : K/(k:ℝ) ≤ ηf/2 := by
    have hh := hN.trans (show (N:ℝ) ≤ k by exact_mod_cast hkN)
    have hh' := (div_le_iff₀ hηf).mp hh
    apply (div_le_iff₀ hkpos).mpr
    nlinarith
  have hYcard : (A∪Z).card=c*k := by
    rw [sigma_finset_card]
    simp only [hY,← Finset.sum_mul,hsize]
  have hRC (C₀ : C) : (R C₀).card=c := by rw [sigma_finset_card];simp only [hR];exact hsize
  have hw0 (C₀ : C) : 0 ≤ w C₀ := (by positivity : (0:ℝ) ≤ b/(k:ℝ)^(c-1)).trans (hw C₀).1
  let P := fun C₀ => (R C₀∩Z).card ≤ 1
  let C' := {C₀ : C // P C₀}
  let R' := candidateResourceSet R P
  let w' := fun D : C' => w D.val
  have hdegree (v) : hypergraphWeightedDegree R' (inducedResourceWeight R' w' (A∪Z)) v=
      hypergraphWeightedDegree R (extensionResourceWeight R w A Z) v := by
    change hypergraphWeightedDegree (candidateResourceSet R P)
      (fun D => inducedResourceWeight R w (A∪Z) D.val) v=_
    rw [candidate_resource_degree]
    congr 1
    funext C₀
    by_cases hp : P C₀ <;> by_cases hs : R C₀⊆A∪Z <;>
      simp [hp,hs,inducedResourceWeight,extensionResourceWeight,P] at *
  have herr' (v) (hv : v∈A∪Z) :
      |1-hypergraphWeightedDegree R' (inducedResourceWeight R' w' (A∪Z)) v| ≤ ηf := by
    rw [hdegree]
    rcases Finset.mem_union.mp hv with hvA | hvZ
    · have hbase := herr v (Finset.mem_union_left _ hvA)
      rw [Finset.insert_eq_of_mem hvA] at hbase
      obtain ⟨hlo,hhi⟩ := extension_resource_degree_change R c J (by omega) hRC hJ w (B/(k:ℝ)^(c-1))
        (by positivity) (fun C₀ => ⟨hw0 C₀,(hw C₀).2⟩) A Z hAZ v hvA
      have hbound : (Z.card:ℝ)*((J:ℝ)*((A∪Z).card:ℝ)^(c-2)*(B/(k:ℝ)^(c-1))) ≤ K/k := by
        calc
          _ ≤ (q:ℝ)*((J:ℝ)*((A∪Z).card:ℝ)^(c-2)*(B/(k:ℝ)^(c-1))) :=
            mul_le_mul_of_nonneg_right (by exact_mod_cast hZ) (by positivity)
          _ = _ := by
            rw [hYcard,Nat.cast_mul,mul_pow]
            have hpow : (k:ℝ)^(c-1)=(k:ℝ)^(c-2)*k := by rw [← pow_succ];congr 1;omega
            rw [hpow]
            dsimp [K]
            field_simp
      have hdelta := hhi.trans (hbound.trans hsmall)
      have hbds := abs_le.mp hbase
      apply abs_le.mpr
      constructor <;> linarith
    · rw [extension_resource_root_degree R w A Z hAZ v hvZ]
      exact (herr v (Finset.mem_union_right _ hvZ)).trans (by linarith)
  have habs' (σ : ∀ i,FixedSubset (V i) (a i)) (hσ : profileRootSet σ⊆A∪Z) :
      a₀*(k:ℝ)^(c*c) ≤ absorberGroundCount R' S (profileRootSet σ) (A∪Z) :=
    (habs σ hσ).trans (absorber_extension_ground_count R S (profileRootSet σ) A (A∪Z) Z hAZ Finset.subset_union_left)
  have hfactor := hf k hkf V C' R' w' (A∪Z) hY (fun D i => hR D.val i)
    (candidate_resource_multiplicity R P J hJ) (fun D => hw D.val) herr' habs'
  exact candidate_resource_decomposition_lift R P (A∪Z) hfactor

end Oberwolfach

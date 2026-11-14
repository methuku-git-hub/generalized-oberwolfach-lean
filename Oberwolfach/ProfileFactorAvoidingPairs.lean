module

public import Oberwolfach.ProfileFactorExtraction
public import Oberwolfach.PairRestrictionScales

@[expose] public section

/-! A class-profile factor avoiding any bounded-degree set of displayed
endpoint pairs. It is extracted from the original weights and absorbers;
no factor-existence hypothesis or new weights are supplied. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option synthInstance.maxSize 256
set_option maxHeartbeats 4800000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I T : Type} [Fintype I] [DecidableEq I] [Nonempty I] [Fintype T] [DecidableEq T]

theorem profile_factor_avoiding_pairs (a : I → ℕ) (c J : ℕ) (hc : 3 ≤ c)
    (ha : ∀ i,1 ≤ a i) (hsize : ∑ i,a i=c)
    (S : T → VertexAbsorberTemplate c) (a₀ b B : ℝ)
    (ha₀ : 0 < a₀) (hb : 0 < b) (hB : 0 ≤ B) :
    ∃ η : ℝ,0 < η ∧ ∀ d : ℕ,∃ k₀ : ℕ,∀ k : ℕ,k₀ ≤ k →
      ∀ (V : I → Type) [∀ i,Fintype (V i)] [∀ i,DecidableEq (V i)]
        (C : Type) [Fintype C] [DecidableEq C],
      (∀ i,Fintype.card (V i)=a i*k) →
      ∀ (R : C → Finset (Σ i,V i)) (w : C → ℝ),
      (∀ C₀ i,(Finset.univ.filter (fun v : V i => (⟨i,v⟩ : Σ i,V i)∈R C₀)).card=a i) →
      (∀ Y : Finset (Σ i,V i),Fintype.card {C₀ : C // R C₀=Y} ≤ J) →
      (∀ C₀,b/(k:ℝ)^(c-1) ≤ w C₀ ∧ w C₀ ≤ B/(k:ℝ)^(c-1)) →
      (∀ v,|1-hypergraphWeightedDegree R w v| ≤ η) →
      (∀ σ : ∀ i,FixedSubset (V i) (a i),
        a₀*(k:ℝ)^(c*c) ≤ Fintype.card (LabelledAbsorberFamily R S (profileRootSet σ))) →
      ∀ E : Finset ((Σ i,V i)×(Σ i,V i)),
      (∀ e∈E,e.1≠e.2) → E.card ≤ c*k →
      (∀ v,(E.filter (fun e => v=e.1 ∨ v=e.2)).card ≤ d) →
      ∃ D : Finset C,
        ((∀ x∈D,∀ y∈D,x≠y → Disjoint (R x) (R y)) ∧ D.biUnion R=Finset.univ) ∧
        ∀ C₀∈D,∀ e∈E,¬(e.1∈R C₀ ∧ e.2∈R C₀) := by
  obtain ⟨ηf,hηf,kf,hf⟩ := profile_factor_extraction a c J hc ha hsize S (a₀/2) b B (by positivity) hb hB
  refine ⟨ηf/2,by positivity,?_⟩
  intro d
  let K := ((d:ℝ)+1)*(J:ℝ)*(c:ℝ)^(c-2)*B
  let L := absorberPairDeletionCoefficient c J (Fintype.card T) d
  have hK : 0 ≤ K := by dsimp [K];positivity
  have hL : 0 ≤ L := by dsimp [L,absorberPairDeletionCoefficient];positivity
  obtain ⟨N,hN⟩ := exists_nat_ge (max (2*K/ηf) (2*L/a₀))
  refine ⟨max kf (max N 1),?_⟩
  intro k hk V _ _ C _ _ hn R w hR hJ hw herr habs E hE hEsize hEd
  have hkf : kf ≤ k := (le_max_left _ _).trans hk
  have hkN : N ≤ k := (le_max_left N 1).trans ((le_max_right _ _).trans hk)
  have hk1 : 1 ≤ k := (le_max_right N 1).trans ((le_max_right _ _).trans hk)
  have hkpos : (0:ℝ)<k := by exact_mod_cast (show 0<k by omega)
  have hkNR : (N:ℝ) ≤ k := by exact_mod_cast hkN
  have hKsmall : K/(k:ℝ) ≤ ηf/2 := by
    have hh := (le_max_left (2*K/ηf) (2*L/a₀)).trans (hN.trans hkNR)
    have hh' := (div_le_iff₀ hηf).mp hh
    apply (div_le_iff₀ hkpos).mpr
    nlinarith
  have hLsmall : L ≤ (a₀/2)*k := by
    have hh := (le_max_right (2*K/ηf) (2*L/a₀)).trans (hN.trans hkNR)
    have hh' := (div_le_iff₀ ha₀).mp hh
    nlinarith
  have hnall : Fintype.card (Σ i,V i)=c*k := by
    simp only [Fintype.card_sigma,hn,← Finset.sum_mul,hsize]
  have hRC (C₀ : C) : (R C₀).card=c := by rw [sigma_finset_card];simp only [hR];exact hsize
  have hw0 (C₀ : C) : 0 ≤ w C₀ := (by positivity : (0:ℝ) ≤ b/(k:ℝ)^(c-1)).trans (hw C₀).1
  let P := fun C₀ => ∀ e : E,¬(e.val.1∈R C₀ ∧ e.val.2∈R C₀)
  let C' := {C₀ : C // P C₀}
  let R' := candidateResourceSet R P
  let w' := fun D : C' => w D.val
  have hR' (D : C') (i) :
      (Finset.univ.filter (fun v : V i => (⟨i,v⟩ : Σ i,V i)∈R' D)).card=a i := hR D.val i
  have hJ' : ∀ Y : Finset (Σ i,V i),Fintype.card {D : C' // R' D=Y} ≤ J :=
    candidate_resource_multiplicity R P J hJ
  have hw' (D : C') : b/(k:ℝ)^(c-1) ≤ w' D ∧ w' D ≤ B/(k:ℝ)^(c-1) := hw D.val
  have herr' (v : Σ i,V i) : |1-hypergraphWeightedDegree R' w' v| ≤ ηf := by
    obtain ⟨hlo,hhi⟩ := candidate_resource_pair_degree_loss_scale R c J hc hRC hJ w B k hB hkpos
      (by exact_mod_cast hnall) (fun C₀ => ⟨hw0 C₀,(hw C₀).2⟩) E hE v d (hEd v) (by simpa only [hnall] using hEsize)
    change _ ≤ K/k at hhi
    have hs := abs_le.mp (herr v)
    apply abs_le.mpr
    constructor
    all_goals change hypergraphWeightedDegree R w v-hypergraphWeightedDegree R' w' v ≤ K/k at hhi
    all_goals change 0 ≤ hypergraphWeightedDegree R w v-hypergraphWeightedDegree R' w' v at hlo
    all_goals linarith
  have habs' (σ : ∀ i,FixedSubset (V i) (a i)) :
      (a₀/2)*(k:ℝ)^(c*c) ≤ Fintype.card (LabelledAbsorberFamily R' S (profileRootSet σ)) := by
    have hX : (profileRootSet σ).card=c := (profileRootSet_card σ).trans hsize
    have hloss := candidate_absorber_pair_loss_scale (by omega : 2≤c) R S (profileRootSet σ) J hJ E hE d
      (fun v _ => hEd v) (by simpa only [hnall] using hEsize) k (by exact_mod_cast hnall) hX
    change (Fintype.card (LabelledAbsorberFamily R S (profileRootSet σ)):ℝ) ≤
      Fintype.card (LabelledAbsorberFamily R' S (profileRootSet σ))+L*(k:ℝ)^(c*c-1) at hloss
    have hpow : (k:ℝ)*(k:ℝ)^(c*c-1)=(k:ℝ)^(c*c) := by
      rw [← pow_succ']
      congr 1
      have hh : 1≤c*c := by nlinarith
      omega
    have hsmall : L*(k:ℝ)^(c*c-1) ≤ (a₀/2)*(k:ℝ)^(c*c) := by
      calc
        _ ≤ ((a₀/2)*k)*(k:ℝ)^(c*c-1) := mul_le_mul_of_nonneg_right hLsmall (by positivity)
        _ = _ := by rw [mul_assoc,hpow]
    linarith [habs σ]
  have hfactor := hf k hkf V C' hn R' w' hR' hJ' hw' herr' habs'
  obtain ⟨D,hD,hP⟩ := candidate_resource_decomposition_lift R P Finset.univ hfactor
  exact ⟨D,hD,fun C₀ hC e he => hP C₀ hC ⟨e,he⟩⟩

end Oberwolfach

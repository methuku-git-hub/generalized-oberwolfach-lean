module

public import Oberwolfach.ProfileExtensionFactor
public import Oberwolfach.LocalPairRestrictionScales

@[expose] public section

/-! The enlarged-set factor can avoid the displayed edges of an earlier
factor. Both the local free-vertex condition and original weights survive. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option synthInstance.maxSize 256
set_option maxHeartbeats 4200000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I T : Type} [Fintype I] [DecidableEq I] [Nonempty I] [Fintype T] [DecidableEq T]

theorem profile_extension_avoiding_pairs (a : I → ℕ) (c J : ℕ) (hc : 3 ≤ c)
    (ha : ∀ i,1 ≤ a i) (hsize : ∑ i,a i=c)
    (S : T → VertexAbsorberTemplate c) (a₀ b B : ℝ)
    (ha₀ : 0 < a₀) (hb : 0 < b) (hB : 0 ≤ B) :
    ∃ η : ℝ,0 < η ∧ ∀ q d : ℕ,∃ k₀ : ℕ,∀ k : ℕ,k₀ ≤ k →
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
      ∀ E : Finset ((Σ i,V i)×(Σ i,V i)),
      (∀ e∈E,e.1≠e.2) → E.card ≤ A.card →
      (∀ v,(E.filter (fun e => v=e.1 ∨ v=e.2)).card ≤ d) →
      ∃ D : Finset C,((∀ x∈D,∀ y∈D,x≠y → Disjoint (R x) (R y)) ∧ D.biUnion R=A∪Z) ∧
        (∀ C₀∈D,(R C₀∩Z).card ≤ 1) ∧
        ∀ C₀∈D,∀ e∈E,¬(e.1∈R C₀ ∧ e.2∈R C₀) := by
  obtain ⟨ηe,hηe,hext⟩ := profile_extension_factor a c J hc ha hsize S (a₀/2) b B (by positivity) hb hB
  refine ⟨ηe/2,by positivity,?_⟩
  intro q d
  obtain ⟨ke,hfactor⟩ := hext q
  let K := ((d:ℝ)+1)*J*((c:ℝ)+1)^(c-2)*B
  let L := absorberPairDeletionCoefficient c J (Fintype.card T) d
  obtain ⟨N,hN⟩ := exists_nat_ge (max (2*K/ηe) (2*L/a₀))
  refine ⟨max ke (max N 1),?_⟩
  intro k hk V _ _ C _ _ R w A Z hAZ hZ hY hR hJ hw herr habs E hE hsizeE hEd
  have hke : ke ≤ k := (le_max_left _ _).trans hk
  have hkN : N ≤ k := (le_max_left N 1).trans ((le_max_right _ _).trans hk)
  have hk1 : 1 ≤ k := (le_max_right N 1).trans ((le_max_right _ _).trans hk)
  have hkpos : (0:ℝ)<k := by exact_mod_cast (show 0<k by omega)
  have hkR : (N:ℝ) ≤ k := by exact_mod_cast hkN
  have hKsmall : K/(k:ℝ) ≤ ηe/2 := by
    have hh := (le_max_left (2*K/ηe) (2*L/a₀)).trans (hN.trans hkR)
    have hh' := (div_le_iff₀ hηe).mp hh
    apply (div_le_iff₀ hkpos).mpr
    nlinarith
  have hLsmall : L ≤ (a₀/2)*k := by
    have hh := (le_max_right (2*K/ηe) (2*L/a₀)).trans (hN.trans hkR)
    have hh' := (div_le_iff₀ ha₀).mp hh
    nlinarith
  have hYcard : (A∪Z).card=c*k := by
    rw [sigma_finset_card]
    simp only [hY,← Finset.sum_mul,hsize]
  have hA : A.card ≤ c*k := by rw [← hYcard];exact Finset.card_le_card Finset.subset_union_left
  have hRC (C₀ : C) : (R C₀).card=c := by rw [sigma_finset_card];simp only [hR];exact hsize
  have hw0 (C₀ : C) : 0 ≤ w C₀ := (by positivity : (0:ℝ) ≤ b/(k:ℝ)^(c-1)).trans (hw C₀).1
  let P := fun C₀ => ∀ e : E,¬(e.val.1∈R C₀ ∧ e.val.2∈R C₀)
  let C' := {C₀ : C // P C₀}
  let R' := candidateResourceSet R P
  let w' := fun D : C' => w D.val
  have herr' (v) (hv : v∈A∪Z) :
      |1-hypergraphWeightedDegree R' (inducedResourceWeight R' w' (insert v A)) v| ≤ ηe := by
    have hlocal : ((insert v A).card:ℝ) ≤ ((c:ℝ)+1)*k := by
      have hcard := (Finset.card_insert_le v A).trans (Nat.add_le_add_right hA 1)
      have hcardR : ((insert v A).card:ℝ) ≤ (c:ℝ)*k+1 := by exact_mod_cast hcard
      have hkR' : (1:ℝ) ≤ k := by exact_mod_cast hk1
      nlinarith
    obtain ⟨hlo,hhi⟩ := candidate_resource_local_pair_degree_loss_scale R c J hc hRC hJ w B k (c+1) hB hkpos
      (by positivity) (insert v A) hlocal (fun C₀ => ⟨hw0 C₀,(hw C₀).2⟩) E hE v d (hEd v)
      (hsizeE.trans (Finset.card_le_card (Finset.subset_insert _ _)))
    rw [candidate_resource_induced_pair_degree R w E (insert v A) v]
    change _ ≤ K/k at hhi
    have hs := abs_le.mp (herr v hv)
    have hd := hhi.trans hKsmall
    apply abs_le.mpr
    constructor <;> linarith
  have habs' (σ : ∀ i,FixedSubset (V i) (a i)) (hσ : profileRootSet σ⊆A∪Z) :
      (a₀/2)*(k:ℝ)^(c*c) ≤ absorberGroundCount R' S (profileRootSet σ) A := by
    have hX : (profileRootSet σ).card=c := (profileRootSet_card σ).trans hsize
    have hloss := candidate_absorber_ground_pair_loss_scale (by omega : 2≤c) R S (profileRootSet σ) A J hJ E hE d
      (fun v _ => hEd v) hsizeE k hkpos.le (by exact_mod_cast hA) hX
    change absorberGroundCount R S (profileRootSet σ) A ≤
      absorberGroundCount R' S (profileRootSet σ) A+L*(k:ℝ)^(c*c-1) at hloss
    have hp : (k:ℝ)*(k:ℝ)^(c*c-1)=(k:ℝ)^(c*c) := by
      rw [← pow_succ'];congr 1
      have hh : 1≤c*c := by nlinarith
      omega
    have hl : L*(k:ℝ)^(c*c-1) ≤ (a₀/2)*(k:ℝ)^(c*c) := by
      calc
        _ ≤ ((a₀/2)*k)*(k:ℝ)^(c*c-1) := mul_le_mul_of_nonneg_right hLsmall (by positivity)
        _ = _ := by rw [mul_assoc,hp]
    linarith [habs σ hσ]
  obtain ⟨D,⟨hD,hcover⟩,hcap⟩ := hfactor k hke V C' R' w' A Z hAZ hZ hY
    (fun D i => hR D.val i) (candidate_resource_multiplicity R P J hJ) (fun D => hw D.val) herr' habs'
  refine ⟨D.image Subtype.val,⟨?_,?_⟩,?_,?_⟩
  · intro x hx y hy hxy
    obtain ⟨x',hx',rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨y',hy',rfl⟩ := Finset.mem_image.mp hy
    exact hD x' hx' y' hy' (fun hh => hxy (congrArg Subtype.val hh))
  · rw [Finset.image_biUnion]
    exact hcover
  · intro C₀ hC
    obtain ⟨D₀,hD₀,rfl⟩ := Finset.mem_image.mp hC
    exact hcap D₀ hD₀
  · intro C₀ hC e he
    obtain ⟨D₀,_,rfl⟩ := Finset.mem_image.mp hC
    exact D₀.property ⟨e,he⟩

end Oberwolfach

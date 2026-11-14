module

public import Oberwolfach.ProfileAbsorberReservoir
public import Oberwolfach.ProfileMarginalCorrection
public import Oberwolfach.ProfileFractionalFactor
public import Oberwolfach.ProfileRestrictionCounts
public import Oberwolfach.AbsorberRestrictionScales
public import Oberwolfach.ResourceAbsorptionCompletion

@[expose] public section

/-! Exact factor extraction from the original class-profile weights and
labelled absorbers. The error tolerance is fixed before the reservoir
and matching accuracies; no factor-existence input is assumed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 256
set_option maxHeartbeats 4800000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I T : Type} [Fintype I] [DecidableEq I] [Nonempty I] [Fintype T] [DecidableEq T]

theorem profile_factor_extraction (a : I → ℕ) (c J : ℕ) (hc : 3 ≤ c)
    (ha : ∀ i,1 ≤ a i) (hsize : ∑ i,a i=c)
    (S : T → VertexAbsorberTemplate c) (a₀ b B : ℝ)
    (ha₀ : 0 < a₀) (hb : 0 < b) (hB : 0 ≤ B) :
    ∃ η : ℝ,0 < η ∧ ∃ k₀ : ℕ,∀ k : ℕ,k₀ ≤ k →
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
      HasResourceDecomposition R Finset.univ := by
  let b' := b/(2:ℝ)^(c-1)
  have hb' : 0 < b' := by dsimp [b'];positivity
  obtain ⟨ηcor,hηcor,hcor⟩ := profile_marginal_correction a c J (by omega) ha hsize S
    (a₀/2) b' B (by positivity) hb'
  let D := absorberVertexDeletionCoefficient c J (Fintype.card T)
  let K := B*J*(c:ℝ)^(c-2)
  have hD : 0 ≤ D := by dsimp [D,absorberVertexDeletionCoefficient];positivity
  have hK : 0 ≤ K := by dsimp [K];positivity
  let δ := min (1/4:ℝ) (min (a₀/(4*(D+1))) (ηcor/(4*(K+1))))
  have hδ : 0 < δ := by dsimp [δ];positivity
  have hδ1 : δ ≤ 1/4 := min_le_left _ _
  have hδD : δ*D ≤ a₀/2 := by
    have hh : δ ≤ a₀/(4*(D+1)) := (min_le_right _ _).trans (min_le_left _ _)
    have hh' := (le_div_iff₀ (by positivity : (0:ℝ)<4*(D+1))).mp hh
    nlinarith
  have hδK : δ*K ≤ ηcor/4 := by
    have hh : δ ≤ ηcor/(4*(K+1)) := (min_le_right _ _).trans (min_le_right _ _)
    have hh' := (le_div_iff₀ (by positivity : (0:ℝ)<4*(K+1))).mp hh
    nlinarith
  obtain ⟨γ,hγ,n₁,hn₁⟩ := profile_absorber_reservoir a c J (by omega) hsize S a₀ δ ha₀ hδ
  obtain ⟨n₂,hn₂⟩ := profile_fractional_factor a c J (by omega) ha hsize
    (B+b'/2) γ (by positivity) hγ
  refine ⟨ηcor/4,by positivity,max n₁ (2*max n₂ 2),?_⟩
  intro k hk V _ _ C _ _ hn R w hR hJ hw herr habs
  have hkn₁ : n₁ ≤ k := (le_max_left _ _).trans hk
  have hkN : 2*max n₂ 2 ≤ k := (le_max_right _ _).trans hk
  have hk0 : 0 < k := by omega
  have hkR : (0:ℝ)<k := by exact_mod_cast hk0
  have hnall : Fintype.card (Σ i,V i)=c*k := by
    simp only [Fintype.card_sigma,hn,← Finset.sum_mul,hsize]
  have hRC (C₀ : C) : (R C₀).card=c := by rw [sigma_finset_card];simp only [hR];exact hsize
  have hw0 (C₀ : C) : 0 ≤ w C₀ := (by positivity : (0:ℝ) ≤ b/(k:ℝ)^(c-1)).trans (hw C₀).1
  have hpair (u v : Σ i,V i) (huv : u≠v) :
      (∑ C₀,if u∈R C₀ ∧ v∈R C₀ then w C₀ else 0) ≤ K/k :=
    uniform_resource_pair_weight R c J (by omega) hRC hJ w B k hB hkR
      (by exact_mod_cast hnall) (fun C₀ => (hw C₀).2) u v huv
  obtain ⟨Z,q₀,hZ,hZprofile,_,habsZ⟩ := hn₁ k hkn₁ V C hn R hR hJ habs
  have hZcard : Z.card=c*q₀ := by
    rw [sigma_finset_card];simp only [hZprofile,← Finset.sum_mul,hsize]
  have hq₀ : q₀ ≤ Z.card := by rw [hZcard];nlinarith
  have hqhalf : 2*q₀ ≤ k := by
    have hh : (q₀:ℝ) ≤ Z.card := by exact_mod_cast hq₀
    have hkδ : δ*k ≤ (k:ℝ)/4 := by nlinarith
    have hhalf : (2:ℝ)*q₀ ≤ k := by linarith
    exact_mod_cast hhalf
  have hqk : q₀ ≤ k := by omega
  let k' := k-q₀
  have hk'2 : 2 ≤ k' := by dsimp [k'];omega
  have hk'n₂ : n₂ ≤ k' := by dsimp [k'];omega
  have hk'0 : (0:ℝ)<k' := by exact_mod_cast (show 0<k' by omega)
  have hk'k : k' ≤ k := Nat.sub_le _ _
  have hk'kR : (k':ℝ) ≤ k := by exact_mod_cast hk'k
  have hhalfR : (k:ℝ) ≤ 2*k' := by
    have hh : k ≤ 2*k' := by dsimp [k'];omega
    exact_mod_cast hh
  let V' := ProfileRemainingClass Z
  let e := profileComplementEmbedding Z
  let C' := RestrictedResource R e
  let R' := restrictedResourceSet R e
  let w' (D : C') := w D.val
  have hn' (i) : Fintype.card (V' i)=a i*k' := profileRemainingClass_profile a k q₀ Z hn hZprofile i
  have hR' (D : C') (i) :
      (Finset.univ.filter (fun v : V' i => (⟨i,v⟩ : Σ i,V' i)∈R' D)).card=a i :=
    (profile_restricted_resource_class_card R Z D i).trans (hR D.val i)
  have hJ' : ∀ Y : Finset (Σ i,V' i),Fintype.card {D : C' // R' D=Y} ≤ J :=
    restricted_resource_multiplicity R e J hJ
  have hw' (D : C') : b'/(k':ℝ)^(c-1) ≤ w' D ∧ w' D ≤ B/(k':ℝ)^(c-1) :=
    restricted_individual_weight_scale (c-1) b B k k' (w D.val) hb.le hB hk'0 hk'kR hhalfR (hw D.val)
  have herr' (i) (v : V' i) : |1-hypergraphWeightedDegree R' w' ⟨i,v⟩| ≤ ηcor := by
    have hx : e ⟨i,v⟩∉Z := (profileComplementEmbedding_range Z _).mp ⟨⟨i,v⟩,rfl⟩
    have hh := resource_vertex_deletion_load_error R w hw0 (K/k) (ηcor/4)
      (by positivity) hpair herr Z (e ⟨i,v⟩) hx
    have hZK : (Z.card:ℝ)*(K/k) ≤ δ*K := by
      have hl := mul_le_mul_of_nonneg_right hZ (show 0 ≤ K/k by positivity)
      have heq : (δ*k)*(K/k)=δ*K := by field_simp
      rwa [heq] at hl
    change |1-hypergraphWeightedDegree (restrictedResourceSet R (profileComplementEmbedding Z))
      (fun D => w D.val) ⟨i,v⟩| ≤ ηcor
    rw [profile_restricted_resource_degree]
    linarith
  have habs' (σ : ∀ i,FixedSubset (V' i) (a i)) :
      ∃ A : Finset (LabelledAbsorberFamily R' S (profileRootSet σ)),
        (a₀/2)*(k':ℝ)^(c*c) ≤ A.card := by
    let X := profileRootSet σ
    have hX : X.card=c := (profileRootSet_card σ).trans hsize
    have hXold (i : I) : (Finset.univ.filter (fun v : V i => (⟨i,v⟩ : Σ i,V i)∈X.image e)).card=a i :=
      (profileComplementEmbedding_class_card Z X i).trans (profileRootSet_class_card σ i)
    obtain ⟨τ,hτ⟩ := exists_profile_root_of_class_sizes a (X.image e) hXold
    have hparent : a₀*(k:ℝ)^(c*c) ≤ Fintype.card (LabelledAbsorberFamily R S (X.image e)) := by
      simpa only [hτ] using habs τ
    have hh := restricted_absorber_abundance (by omega : 1≤c) R e S X Z
      (profileComplementEmbedding_range Z) J hJ k k' a₀ δ hkR hk'0.le hk'kR ha₀.le
      (by exact_mod_cast hnall) hX hZ hδD hparent
    exact ⟨Finset.univ,by simpa only [Finset.card_univ] using hh⟩
  obtain ⟨ψ,hψ,hψbounds⟩ := hcor V' C' k' ηcor (by exact_mod_cast hk'2) hηcor.le le_rfl
    (fun i => by exact_mod_cast hn' i) R' w' hR' hJ' hw' herr' habs'
  obtain ⟨M,hMM,hleft,hMcard,hleftprofile⟩ := hn₂ k' hk'n₂ V' C' hn' R' ψ hR' hJ'
    (fun D => ⟨(by positivity : (0:ℝ) ≤ (b'/2)/(k':ℝ)^(c-1)).trans (hψbounds D).1,(hψbounds D).2⟩) hψ
  let W := Finset.univ\M.biUnion R'
  have hW : ((W.image e).card:ℝ) ≤ γ*k := by
    rw [Finset.card_image_of_injective _ e.injective]
    exact hleft.trans (mul_le_mul_of_nonneg_left hk'kR hγ.le)
  have hWZ : Disjoint (W.image e) Z := profileComplementEmbedding_image_disjoint Z W
  have hWp (i : I) :
      (Finset.univ.filter (fun v : V i => (⟨i,v⟩ : Σ i,V i)∈W.image e)).card=a i*(k'-M.card) :=
    (profileComplementEmbedding_class_card Z W i).trans (hleftprofile i)
  have hfinish := habsZ (W.image e) (k'-M.card) hW hWZ hWp
  exact resource_restriction_absorption_completion R e Z (profileComplementEmbedding_range Z) M hMM hfinish

end Oberwolfach

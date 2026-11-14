module

public import Oberwolfach.EndpointPairedAbsorbers
public import Oberwolfach.HubNeighbourClasses
public import Oberwolfach.HubFactorWeightScales

@[expose] public section

/-! Exact endpoint-triangle factors from the actual row/index extension
bounds and positive incident weights. The paired absorber count is constructed
inside the proof; it is not an additional assumption. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 512
set_option maxHeartbeats 5000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem endpoint_triangle_factor (γ b B : ℝ) (hγ : 0<γ) (hb : 0<b) (hB : 0≤B) :
    ∃ ε η : ℝ,0<ε ∧ 0<η ∧ ∃ N : ℕ,
      ∀ (A : Type) [Fintype A] [DecidableEq A],N≤Fintype.card A →
      ∀ (Q F : SimpleGraph A) (S T : Finset A),Disjoint S T → S.card=2*T.card →
      (∀ v,(F.degree v:ℝ)≤ε*Fintype.card A) →
      EndpointNeighbourCounts Q F S T (γ*Fintype.card A) →
      ∀ wt : EndpointTriangle Q F S T→ℝ,
      (∀ C,b/(Fintype.card A:ℝ)^2≤wt C ∧ wt C≤B/(Fintype.card A:ℝ)^2) →
      (∀ v∈S∪T,|1-hypergraphWeightedDegree endpointTriangleVertices wt v|≤η) →
      HasResourceDecomposition (endpointTriangleVertices (Q:=Q) (F:=F) (S:=S) (T:=T)) (S∪T) := by
  let β := ordinaryLocalCountCoeff 2 γ
  have hβ : 0<β := ordinaryLocalCountCoeff_pos 2 γ hγ
  let a := (β/2)^4
  have ha : 0<a := by dsimp [a];positivity
  let α := a*3^9
  have hα : 0<α := by dsimp [α];positivity
  let Templates : Unit→VertexAbsorberTemplate 3 := fun _=>pairedAbsorberTemplate 3
  obtain ⟨η,hη,k₀,hfactor⟩ := supported_profile_factor_extraction (twoClassProfile 2) 3 1
    (by norm_num) (by intro i;cases i <;> norm_num [twoClassProfile]) (twoClassProfile_sum 2)
    Templates α (b*γ^2) B hα (by positivity) hB
  obtain ⟨Na,hNa⟩ := paired_absorber_order_threshold 2 β hβ
  obtain ⟨N₁,hN₁⟩ := exists_nat_gt (max (24/γ) ((k₀:ℝ)/γ))
  let ε := γ/24
  have hε : 0<ε := by dsimp [ε];positivity
  refine ⟨ε,η,hε,hη,max Na (max N₁ 1),?_⟩
  intro A _ _ hn Q F S T hST hratio hF hcommon wt hw herr
  let n : ℝ := Fintype.card A
  let H₀ : A→Unit→Prop := fun v _=>v∈S
  let H₁ : A→Unit→Prop := fun v _=>v∈T
  have hd (v : A) : ¬(H₀ v () ∧ H₁ v ()) := fun h=>Finset.disjoint_left.mp hST h.1 h.2
  let V := hubNeighbourClass H₀ H₁ ()
  let e := hubNeighbourEmbedding H₀ H₁ () hd
  let k := T.card
  let C := EndpointTriangle Q F S T
  let R : C→Finset A := endpointTriangleVertices
  have heimage : Finset.univ.image e=S∪T := by
    rw [hubNeighbourEmbedding_image]
    ext v;simp [H₀,H₁]
  have hnpos : 0<n := by
    have hh : 1≤Fintype.card A := (le_max_right N₁ 1).trans ((le_max_right Na _).trans hn)
    dsimp [n];exact_mod_cast hh
  have hNn : (N₁:ℝ)≤n := by
    dsimp [n]
    exact_mod_cast (le_max_left N₁ 1).trans ((le_max_right Na _).trans hn)
  have hlarge : 24≤γ*n := by
    have hh := (div_le_iff₀ hγ).mp ((le_max_left _ _).trans (hN₁.le.trans hNn))
    linarith only [hh]
  have hbudget : 6*(ε*n+1)≤γ/2*n := by dsimp [ε];nlinarith only [hlarge]
  have hsize : γ*n≤(k:ℝ) := hcommon.indices
  have hkpos : (0:ℝ)<k := (mul_pos hγ hnpos).trans_le hsize
  have hk₀ : k₀≤k := by
    have hh := (div_le_iff₀ hγ).mp ((le_max_right _ _).trans (hN₁.le.trans hNn))
    exact_mod_cast (show (k₀:ℝ)≤k from by linarith only [hh,hsize])
  have hkn : (k:ℝ)≤n := by dsimp [k,n];exact_mod_cast Finset.card_le_univ T
  have hclasscard (i : Bool) : Fintype.card (V i)=(if i then T else S).card := by
    have heq (v : A) : (if i then H₁ v () else H₀ v ()) ↔ v∈(if i then T else S) := by
      cases i <;> rfl
    convert (Fintype.card_congr (Equiv.subtypeEquivRight heq)).trans (Fintype.card_coe _) using 1 <;> congr!
  have hclasses (i : Bool) : Fintype.card (V i)=twoClassProfile 2 i*k := by
    rw [hclasscard]
    cases i <;> simp [twoClassProfile,k,hratio]
  have hsupp (c : C) (v : A) (hv : v∈R c) : ∃ z,e z=v := by
    have hh := c.property.1 hv
    rw [← heimage] at hh
    simpa only [Finset.mem_image,Finset.mem_univ,true_and] using hh
  have hprofile (c : C) (i : Bool) :
      (Finset.univ.filter (fun v : V i=>e ⟨i,v⟩∈R c)).card=twoClassProfile 2 i := by
    have hh : (Finset.univ.filter (fun v : V i=>e ⟨i,v⟩∈R c)).card=
        (c.val∩(if i then T else S)).card := by
      apply Finset.card_bij (fun v _=>v.val)
      · intro v hv;exact Finset.mem_inter.mpr ⟨(Finset.mem_filter.mp hv).2,by cases i <;> exact v.property⟩
      · intro v _ w _ h;exact Subtype.ext h
      · intro v hv
        exact ⟨⟨v,by cases i <;> exact (Finset.mem_inter.mp hv).2⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_inter.mp hv).1⟩,rfl⟩
    cases i
    · exact hh.trans c.property.2.1
    · exact hh.trans c.property.2.2.1
  have hwt (c : C) : (b*γ^2)/(k:ℝ)^(3-1)≤wt c ∧ wt c≤B/(k:ℝ)^(3-1) :=
    hub_factor_weight_scale 2 n k γ b B (wt c) hnpos hkpos hγ hb.le hB hkn hsize (hw c)
  have herr' (v : Σ i,V i) : |1-hypergraphWeightedDegree R wt (e v)|≤η := by
    apply herr
    rw [← heimage]
    exact Finset.mem_image.mpr ⟨v,Finset.mem_univ _,rfl⟩
  have hresult := hfactor k hk₀ V A C hclasses e R wt hsupp hprofile
    (endpointTriangle_multiplicity Q F S T) hwt herr' (by
      intro σ
      obtain ⟨x,hx,hxset,hxT,hxS⟩ := exists_twoClass_root_order σ
      have hroot (i : Fin 3) : e (x i)∈endpointBaseClass S T i.val := by
        refine Fin.cases ?_ (fun j=>?_) i
        · have hh := (embedded_class_image_iff e true (x 0)).mpr hxT
          obtain ⟨z,hz⟩ := hh
          exact hz ▸ z.property
        · have hh := (embedded_class_image_iff e false (x j.succ)).mpr (hxS j)
          obtain ⟨z,hz⟩ := hh
          simpa [endpointBaseClass] using (hz ▸ z.property)
      have hcounts := hNa _ ((le_max_left Na _).trans hn)
      have habs := endpoint_paired_absorber_count Q F S T hST γ (ε*n) hγ (by positivity)
        hF hcommon hbudget (by norm_num at hcounts ⊢;exact hcounts.1)
        (by norm_num at hcounts ⊢;exact hcounts.2) (fun i=>e (x i)) (e.injective.comp hx) hroot
      have hrootset : Finset.univ.image (fun i=>e (x i))=(profileRootSet σ).image e := by
        rw [← hxset,Finset.image_image];rfl
      rw [hrootset] at habs
      have h3k : 3*(k:ℝ)≤n := by
        have hh : 3*k≤Fintype.card A := by
          have hh' := Finset.card_le_univ (S∪T)
          rw [Finset.card_union_of_disjoint hST,hratio] at hh';dsimp [k];omega
        dsimp [n];exact_mod_cast hh
      have hscale : α*(k:ℝ)^9≤a*n^9 := by
        calc
          _ = a*(3*(k:ℝ))^9 := by dsimp [α];rw [mul_pow];ring
          _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) h3k _) ha.le
      let embed : LabelledCycleRecord R (pairedAbsorberTemplate 3).val ((profileRootSet σ).image e)→
          LabelledAbsorberFamily R Templates ((profileRootSet σ).image e) := fun D=>⟨(),D⟩
      have hi : Function.Injective embed := by
        intro D E he;exact eq_of_heq (Sigma.mk.inj_iff.mp he).2
      exact (hscale.trans habs).trans (by exact_mod_cast Fintype.card_le_of_injective embed hi))
  convert hresult using 1
  exact heimage.symm

end Oberwolfach

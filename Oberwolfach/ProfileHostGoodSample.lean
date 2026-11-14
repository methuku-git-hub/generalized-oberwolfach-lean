module

public import Oberwolfach.ProfileHostVertexTail
public import Oberwolfach.ProfileHostAbsorberTail
public import Oberwolfach.ProfileCommonSamplingEvents
public import Oberwolfach.EmbeddedProfileSeparation

@[expose] public section

/-! One sample satisfying every required original-weight vertex sum,
every eligible labelled-absorber count, and all forbidden-pair tests.
The event is chosen once, before either of the two factors is constructed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option synthInstance.maxSize 256
set_option maxHeartbeats 4400000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {s : ℕ} {V : Fin s → Type*} [∀ i,Fintype (V i)] [∀ i,DecidableEq (V i)]
    {C Tpl : Type*} [Fintype C] [DecidableEq C] [Fintype Tpl] [DecidableEq Tpl]

theorem profile_host_good_sample
    (a : Fin s → ℕ) (ha : ∀ i,1≤a i) (c J : ℕ) (hc : 2≤c) (hJpos : 1≤J) (hs : ∑ i,a i=c)
    (R : C → Finset (Σ i,V i)) (w : C → ℝ) (S : Tpl → VertexAbsorberTemplate c)
    (hR : ∀ C₀ i,(Finset.univ.filter (fun v : V i => (⟨i,v⟩ : Σ i,V i)∈R C₀)).card=a i)
    (hJ : ∀ Y : Finset (Σ i,V i),Fintype.card {C₀ : C // R C₀=Y}≤J)
    (k F₀ D B α η ξ : ℝ) (hk : 0<k) (hB : 0<B) (hα : 0≤α) (hη : 0≤η) (hξ : 0≤ξ)
    (hn : ∀ i,(Fintype.card (V i):ℝ)=a i*k)
    (hw : ∀ C₀,0≤w C₀ ∧ w C₀≤B/k^(c-1))
    (herr : ∀ v,|1-hypergraphWeightedDegree R w v|≤η)
    (hcount : ∀ σ : ∀ i,FixedSubset (V i) (a i),α*k^(c*c)≤Fintype.card (LabelledAbsorberFamily R S (profileRootSet σ)))
    (F Z : Finset (Σ i,V i)) (hF : (F.card:ℝ)≤F₀) (q : ℕ) (hZ : Z.card≤c*q)
    (t : ℕ) (ht : c+c*c≤t) (hfeas : 2*(t:ℝ)≤k) (hFhalf : 2*F₀≤k)
    (hlargeV : 2*(c-1:ℕ)*(F₀+1+(c-1:ℕ))≤k)
    (hlargeR : 2*(c*c:ℕ)*(F₀+c+(c*c:ℕ))≤k)
    (hmarginV : (η+F₀*(B*J*(c:ℝ)^(c-2)/k))+
      (1+η+F₀*(B*J*(c:ℝ)^(c-2)/k))*
        (2*(c-1:ℕ)*(((1:ℝ)+(c-1:ℕ))/t+(F₀+1+(c-1:ℕ))/k))≤ξ)
    (hmarginR : 2*(c*c:ℕ)*(((c:ℝ)+(c*c:ℕ))/t+(F₀+c+(c*c:ℕ))/k)≤1/4)
    (hloss : 4*(F₀+c)*absorberVertexDeletionCoefficient c J (Fintype.card Tpl)≤α*k)
    (E : Finset ((Σ i,V i)×(Σ i,V i))) (hE : ∀ e∈E,e.1≠e.2) (hEsize : (E.card:ℝ)≤D*k)
    (hsep : 4*D*(t:ℝ)^2/k≤1/4)
    (hunion :
      (2*Real.exp (-(2*ξ^2/((c:ℝ)*(2*(J:ℝ)*(2*(c:ℝ)+1)^(c-2)*B)^2))*(t:ℝ)))*(c*(t+q):ℕ)+
      (2*Real.exp (-(2*(α/4)^2/((c:ℝ)*(1+2*((c*c)*Fintype.card Tpl*c^c*J^(2*c+1):ℕ)*((c:ℝ)+1)^(c*c-1))^2))*(t:ℝ)))*
        ((c*(t+q):ℕ):ℝ)^c≤1/4) :
    ∃ A : Finset (Σ i,V i),Disjoint A F ∧
      (∀ i,(Finset.univ.filter (fun v : V i => (⟨i,v⟩ : Σ i,V i)∈A)).card=a i*t) ∧
      (∀ v∈A∪Z,|1-hypergraphWeightedDegree R
        (inducedResourceWeight R (fun C₀ => (k/(t:ℝ))^(c-1)*w C₀) (insert v A)) v|≤2*ξ) ∧
      (∀ σ : ∀ i,FixedSubset (V i) (a i),profileRootSet σ⊆A∪Z →
        (α/4)*(t:ℝ)^(c*c)≤absorberGroundCount R S (profileRootSet σ) A) ∧
      ∀ e∈E,¬(e.1∈A ∧ e.2∈A) := by
  have hm := profile_remaining_sample_feasible a ha k F₀ t hk hfeas hFhalf hn F hF
  letI : ∀ i,Nonempty (FixedSubset (ProfileRemainingClass F i) (a i*t)) := fun i => fixedSubset_nonempty (hm i)
  let μ := FiniteLaw.pi (fun i => FiniteLaw.uniform (FixedSubset (ProfileRemainingClass F i) (a i*t)))
  let A := fun τ : ∀ i,FixedSubset (ProfileRemainingClass F i) (a i*t) =>
    (profileRootSet τ).map (profileComplementEmbedding F)
  let Y := fun τ => A τ∪Z
  let wt := fun C₀ => (k/(t:ℝ))^(c-1)*w C₀
  let εv := 2*Real.exp (-(2*ξ^2/((c:ℝ)*(2*(J:ℝ)*(2*(c:ℝ)+1)^(c-2)*B)^2))*(t:ℝ))
  let εr := 2*Real.exp (-(2*(α/4)^2/((c:ℝ)*(1+2*((c*c)*Fintype.card Tpl*c^c*J^(2*c+1):ℕ)*((c:ℝ)+1)^(c*c-1))^2))*(t:ℝ))
  let BadV := fun v τ => 2*ξ< |1-hypergraphWeightedDegree R (inducedResourceWeight R wt (insert v (A τ))) v|
  let BadR := fun (σ : ∀ i,FixedSubset (V i) (a i)) τ =>
    absorberGroundCount R S (profileRootSet σ) (A τ)<(α/4)*(t:ℝ)^(c*c)
  let BadE := fun τ => ∃ e∈E,e.1∈A τ ∧ e.2∈A τ
  have hAc (τ : ∀ i,FixedSubset (ProfileRemainingClass F i) (a i*t)) : (A τ).card=c*t := by
    dsimp [A]
    rw [Finset.card_map,profileRootSet_card,← Finset.sum_mul,hs]
  have hM (τ : ∀ i,FixedSubset (ProfileRemainingClass F i) (a i*t)) : (Y τ).card≤c*(t+q) := by
    apply (Finset.card_union_le _ _).trans
    rw [hAc,Nat.mul_add]
    exact Nat.add_le_add_left hZ _
  have hV (v : Σ i,V i) : μ.probability (fun τ => v∈Y τ ∧ BadV v τ)≤εv*μ.probability (fun τ => v∈Y τ) :=
    profile_host_vertex_tail a ha c J hc hJpos hs R w hR hJ k F₀ B η ξ hk hB hη hξ hn hw herr F Z hF t
      (by omega) hm hlargeV hmarginV v
  have hRoots (σ : ∀ i,FixedSubset (V i) (a i)) :
      μ.probability (fun τ => profileRootSet σ⊆Y τ ∧ BadR σ τ)≤εr*μ.probability (fun τ => profileRootSet σ⊆Y τ) :=
    profile_host_absorber_tail a ha c J (by omega) hs R S hR hJ k F₀ α hk hα hn F Z (profileRootSet σ) hF
      ((profileRootSet_card σ).trans hs) (hcount σ) t ht hm hlargeR hmarginR hloss
  have hOther : μ.probability BadE≤4*D*(t:ℝ)^2/k :=
    profile_remaining_forbidden_pairs_probability a ha k F₀ t D hk (by positivity) hFhalf hn F hF
      (fun i => a i*t) hm (fun i => by simp only [Nat.cast_mul,le_refl]) E hE hEsize
  have hsmall : εv*(c*(t+q):ℕ)+εr*((c*(t+q):ℕ):ℝ)^c+4*D*(t:ℝ)^2/k<1 := by
    change εv*(c*(t+q):ℕ)+εr*((c*(t+q):ℕ):ℝ)^c≤1/4 at hunion
    linarith
  obtain ⟨τ,_,hv,hr,he⟩ := profile_all_sampling_tests_exists μ a c hs Y (c*(t+q)) hM BadV BadR BadE
    εv εr (4*D*(t:ℝ)^2/k) (by dsimp [εv];positivity) (by dsimp [εr];positivity) hV hRoots hOther hsmall
  refine ⟨A τ,?_,?_,?_,?_,?_⟩
  · have heA : A τ=(profileRootSet τ).image (profileComplementEmbedding F) := Finset.map_eq_image _ _
    exact heA.symm ▸ profileComplementEmbedding_image_disjoint F (profileRootSet τ)
  · intro i
    have heA : A τ=(profileRootSet τ).image (profileComplementEmbedding F) := Finset.map_eq_image _ _
    have hh := congrArg (fun U : Finset (Σ i,V i) =>
      (Finset.univ.filter (fun v : V i => (⟨i,v⟩ : Σ i,V i)∈U)).card) heA
    have hh' := profileComplementEmbedding_class_card F (profileRootSet τ) i
    convert hh.trans (hh'.trans (profileRootSet_class_card τ i)) using 1 <;> congr!
  · intro v hvτ
    exact le_of_not_gt (hv v hvτ)
  · intro σ hσ
    exact le_of_not_gt (hr σ hσ)
  · intro e heE hedge
    exact he ⟨e,heE,hedge⟩

end Oberwolfach

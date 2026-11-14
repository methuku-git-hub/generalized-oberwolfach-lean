module

public import Oberwolfach.UniformWeightedHypergraphMatching
public import Oberwolfach.FractionalResourceSparsification
public import Oberwolfach.ResourceRoundingScales
public import Oberwolfach.ResourceRoundingTransfer
public import Oberwolfach.UniformResourcePaddingBounds

@[expose] public section

/-! Rounding fractional weights with prescribed local estimates. The order
threshold is uniform over the original parallel edge identifiers and all
fixed coefficient functions. No weighted-matching theorem is assumed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem fractional_resource_matching (r B : ℕ) (hr : 2≤r) (hB : 1≤B)
    (K a γ : ℝ) (hK : 0<K) (ha : 0<a) (hγ : 0<γ) :
    ∃ η₀ : ℝ,0<η₀ ∧ ∃ n₀ : ℕ,∀ n : ℕ,n₀≤n →
    ∀ (V E A I : Type) [Fintype V] [Fintype E] [Fintype A] [Fintype I] [DecidableEq V],
    ∀ (R : E → Finset V) (w : E → ℝ) (g : A → E → ℝ) (S : I → Finset V),
    Fintype.card V≤n^B → Fintype.card A≤n^B → Fintype.card I≤n^B →
    (∀ e,2≤(R e).card ∧ (R e).card≤r) → (∀ e,0≤w e) →
    (∀ v,1-η₀≤hypergraphWeightedDegree R w v ∧ hypergraphWeightedDegree R w v≤1+η₀) →
    (∀ u v,u≠v → (∑ e,if u∈R e ∧ v∈R e then w e else 0)≤K/n) →
    (∀ i,a*n≤(S i).card) → (∀ i e,0≤g i e ∧ g i e≤1) →
    (∀ i,a*n≤∑ e,g i e*w e) →
    ∃ M : Finset E,(∀ e∈M,∀ f∈M,e≠f → Disjoint (R e) (R f)) ∧
      (∀ i,((S i \ M.biUnion R).card : ℝ)≤γ*(S i).card) ∧
      (∀ i,(1-γ)*(∑ e,g i e*w e)≤∑ e∈M,g i e) ∧
      (∀ i,(∑ e∈M,g i e)≤(1+γ)*(∑ e,g i e*w e)) := by
  classical
  let η := min (γ/20) (1/100)
  have hη : 0<η := lt_min (by positivity) (by norm_num)
  have hηsmall : η≤1/100 := min_le_right _ _
  have hηγ : 10*η≤γ := by have hh : η≤γ/20 := min_le_left _ _;linarith
  have hrR : (0 : ℝ)<r := by exact_mod_cast (show 0<r by omega)
  obtain ⟨N₁,hmatch⟩ := uniform_weighted_hypergraph_matching r (3*B+4) hr
    (K+1) (a/(4*r)) η (by linarith) (by positivity) hη
  obtain ⟨N₂,horder⟩ := resource_rounding_order r η a hη ha
  refine ⟨η,hη,max N₁ N₂,?_⟩
  intro n hn V E A I _ _ _ _ _ R w g S hV hA hI hsize hw hdegree hcodeg hS hg hweight
  obtain ⟨hn2,hrn,hηn,han⟩ := horder n ((le_max_right _ _).trans hn)
  have hn0 : 0<n := by omega
  have hnR : (0 : ℝ)<n := by exact_mod_cast hn0
  by_cases hnon : Nonempty V
  swap
  · haveI : IsEmpty V := not_nonempty_iff.mp hnon
    haveI : IsEmpty E := ⟨fun e=>by
      have he : R e=∅ := Finset.eq_empty_of_isEmpty _
      have hh := (hsize e).1
      rw [he,Finset.card_empty] at hh
      omega⟩
    refine ⟨∅,by simp,?_,?_,?_⟩
    · intro i
      have hh := hS i
      rw [Finset.eq_empty_of_isEmpty (S i),Finset.card_empty,Nat.cast_zero] at hh
      nlinarith
    · intro i
      simp
    · intro i
      simp
  letI : Nonempty V := hnon
  have hWpos : 0<∑ e,w e := by
    obtain ⟨v⟩ := hnon
    have hv : hypergraphWeightedDegree R w v≤∑ e,w e := by
      apply Finset.sum_le_sum
      intro e _
      split_ifs <;> first | exact le_refl _ | exact hw e
    exact (show 0<hypergraphWeightedDegree R w v by have hh := (hdegree v).1;linarith).trans_le hv
  obtain ⟨w',hw',hzero,htotal,hdeg',hpair',htest',hsupport⟩ :=
    fractional_resource_sparsification R w g hw hWpos
  have hdeg'bound (v : V) : 1-η≤hypergraphWeightedDegree R w' v ∧
      hypergraphWeightedDegree R w' v≤1+η := by rw [hdeg'];exact hdegree v
  let T := n^(2*B+2)
  let D := ⌈(1+η)*(T : ℝ)⌉₊
  obtain ⟨hnT,hηT,hsupscale,hDlo,hDhi,hD2,hnD,hDbound⟩ :=
    resource_rounding_scales n B η hn2 hη hηsmall hηn
  change n≤T at hnT
  change 1≤η*T at hηT
  change 4*(n : ℝ)^(2*B)≤η*T at hsupscale
  change (1+η)*(T : ℝ)≤D at hDlo
  change (D : ℝ)≤(1+2*η)*T at hDhi
  change D≤2*T at hD2
  change n≤D at hnD
  change D≤n^(3*B+4) at hDbound
  have hT0 : 0<T := hn0.trans_le hnT
  have hTR : (0 : ℝ)<T := by exact_mod_cast hT0
  have hD0 : 0<D := hn0.trans_le hnD
  have hDR : (0 : ℝ)<D := by exact_mod_cast hD0
  have hTD : (T : ℝ)≤D := by nlinarith
  have hsparse : (Finset.univ.filter (fun e=>0<w' e)).card≤4*n^(2*B) :=
    hsupport.trans (resource_sparse_support_bound n B _ _ (by omega) hV hA)
  have hsparseR : ((Finset.univ.filter (fun e=>0<w' e)).card : ℝ)≤η*T :=
    (by exact_mod_cast hsparse : ((Finset.univ.filter (fun e=>0<w' e)).card : ℝ)≤4*(n : ℝ)^(2*B)).trans hsupscale
  let m (e : E) := ⌊(T : ℝ)*w' e⌋₊
  let E' := Σ e,Fin (m e)
  letI : Fintype E' := inferInstanceAs (Fintype (Σ e,Fin (m e)))
  letI : DecidableEq E' := inferInstanceAs (DecidableEq (Σ e,Fin (m e)))
  let H (c : E') := R c.1
  have hcopies (v : V) : (1-2*η)*(T : ℝ)≤(Fintype.card (HypergraphEdgesAt H v) : ℝ) ∧
      (Fintype.card (HypergraphEdgesAt H v) : ℝ)≤(1+η)*T := by
    have heq : Fintype.card (HypergraphEdgesAt H v)=∑ e,if v∈R e then m e else 0 := by
      simpa only [HypergraphEdgesAt,Fintype.card_subtype] using resource_copies_degree R m v
    rw [heq]
    exact rounded_resource_degree_bounds R w' T η hw' hsparseR hdeg'bound v
  have hcopydegree (v : V) : 0<Fintype.card (HypergraphEdgesAt H v) ∧
      Fintype.card (HypergraphEdgesAt H v)≤D := by
    obtain ⟨hl,hu⟩ := hcopies v
    constructor
    · have hh : (0 : ℝ)<Fintype.card (HypergraphEdgesAt H v) :=
        (mul_pos (by linarith) hTR).trans_le hl
      exact_mod_cast hh
    · exact_mod_cast hu.trans hDlo
  have hmass : ∑ e,w' e≤Fintype.card V := bounded_rank_weight_mass R w' hw'
    (fun e=>(hsize e).1) (fun v=>by have hh := (hdeg'bound v).2;linarith)
  have hcopycard : Fintype.card E'≤T*Fintype.card V := rounded_resource_copy_card w' T hw' hmass
  let P := UniformPaddingVertex H r
  let Pinc := uniformPaddingIncidence H r
  have hPcard : Fintype.card P≤n^(3*B+4) := (uniformPadding_vertex_card H r).trans
    (resource_padding_polynomial_card n B r _ _ hn2 hrn hV hcopycard)
  have hPdegree := uniformPadding_degree_bounds H r D (by omega) hcopydegree
  have hκ : 1≤(K+1)*D/n := by
    apply (le_div_iff₀ hnR).mpr
    have hh : (n : ℝ)≤D := by exact_mod_cast hnD
    nlinarith
  have hPcodeg := uniformPadding_codegree_bounds H r ((K+1)*D/n) hκ (by
    intro u v huv
    have hc := rounded_resource_codegree_bound R w' T hw' u v
    change ((Finset.univ.filter (fun c : E'=>u∈H c ∧ v∈H c)).card : ℝ)≤_ at hc
    rw [hpair' u v] at hc
    calc
      _ ≤ (T : ℝ)*∑ e,if u∈R e ∧ v∈R e then w e else 0 := hc
      _ ≤ (T : ℝ)*(K/n) := mul_le_mul_of_nonneg_left (hcodeg u v huv) hTR.le
      _ = K*T/n := by ring
      _ ≤ (K+1)*D/n := div_le_div_of_nonneg_right (by nlinarith) hnR.le)
  let J := I⊕A
  let z : J → E' → ℝ := Sum.elim (fun i c=>((R c.1∩S i).card : ℝ)) (fun i c=>g i c.1)
  let W₀ : J → ℝ := Sum.elim (fun i=>(S i).card) (fun i=>∑ e,g i e*w e)
  let X (i : J) := ∑ c,z i c
  have hW₀ (i : J) : a*n≤W₀ i := by cases i with
    | inl i => exact hS i
    | inr i => exact hweight i
  have hW₀0 (i : J) : 0≤W₀ i := (mul_pos ha hnR).le.trans (hW₀ i)
  have hz (i : J) (c : E') : 0≤z i c ∧ z i c≤r := by
    cases i with
    | inl i =>
      change 0≤((R c.1∩S i).card : ℝ) ∧ ((R c.1∩S i).card : ℝ)≤r
      exact ⟨Nat.cast_nonneg _,by exact_mod_cast (Finset.card_le_card (Finset.inter_subset_left (s₁:=R c.1) (s₂:=S i))).trans (hsize c.1).2⟩
    | inr i =>
      exact ⟨(hg i c.1).1,(hg i c.1).2.trans (by exact_mod_cast (show 1≤r by omega))⟩
  have hXg (i : A) : (1-η)*(T : ℝ)*(∑ e,g i e*w e)≤X (Sum.inr i) ∧
      X (Sum.inr i)≤(T : ℝ)*(∑ e,g i e*w e) := by
    apply rounded_resource_test_bounds w' (g i) T η 1 _ hw' (by norm_num) (hg i) (htest' i)
    have hW1 : 1≤∑ e,g i e*w e := han.trans (hweight i)
    have hh := mul_le_mul_of_nonneg_left hW1 (mul_nonneg hη.le hTR.le)
    simp only [mul_one] at hh ⊢
    exact hsparseR.trans hh
  have hXlo (i : J) : (1-2*η)*(T : ℝ)*W₀ i≤X i := by
    cases i with
    | inl i => exact (resource_set_sum_bounds H (S i) _ _ hcopies).1
    | inr i =>
      have hh := (hXg i).1
      have hp := mul_nonneg hη.le (mul_nonneg hTR.le (hW₀0 (Sum.inr i)))
      change (1-2*η)*(T : ℝ)*(∑ e,g i e*w e)≤X (Sum.inr i)
      dsimp only [W₀,Sum.elim_inr] at hp
      nlinarith
  have hXmass (i : J) : (a/(4*r))*(r : ℝ)*D*n≤X i := by
    have heq : (a/(4*r))*(r : ℝ)=a/4 := by field_simp
    rw [heq]
    have hm := mul_le_mul_of_nonneg_left (hW₀ i)
      (mul_nonneg (by linarith : 0≤1-2*η) hTR.le)
    have hD2R : (D : ℝ)≤2*T := by exact_mod_cast hD2
    have hDscale := mul_le_mul_of_nonneg_right hD2R (show 0≤a*(n : ℝ) by positivity)
    have hsmall := mul_nonneg (show 0≤1/2-2*η by linarith)
      (show 0≤(T : ℝ)*a*n by positivity)
    nlinarith [hXlo i]
  obtain ⟨M',hM',hMz⟩ := hmatch n D ((le_max_left _ _).trans hn) hnD hDbound
    P E' J Pinc z (fun _=>r) X hPcard
    (by simpa only [J,Fintype.card_sum] using resource_test_polynomial_card n B _ _ hn2 hI hA)
    (fun c=>uniformPadding_card H r (fun c=>(hsize c.1).2) c)
    (fun v=>by simpa only [HypergraphEdgesAt,Fintype.card_subtype] using (hPdegree v).1)
    (fun v=>by simpa only [HypergraphEdgesAt,Fintype.card_subtype] using (hPdegree v).2)
    (by intro u v huv;convert hPcodeg u v huv using 1;congr 2;ext e;simp only [Finset.mem_filter,Pinc])
    (fun _=>hrR) hz (fun _=>rfl) hXmass
  have hproj := resource_copy_matching_projection_weights R m
    (fun e=>Finset.card_pos.mp (by have hh := (hsize e).1;omega)) M'
    (uniformPadding_matching_projection H r M' hM')
  let M := M'.image Sigma.fst
  refine ⟨M,hproj.1,?_,?_,?_⟩
  · intro i
    have hl := rounded_matching_lower_transfer hη hηsmall hηγ hTR (hW₀0 (Sum.inl i))
      hDlo hDhi (hXlo (Sum.inl i)) (hMz (Sum.inl i))
    have heq := hproj.2 (fun e=>((R e∩S i).card : ℝ))
    rw [matching_set_test_sum R (S i) _ hproj.1] at heq
    change ((S i∩M.biUnion R).card : ℝ)=_ at heq
    change (1-γ)*((S i).card : ℝ)≤∑ c∈M',((R c.1∩S i).card : ℝ) at hl
    rw [← heq] at hl
    have hcard : ((S i \ M.biUnion R).card : ℝ)+((S i∩M.biUnion R).card : ℝ)=(S i).card := by
      exact_mod_cast Finset.card_sdiff_add_card_inter (S i) (M.biUnion R)
    nlinarith
  · intro i
    have hl := rounded_matching_lower_transfer hη hηsmall hηγ hTR (hW₀0 (Sum.inr i))
      hDlo hDhi (hXlo (Sum.inr i)) (hMz (Sum.inr i))
    rw [hproj.2 (g i)]
    exact hl
  · intro i
    have hu := rounded_matching_upper_transfer hη.le hTR (hW₀0 (Sum.inr i))
      hDlo (hXg i).2 (hMz (Sum.inr i))
    rw [hproj.2 (g i)]
    exact hu.trans (by have hp := mul_nonneg hγ.le (hW₀0 (Sum.inr i));dsimp [W₀] at hp ⊢; nlinarith)

end Oberwolfach

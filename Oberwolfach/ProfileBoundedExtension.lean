module

public import Oberwolfach.ProfileHostGoodSample
public import Oberwolfach.ProfileSamplingNumericalMargins
public import Oberwolfach.ProfileTwoExtensionFactors

@[expose] public section

/-! The bounded-extension theorem for finite indexed resources with a
fixed class profile. Both factors and their common sampled ground set
are constructed from the original weights and absorber abundance.
The tolerance precedes q, the sample order precedes the forbidden-set
and forbidden-pair bounds, and only the ambient threshold depends on
these later inputs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option synthInstance.maxSize 256
set_option maxHeartbeats 5000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {s : ℕ} {Tpl : Type} [Fintype Tpl] [DecidableEq Tpl]

theorem profile_two_bounded_factors (hspos : 1≤s)
    (a : Fin s → ℕ) (c J : ℕ) (hc : 3≤c) (hJpos : 1≤J)
    (ha : ∀ i,1≤a i) (hs : ∑ i,a i=c)
    (S : Tpl → VertexAbsorberTemplate c) (α b B : ℝ)
    (hα : 0<α) (hb : 0<b) (hB : 0<B) :
    ∃ η : ℝ,0<η ∧ ∀ q : ℕ,∃ t : ℕ,1≤t ∧ ∀ F₀ D : ℝ,0≤F₀ → 0≤D →
      ∃ k₀ : ℝ,1<k₀ ∧ ∀ k : ℝ,k₀≤k →
        ∀ (V : Fin s → Type) [∀ i,Fintype (V i)] [∀ i,DecidableEq (V i)]
          (C : Type) [Fintype C] [DecidableEq C],
        ∀ (R : C → Finset (Σ i,V i)) (w : C → ℝ),
        (∀ i,(Fintype.card (V i):ℝ)=a i*k) →
        (∀ C₀ i,(Finset.univ.filter (fun v : V i => (⟨i,v⟩ : Σ i,V i)∈R C₀)).card=a i) →
        (∀ U : Finset (Σ i,V i),Fintype.card {C₀ : C // R C₀=U}≤J) →
        (∀ C₀,b/k^(c-1)≤w C₀ ∧ w C₀≤B/k^(c-1)) →
        (∀ v,|1-hypergraphWeightedDegree R w v|≤η) →
        (∀ σ : ∀ i,FixedSubset (V i) (a i),α*k^(c*c)≤Fintype.card (LabelledAbsorberFamily R S (profileRootSet σ))) →
        ∀ (T Z : Finset (Σ i,V i)) (z : ℕ),(T.card:ℝ)≤F₀ → z≤q →
        (∀ i,(Finset.univ.filter (fun v : V i => (⟨i,v⟩ : Σ i,V i)∈Z)).card=a i*z) →
        ∀ E : Finset ((Σ i,V i)×(Σ i,V i)),(∀ e∈E,e.1≠e.2) → (E.card:ℝ)≤D*k →
        ∀ P : C → Finset ((Σ i,V i)×(Σ i,V i)),
        (∀ C₀,∀ e∈P C₀,e.1≠e.2 ∧ e.1∈R C₀ ∧ e.2∈R C₀) →
        (∀ C₀,(P C₀).card≤c) →
        (∀ C₀ v,((P C₀).filter (fun e => v=e.1 ∨ v=e.2)).card≤2) →
        ∃ A : Finset (Σ i,V i),∃ D₀ D₁ : Finset C,
          Disjoint A (Z∪T) ∧
          (∀ i,(Finset.univ.filter (fun v : V i => (⟨i,v⟩ : Σ i,V i)∈A)).card=a i*t) ∧
          (∀ e∈E,¬(e.1∈A ∧ e.2∈A)) ∧
          ((∀ x∈D₀,∀ y∈D₀,x≠y → Disjoint (R x) (R y)) ∧ D₀.biUnion R=A) ∧
          ((∀ x∈D₁,∀ y∈D₁,x≠y → Disjoint (R x) (R y)) ∧ D₁.biUnion R=A∪Z) ∧
          Disjoint (D₀.biUnion P) (D₁.biUnion P) ∧
          ∀ C₀∈D₁,(R C₀∩Z).card≤1 := by
  letI : Nonempty (Fin s) := ⟨⟨0,by omega⟩⟩
  let αf := α/(4*(2:ℝ)^(c*c))
  let Bf := (2:ℝ)^(c-1)*B
  have hαf : 0<αf := by dsimp [αf];positivity
  have hBf : 0≤Bf := by dsimp [Bf];positivity
  obtain ⟨ηf,hηf,hfactor⟩ := profile_two_extension_factors_from_counts a c J hc ha hs S αf b Bf hαf hb hBf
  let ξ := min 1 (ηf/2)
  have hξ : 0<ξ := lt_min (by norm_num) (by positivity)
  have hξ1 : ξ≤1 := min_le_left _ _
  have hξf : 2*ξ≤ηf := by have hh := min_le_right (1:ℝ) (ηf/2);dsimp [ξ];linarith
  let A₀ := B*J*(c:ℝ)^(c-2)
  let Dₐ := absorberVertexDeletionCoefficient c J (Fintype.card Tpl)
  obtain ⟨N,hNc,hnum⟩ := profile_sampling_numerical_margins c (by omega) A₀ Dₐ α ξ
    (by dsimp [A₀];positivity) (by dsimp [Dₐ,absorberVertexDeletionCoefficient];positivity) hα hξ hξ1
  let Lv := 2*(J:ℝ)*(2*(c:ℝ)+1)^(c-2)*B
  let Lr := 1+2*((c*c)*Fintype.card Tpl*c^c*J^(2*c+1):ℕ)*((c:ℝ)+1)^(c*c-1)
  let κv := 2*ξ^2/((c:ℝ)*Lv^2)
  let κr := 2*(α/4)^2/((c:ℝ)*Lr^2)
  have hcR : (0:ℝ)<c := by exact_mod_cast (show 0<c by omega)
  have hJR : (0:ℝ)<J := by exact_mod_cast (show 0<J by omega)
  have hLv : 0<Lv := by dsimp [Lv];positivity
  have hLr : 0<Lr := by dsimp [Lr];positivity
  have hκv : 0<κv := by dsimp [κv];positivity
  have hκr : 0<κr := by dsimp [κr];positivity
  refine ⟨ξ/4,by positivity,?_⟩
  intro q
  obtain ⟨Nf,hfactor⟩ := hfactor q
  obtain ⟨t,htN,htq,ht4,hunion⟩ := profile_sample_order_union_margin c q (max N Nf) (by omega) κv κr hκv hκr
  have ht : N≤t := (le_max_left _ _).trans htN
  have htf : Nf≤t := (le_max_right _ _).trans htN
  have htc : c+c*c≤t := hNc.trans ht
  have htpos : (0:ℝ)<t := by exact_mod_cast (show 0<t by omega)
  refine ⟨t,by omega,?_⟩
  intro F₀ D hF₀ hD
  obtain ⟨k₀,hk₀,hknum⟩ := hnum t ht (F₀+c*q) D (by positivity) hD
  refine ⟨k₀,hk₀,?_⟩
  intro k hk V _ _ C _ _ R w hn hR hJ hw herr habs T Z z hT hz hZ E hE hEsize P hP hPc hPd
  obtain ⟨hkpos,hfeas,hhalf,hlargeV,hlargeR,hmarginV,hmarginR,hloss,hsep⟩ := hknum k hk
  have hZsize : Z.card≤c*q := by
    rw [sigma_finset_card]
    simp_rw [hZ]
    rw [← Finset.sum_mul,hs]
    exact Nat.mul_le_mul_left c hz
  have hF : ((Z∪T).card:ℝ)≤F₀+c*q := by
    have hU : ((Z∪T).card:ℝ)≤(Z.card:ℝ)+T.card := by exact_mod_cast Finset.card_union_le Z T
    have hZR : (Z.card:ℝ)≤(c:ℝ)*q := by exact_mod_cast hZsize
    linarith
  have hw0 (C₀ : C) : 0≤w C₀ := (by positivity : (0:ℝ)≤b/k^(c-1)).trans (hw C₀).1
  obtain ⟨A,hAF,hAc,hAv,hAa,hAE⟩ := profile_host_good_sample a ha c J (by omega) hJpos hs R w S hR hJ
    k (F₀+c*q) D B α (ξ/4) ξ hkpos hB hα.le (by positivity) hξ.le hn
    (fun C₀ => ⟨hw0 C₀,(hw C₀).2⟩) herr habs (Z∪T) Z hF q hZsize t htc hfeas hhalf
    hlargeV hlargeR hmarginV hmarginR hloss E hE hEsize hsep hunion
  let wt := fun C₀ => (k/(t:ℝ))^(c-1)*w C₀
  have hkt : (t:ℝ)≤(t+z:ℕ) := by exact_mod_cast Nat.le_add_right t z
  have hk2t : ((t+z:ℕ):ℝ)≤2*t := by exact_mod_cast (show t+z≤2*t by omega)
  have hkp : (0:ℝ)<(t+z:ℕ) := htpos.trans_le hkt
  have hwt (C₀ : C) : b/(t+z:ℕ)^(c-1)≤wt C₀ ∧ wt C₀≤Bf/(t+z:ℕ)^(c-1) := by
    have hup := (rescaled_individual_weight (c-1) k t B (w C₀) hkpos htpos ⟨hw0 C₀,(hw C₀).2⟩).2
    have hlo : b/(t:ℝ)^(c-1)≤wt C₀ := by
      calc
        _ = (k/(t:ℝ))^(c-1)*(b/k^(c-1)) := by rw [div_pow];field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left (hw C₀).1 (by positivity)
    constructor
    · exact (div_le_div_of_nonneg_left hb.le (pow_pos htpos _) (pow_le_pow_left₀ htpos.le hkt _)).trans hlo
    · apply hup.trans
      apply (div_le_div_iff₀ (pow_pos htpos _) (pow_pos hkp _)).mpr
      have hp := pow_le_pow_left₀ hkp.le hk2t (c-1)
      dsimp [Bf]
      rw [mul_pow] at hp
      nlinarith [mul_le_mul_of_nonneg_left hp hB.le]
  have habs' (σ : ∀ i,FixedSubset (V i) (a i)) (hσ : profileRootSet σ⊆A∪Z) :
      αf*(t+z:ℕ)^(c*c)≤absorberGroundCount R S (profileRootSet σ) A := by
    apply le_trans _ (hAa σ hσ)
    calc
      _ ≤ αf*((2:ℝ)*t)^(c*c) := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hkp.le hk2t _) hαf.le
      _ = (α/4)*(t:ℝ)^(c*c) := by dsimp [αf];rw [mul_pow];field_simp
  have hAZ : Disjoint A Z := hAF.mono_right Finset.subset_union_left
  obtain ⟨D₀,D₁,hD₀,hD₁,hdis,hcap⟩ := hfactor t z htf hz V C R wt A Z hAZ hAc hZ hR hJ hwt
    (fun v hv => (hAv v hv).trans hξf) habs' P hP hPc hPd
  exact ⟨A,D₀,D₁,hAF,hAc,hAE,hD₀,hD₁,hdis,hcap⟩

end Oberwolfach

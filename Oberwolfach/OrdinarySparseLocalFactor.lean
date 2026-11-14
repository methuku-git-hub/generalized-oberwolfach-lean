module

public import Oberwolfach.OrdinaryLocalAbsorbers
public import Oberwolfach.SingleClassFactorExtraction
public import Oberwolfach.MarkedHubAbsorberAbundance
public import Oberwolfach.HubFactorWeightScales

@[expose] public section

/-! Ordinary factors from actual sparse common-neighbourhood estimates.
Absorber existence and counts are constructed; only the original positive
vertex weights and their incident error are supplied. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 512
set_option maxHeartbeats 5000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_sparse_local_factor (m : ℕ) (hm : 2≤m) (γ κ b B : ℝ)
    (hγ : 0<γ) (hκ : 0<κ) (hb : 0<b) (hB : 0≤B) :
    ∃ ε η : ℝ,0<ε ∧ 0<η ∧ ∃ N : ℕ,
      ∀ (V : Type) [Fintype V] [DecidableEq V],N≤Fintype.card V →
      ∀ (Q F : SimpleGraph V) (T : Finset V),κ*Fintype.card V≤(T.card:ℝ) →
      (m+1)∣T.card → (∀ v,(F.degree v:ℝ)≤ε*Fintype.card V) →
      (∀ S : Finset V,S.card≤(if m=2 then 3 else 2) →
        γ*Fintype.card V≤((common T S (fun x=>Q.neighborFinset x)).card:ℝ)) →
      ∀ wt : LocalOrdinaryCycle Q F T (m+1)→ℝ,
      (∀ C,b/(Fintype.card V:ℝ)^m≤wt C ∧ wt C≤B/(Fintype.card V:ℝ)^m) →
      (∀ v∈T,|1-hypergraphWeightedDegree localOrdinaryVertices wt v|≤η) →
      HasResourceDecomposition (localOrdinaryVertices (Q:=Q) (F:=F) (T:=T) (r:=m+1)) T := by
  let β := ordinaryLocalCountCoeff m γ
  have hβ : 0<β := ordinaryLocalCountCoeff_pos m γ hγ
  let a := (β/2)^(m+2)
  have ha : 0<a := by dsimp [a];positivity
  let α := a*(m+1:ℝ)^((m+1)*(m+1))
  have hα : 0<α := by dsimp [α];positivity
  let κ' := κ/(m+1:ℝ)
  have hκ' : 0<κ' := by dsimp [κ'];positivity
  obtain ⟨η,hη,k₀,hfactor⟩ := single_class_factor_extraction (m+1) ((m+1)^(m+1))
    (by omega) α (b*κ'^m) B hα (by positivity) hB
  obtain ⟨Na,hNa⟩ := paired_absorber_order_threshold m β hβ
  obtain ⟨N₁,hN₁⟩ := exists_nat_gt (max (4*(m+3:ℝ)/γ) ((k₀:ℝ)/κ'))
  let ε := γ/(4*(m+3:ℝ))
  have hε : 0<ε := by dsimp [ε];positivity
  refine ⟨ε,η,hε,hη,max Na (max N₁ 1),?_⟩
  intro V _ _ hn Q F T hsize hdiv hF hcommon wt hw herr
  let n : ℝ := Fintype.card V
  have hnn : 1≤Fintype.card V := (le_max_right N₁ 1).trans ((le_max_right Na _).trans hn)
  have hnpos : 0<n := by dsimp [n];exact_mod_cast hnn
  have hNn : (N₁:ℝ)≤n := by
    dsimp [n]
    exact_mod_cast (le_max_left N₁ 1).trans ((le_max_right Na _).trans hn)
  have hlarge : 4*(m+3:ℝ)≤γ*n := by
    have hh := (le_max_left (4*(m+3:ℝ)/γ) _).trans (hN₁.le.trans hNn)
    nlinarith only [(div_le_iff₀ hγ).mp hh]
  have hbudget : (m+3:ℝ)*(ε*n+1)≤γ/2*n := by
    have he : (m+3:ℝ)*ε=γ/4 := by dsimp [ε];field_simp
    nlinarith only [congrArg (fun z : ℝ=>z*n) he,hlarge]
  obtain ⟨k,hkT⟩ := hdiv
  have hkTreal : (T.card:ℝ)=(m+1:ℝ)*k := by exact_mod_cast hkT
  have hkappa : κ'*n≤(k:ℝ) := by
    dsimp [κ']
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (show (0:ℝ)<m+1 by positivity)).mpr
    nlinarith only [hsize,hkTreal]
  have hkpos : (0:ℝ)<k := (mul_pos hκ' hnpos).trans_le hkappa
  have hkn : (k:ℝ)≤n := by
    have ht : (T.card:ℝ)≤n := by dsimp [n];exact_mod_cast Finset.card_le_univ T
    have hmR : (0:ℝ)≤m := Nat.cast_nonneg _
    nlinarith only [ht,hkTreal,mul_nonneg hmR hkpos.le]
  have hk : k₀≤k := by
    have hh := (le_max_right (4*(m+3:ℝ)/γ) ((k₀:ℝ)/κ')).trans (hN₁.le.trans hNn)
    have hh' : (k₀:ℝ)≤κ'*n := by nlinarith only [(div_le_iff₀ hκ').mp hh]
    exact_mod_cast hh'.trans hkappa
  have hweights (C : LocalOrdinaryCycle Q F T (m+1)) :
      (b*κ'^m)/(k:ℝ)^((m+1)-1)≤wt C ∧ wt C≤B/(k:ℝ)^((m+1)-1) := by
    simpa only [Nat.add_sub_cancel] using hub_factor_weight_scale m n k κ' b B (wt C)
      hnpos hkpos hκ' hb.le hB hkn hkappa (hw C)
  apply hfactor k hk V (LocalOrdinaryCycle Q F T (m+1)) T localOrdinaryVertices wt hkT
    (fun C v hv=>C.property.1 v (Set.mem_toFinset.mp hv)) localOrdinaryVertices_card
    (local_ordinary_multiplicity Q F T) hweights herr
  intro X hXT hXr
  let e : Fin (m+1)≃X := Fintype.equivOfCardEq (by simp only [Fintype.card_fin,Fintype.card_coe,hXr])
  let x : Fin (m+1)→V := fun i=>(e i).val
  have hx : Function.Injective x := by
    intro i j h;exact e.injective (Subtype.ext h)
  have hxT (i : Fin (m+1)) : x i∈T := hXT (e i).property
  have hxX : Finset.univ.image x=X := by
    ext v
    simp only [Finset.mem_image,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨i,rfl⟩;exact (e i).property
    · intro hv
      obtain ⟨i,hi⟩ := e.surjective ⟨v,hv⟩
      exact ⟨i,congrArg Subtype.val hi⟩
  have habs := ordinary_local_paired_absorber_count Q F T hm γ (ε*n) hγ (by positivity)
    hF hcommon hbudget (hNa _ ((le_max_left Na _).trans hn)).1
    (hNa _ ((le_max_left Na _).trans hn)).2 x hx hxT
  rw [hxX] at habs
  have hscale : α*(k:ℝ)^((m+1)*(m+1))≤a*n^((m+1)*(m+1)) := by
    have hc : (m+1:ℝ)*k≤n := by rw [← hkTreal];dsimp [n];exact_mod_cast Finset.card_le_univ T
    calc
      _ = a*((m+1:ℝ)*k)^((m+1)*(m+1)) := by dsimp [α];rw [mul_pow];ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hc _) ha.le
  exact hscale.trans habs

end Oberwolfach

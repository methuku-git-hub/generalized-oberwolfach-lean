module

public import Oberwolfach.ThinnedCommonConfigurations
public import Oberwolfach.ThinnedCommonClassSizes
public import Oberwolfach.CommonWeightWitnessBounds

@[expose] public section

/-! Loads, accurate class sizes and actual cycle/path counts hold with the
same thinning selector. The coefficient function remains fixed before all
sampling. Projection to a selector is performed only after this conjunction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color : Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

def thinnedMarkedAddCoins (σ : RawMarkedOutcome V U Γ Color) (κ : V→Bool) : ThinnedMarkedOutcome V U Γ Color
  | Sum.inl e=>σ e
  | Sum.inr v=>κ v

def RawCommonWitness (P : SimpleGraph V) (π : Equiv.Perm V) (d r : ℕ)
    (α astar pstar D p k s₀ ηsize ηload : ℝ) (weight : (Fin (r+4+1)→V)→ℝ)
    (g : Γ) (j : Color) (u u' : U) (σ : RawMarkedOutcome V U Γ Color) (κ : V→Bool) : Prop :=
  let T := thinnedCommonClass π d g j u u' (thinnedMarkedAddCoins σ κ)
  CommonClassDensity P π α astar T ∧
  CommonClassConfigurationCounts P π d r α astar pstar T (fun e=>σ (Sum.inl e)) ∧
  (∀ b,|((T b).card:ℝ)-(if b then (s₀/((r+4:ℕ):ℝ))*(s₀/((r+4:ℕ):ℝ)) else s₀*s₀/((r+4:ℕ):ℝ))*Fintype.card V|≤ηsize*Fintype.card V) ∧
  CommonPotentialSpokeLoads P π d (r+4) D p k (s₀*s₀/((r+4:ℕ):ℝ)) weight ηload σ
    (rawMarkedPairSpokes π d σ g j) κ u u'

theorem thinnedCommon_joint_event
    (r : ℕ) (hr : 1≤r) (α astar pstar B εsize εload : ℝ)
    (hα : 0<α) (hα1 : α≤1/2) (hastar : 0<astar) (hpstar : 0<pstar)
    (hB : 0<B) (hεsize : 0<εsize) (hεload : 0<εload)
    (d Q : ℕ) (hd : 2≤d) :
    ∃ N : ℕ,1≤N ∧ ∀ (V U Γ Color : Type)
      [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [LinearOrder V] [DecidableEq U],
      N≤Fintype.card V → ∀ (P : SimpleGraph V) (π : Equiv.Perm V),
      (∀ x,(1/2+α)*Fintype.card V≤(P.degree x:ℝ)) →
      (∀ x l,0<l → l<2*d+1 → (π^l) x≠x) →
    ∀ (p k : ℝ) (hp : 0<p) (hk : 0<k) (hphys : 2*p+2*k≤1),pstar≤p → pstar≤k →
    ∀ (q : U→Γ→ℝ) (hq : ∀ u a,0≤q u a) (hQ : ∀ u,∑ a,q u a≤1/8)
      (s : U→Color→ℝ) (hs : ∀ u j,0≤s u j)
      (hS : ∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ a,q u a))
      (g : Γ) (j : Color) (s₀ D τ A : ℝ),0<s₀ →
      (∀ u,q u g=s₀/((r+4:ℕ):ℝ)) → (∀ u,s u j=s₀) →
      pstar≤s₀*s₀/((r+4:ℕ):ℝ) → s₀*s₀/((r+4:ℕ):ℝ)≤1 →
      astar≤(s₀/((r+4:ℕ):ℝ))*(s₀/((r+4:ℕ):ℝ)) → astar≤s₀*s₀/((r+4:ℕ):ℝ) →
    ∀ weight : (Fin (r+4+1)→V)→ℝ,
      SuccessorSequenceWeightConditions P π (3*d) D τ A B weight →
      (Fintype.card V:ℝ)/2≤D → D≤2*Fintype.card V →
    ∀ u u' : U,u≠u' →
    1-3/(Fintype.card V:ℝ)^Q≤
      (FiniteLaw.pi (thinnedMarkedLaw (rawMarkedWheelLaw p k hp.le hk.le hphys d hd q hq hQ s hs hS)
        (1/((r+4:ℕ):ℝ)) (by positivity) (by apply (div_le_one (by positivity)).mpr;exact_mod_cast (show 1≤r+4 by omega)))).probability
        (fun σ=>RawCommonWitness P π d r α astar pstar D p k s₀ εsize (τ+εload) weight g j u u'
          (fun e=>σ (Sum.inl e)) (fun v=>σ (Sum.inr v))) := by
  let m := r+4
  let Bplus := 2*B/pstar^(2*m+1)
  have hBplus : 0<Bplus := by dsimp [Bplus];positivity
  obtain ⟨N₁,hN₁pos,hN₁⟩ := thinnedCommon_configurations_event r hr α astar pstar hα hα1 hastar hpstar d Q hd
  obtain ⟨N₂,hN₂pos,hN₂⟩ := thinnedCommonClass_size_event εsize hεsize d Q hd
  obtain ⟨N₃,hN₃⟩ := eventually_stretchedExp_le_inv_pow 8 2
    (c:=commonWeightLoadExponent m d Bplus εload) (p:=1)
    (commonWeightLoadExponent_pos m d Bplus εload hBplus hεload) (by norm_num) Q
  refine ⟨max 1 (max N₁ (max N₂ N₃)),le_max_left _ _,?_⟩
  intro V U Γ Color _ _ _ _ _ _ hnN P π hP hnoshort p k hp hk hphys hpmin hkmin q hq hQ s hs hS g j s₀ D τ A hs₀ hq₀ hs₀' hsmin hs1 hqclass hsclass weight hw hDlo hDhi u u' hu
  have hn : 0<Fintype.card V := by omega
  have hnR : (0:ℝ)<Fintype.card V := Nat.cast_pos.mpr hn
  obtain ⟨hθ,hθ1,hsbar,hqbar,hsbar'⟩ := commonThinning_parameters m (by dsimp [m];omega) s₀ hs₀
  let μ : FiniteLaw (ThinnedMarkedOutcome V U Γ Color) := FiniteLaw.pi (thinnedMarkedLaw (rawMarkedWheelLaw p k hp.le hk.le hphys d hd q hq hQ s hs hS) (1/(m:ℝ)) hθ hθ1)
  let T := fun σ : ThinnedMarkedOutcome V U Γ Color=>thinnedCommonClass π d g j u u' σ
  let Counts := fun σ : ThinnedMarkedOutcome V U Γ Color=>
    CommonClassDensity P π α astar (T σ) ∧
      CommonClassConfigurationCounts P π d r α astar pstar (T σ) (thinnedMarkedPhysicalPart σ)
  let Sizes := fun σ : ThinnedMarkedOutcome V U Γ Color=>∀ b,
    |((T σ b).card:ℝ)-(if b then (s₀/m)*(s₀/m) else s₀*s₀/m)*Fintype.card V|≤εsize*Fintype.card V
  let Loads := fun σ : ThinnedMarkedOutcome V U Γ Color=>
    CommonPotentialSpokeLoads P π d m D p k (s₀*s₀/m) weight (τ+εload)
      (fun e=>σ (Sum.inl e)) (rawMarkedPairSpokes π d (fun e=>σ (Sum.inl e)) g j) (fun v=>σ (Sum.inr v)) u u'
  have hcounts : 1-1/(Fintype.card V:ℝ)^Q≤μ.probability Counts :=
    hN₁ V U Γ Color (by omega) P π hP hnoshort p k hp.le hk.le hphys hpmin hkmin
      q hq hQ s hs hS (1/(m:ℝ)) hθ hθ1 g j u u' hu
      (by rw [hq₀,hq₀];exact hqclass) (by rw [hs₀',hs₀',hsbar'];exact hsclass)
  have hsizes : 1-1/(Fintype.card V:ℝ)^Q≤μ.probability Sizes := by
    have hh := hN₂ V U Γ Color (by omega) π hnoshort p k hp.le hk.le hphys
      q hq hQ s hs hS (1/(m:ℝ)) hθ hθ1 g j u u' hu
    simpa only [hq₀,hs₀',hsbar'] using hh
  have hloads : 1-1/(Fintype.card V:ℝ)^Q≤μ.probability Loads := by
    have hh := thinnedMarkedSeed_spoke_event P π p k hp hk hphys d hd q hq hQ s hs hS hnoshort
      (1/(m:ℝ)) hθ hθ1 g j u u' hu m (by dsimp [m];omega) (s₀*s₀/m) ((s₀/m)*(s₀/m)) D τ A B hB
      (by rw [hq₀,hq₀]) (by rw [hs₀',hs₀'];exact hsbar') hqbar weight hw hn hDlo hDhi
      pstar hpstar hpmin hkmin hsmin (by linarith) (by linarith) hs1 εload hεload
    dsimp only at hh
    rw [commonWeightLoad_tail_exponential m d Bplus εload (Fintype.card V) hnR] at hh
    have hroots := marked_root_domain_card (V:=V) (U:=Unit) (by simpa only [Fintype.card_unique] using Nat.succ_le_of_lt hn)
    have hrootsR : (Fintype.card (((V×V)⊕(V×V))⊕(Bool×V×Unit)):ℝ)≤4*(Fintype.card V:ℝ)^2 := by exact_mod_cast hroots
    have hfail := hN₃ (Fintype.card V) (by omega)
    simp only [Real.rpow_two,Real.rpow_one] at hfail
    have hmul := mul_le_mul_of_nonneg_right hrootsR
      (show 0≤2*Real.exp (-commonWeightLoadExponent m d Bplus εload*Fintype.card V) by positivity)
    have hsmall : (Fintype.card (((V×V)⊕(V×V))⊕(Bool×V×Unit)):ℝ)*
        (2*Real.exp (-commonWeightLoadExponent m d Bplus εload*Fintype.card V))≤1/(Fintype.card V:ℝ)^Q := by
      calc
        _ ≤ 8*(Fintype.card V:ℝ)^(2:ℕ)*Real.exp (-commonWeightLoadExponent m d Bplus εload*Fintype.card V) := by convert hmul using 1 <;> ring
        _ ≤ _ := hfail
    exact (sub_le_sub_left hsmall 1).trans hh
  have hcs := (sub_le_sub_right hcounts (1/(Fintype.card V:ℝ)^Q)).trans
    (finiteLaw_good_intersection μ Counts Sizes (1/(Fintype.card V:ℝ)^Q) hsizes)
  have hall := (sub_le_sub_right hcs (1/(Fintype.card V:ℝ)^Q)).trans
    (finiteLaw_good_intersection μ (fun σ=>Counts σ ∧ Sizes σ) Loads (1/(Fintype.card V:ℝ)^Q) hloads)
  have heq : 1-3/(Fintype.card V:ℝ)^Q=
      1-1/(Fintype.card V:ℝ)^Q-1/(Fintype.card V:ℝ)^Q-1/(Fintype.card V:ℝ)^Q := by ring
  rw [heq]
  apply hall.trans
  apply finiteLaw_probability_mono
  intro σ hσ
  exact ⟨hσ.1.1.1,hσ.1.1.2,hσ.1.2,hσ.2⟩

end Oberwolfach

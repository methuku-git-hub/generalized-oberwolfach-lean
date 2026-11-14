module

public import Oberwolfach.ThinnedCommonJointEvent

@[expose] public section

/-! One original-sample event for all hub pairs. Each selector simultaneously
certifies the loads, class sizes and configuration counts. Pairwise
independence is neither assumed nor needed for the final union bound. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem rawMarked_common_joint_witness_event
    (r : ℕ) (hr : 1≤r) (α astar pstar B εsize εload : ℝ)
    (hα : 0<α) (hα1 : α≤1/2) (hastar : 0<astar) (hpstar : 0<pstar)
    (hB : 0<B) (hεsize : 0<εsize) (hεload : 0<εload)
    (d Q : ℕ) (hd : 2≤d) :
    ∃ N : ℕ,1≤N ∧ ∀ (V U Γ Color : Type)
      [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [LinearOrder V] [DecidableEq U],
      N≤Fintype.card V → Fintype.card U≤Fintype.card V → ∀ (P : SimpleGraph V) (π : Equiv.Perm V),
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
    1-1/(Fintype.card V:ℝ)^Q≤
      (FiniteLaw.pi (rawMarkedWheelLaw p k hp.le hk.le hphys d hd q hq hQ s hs hS)).probability
        (fun σ=>∀ u u',u≠u' → ∃ κ,
          RawCommonWitness P π d r α astar pstar D p k s₀ εsize (τ+εload) weight g j u u' σ κ) := by
  obtain ⟨N,hNpos,hN⟩ := thinnedCommon_joint_event r hr α astar pstar B εsize εload
    hα hα1 hastar hpstar hB hεsize hεload d (Q+3) hd
  refine ⟨max N 3,by omega,?_⟩
  intro V U Γ Color _ _ _ _ _ _ hnN huCard P π hP hnoshort p k hp hk hphys hpmin hkmin q hq hQ s hs hS g j s₀ D τ A hs₀ hq₀ hs₀' hsmin hs1 hqclass hsclass weight hw hDlo hDhi
  have hn : 0<Fintype.card V := by omega
  have hnR : (0:ℝ)<Fintype.card V := Nat.cast_pos.mpr hn
  let μ := rawMarkedWheelLaw (V:=V) p k hp.le hk.le hphys d hd q hq hQ s hs hS
  let err := 3/(Fintype.card V:ℝ)^(Q+3)
  let Good := fun a : U×U=>fun σ : RawMarkedOutcome V U Γ Color=>
    a.1≠a.2 → ∃ κ,RawCommonWitness P π d r α astar pstar D p k s₀ εsize (τ+εload) weight g j a.1 a.2 σ κ
  have herr : 0≤err := by dsimp [err];positivity
  have hpair (a : U×U) : 1-err≤(FiniteLaw.pi μ).probability (Good a) := by
    by_cases ha : a.1=a.2
    · simp only [Good,ha,ne_eq,not_true_eq_false,false_implies,finiteLaw_probability_true]
      have ht := finiteLaw_probability_true (FiniteLaw.pi μ)
      linarith only [herr,ht]
    obtain ⟨hθ,hθ1,hsbar,hqbar,hsbar'⟩ := commonThinning_parameters (r+4) (by omega) s₀ hs₀
    have hh := hN V U Γ Color (by omega) P π hP hnoshort p k hp hk hphys hpmin hkmin
      q hq hQ s hs hS g j s₀ D τ A hs₀ hq₀ hs₀' hsmin hs1 hqclass hsclass weight hw hDlo hDhi a.1 a.2 ha
    have hpj := thinnedMarked_exists_coins_probability μ (1/((r+4:ℕ):ℝ)) hθ hθ1
      (fun σ κ=>RawCommonWitness P π d r α astar pstar D p k s₀ εsize (τ+εload) weight g j a.1 a.2 σ κ)
    apply (hh.trans hpj).trans
    apply finiteLaw_probability_mono
    intro σ hσ _
    exact hσ
  have hh := finiteLaw_common_event_lower (FiniteLaw.pi μ) Finset.univ
    (fun a σ=>¬Good a σ) (fun _=>err) (by
      intro a ha
      have hc := finiteLaw_probability_compl (FiniteLaw.pi μ) (Good a)
      linarith only [hpair a,hc])
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Finset.mem_univ,true_implies,not_not] at hh
  have hpairs : (Fintype.card (U×U):ℝ)≤(Fintype.card V:ℝ)^2 := by
    have h := Nat.mul_le_mul huCard huCard
    simpa only [Fintype.card_prod,Nat.cast_mul,pow_two] using
      (show (Fintype.card U:ℝ)*Fintype.card U≤(Fintype.card V:ℝ)*Fintype.card V by exact_mod_cast h)
  have hsmall : (Fintype.card (U×U):ℝ)*err≤1/(Fintype.card V:ℝ)^Q := by
    dsimp [err]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (pow_pos hnR _)).mpr
    have heq : (1/(Fintype.card V:ℝ)^Q)*(Fintype.card V:ℝ)^(Q+3)=
        (Fintype.card V:ℝ)^2*Fintype.card V := by
      rw [pow_add]
      field_simp <;> ring
    rw [heq]
    calc
      _ ≤ (Fintype.card V:ℝ)^2*3 := mul_le_mul_of_nonneg_right hpairs (by norm_num)
      _ ≤ _ := mul_le_mul_of_nonneg_left (by exact_mod_cast (show 3≤Fintype.card V by omega)) (sq_nonneg _)
  apply (sub_le_sub_left hsmall 1).trans
  simpa only [Good,Prod.forall] using hh

end Oberwolfach

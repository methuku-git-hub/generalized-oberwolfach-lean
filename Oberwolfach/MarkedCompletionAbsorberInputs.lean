module

public import Oberwolfach.MarkedCompletionProfileRealization
public import Oberwolfach.MarkedRetainedExtensionEvent

@[expose] public section

/-! The actual retained experiment supplies all marked-absorber inputs
simultaneously. The parent weighting is fixed before the marginal arrays;
all count constants precede the small error and the permutation radius. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_completion_absorber_input_realization
    (k₀ r : ℕ) (hr : 1≤r) (hlen : r+4+1=(k₀+2)*2)
    (α₀ ρstar sstar ω : ℝ) (Q : ℕ) (hα₀ : 0<α₀)
    (hρstar : 0<ρstar) (hsstar : 0<sstar) (hω : 0<ω)
    (hmargin : successorCycleRatio k₀+α₀/2≤1/2+α₀) :
    let pstar := min (ρstar*sstar/(2*((r+4:ℕ):ℝ))) (sstar*sstar/((r+4:ℕ):ℝ))
    let pmin := min pstar (1/2)
    let γ := min α₀ (1/2)
    ∃ bc bp : ℝ,0<bc ∧ 0<bp ∧ ∀ η : ℝ,0<η →
    ∃ δ : ℝ,0<δ ∧ ∀ d : ℕ,∀ hd : 2≤d,∃ N : ℕ,1≤N ∧
    ∀ (V U Γ Color : Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [Nonempty V] [DecidableEq U],
      N≤Fintype.card V → ω*Fintype.card V≤(Fintype.card U:ℝ) → Fintype.card U≤Fintype.card V →
    ∀ (P : SimpleGraph V) (π : Equiv.Perm V),
      (∀ x l,0<l → l<2*d+1 → (π^l) x≠x) →
    ∀ D : ℝ,(Fintype.card V:ℝ)/2≤D → D≤2*Fintype.card V →
      (∀ v,|(P.degree v:ℝ)-D|≤δ*Fintype.card V) →
      (∀ v,(1/2+α₀)*Fintype.card V≤(P.degree v:ℝ)) →
    ∃ weight : (Fin (r+4+1)→V)→ℝ,
      SuccessorSequenceWeightConditions P π (3*d) D (η/4)
        (successorWeightLower k₀ (α₀/2)) (successorWeightUpper k₀ (α₀/2)) weight ∧
    ∀ (ρ s₀ : ℝ) (hρlo : ρstar≤ρ) (hρhi : ρ≤1) (hslo : sstar≤s₀) (hshi : s₀≤1/100),
    let densities := marked_seed_density_bounds (r+4) (by omega) ρ s₀ ρstar sstar hρstar hsstar hρlo hρhi hslo hshi
    let p := ρ*s₀/2
    let k := p/((r+4:ℕ):ℝ)
    ∀ (q : U→Γ→ℝ) (hq : ∀ u a,0≤q u a) (hQ : ∀ u,∑ a,q u a≤1/8)
      (s : U→Color→ℝ) (hs : ∀ u j,0≤s u j)
      (hS : ∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ a,q u a))
      (g : Γ) (j : Color),(∀ u,q u g=s₀/((r+4:ℕ):ℝ)) → (∀ u,s u j=s₀) →
    (∀ C : Fin (r+4+1)→V,
      SuccessorSequenceValid P π C → PermutationSeparated π (3*d) C →
      (successorWeightLower k₀ (α₀/2)/2)/(Fintype.card V:ℝ)^(r+4)≤
        weight C/(D*p^(r+4)*k*(s₀*s₀/((r+4:ℕ):ℝ))^(r+4)) ∧
      weight C/(D*p^(r+4)*k*(s₀*s₀/((r+4:ℕ):ℝ))^(r+4))≤
        (2*successorWeightUpper k₀ (α₀/2)/pstar^(2*(r+4)+1))/(Fintype.card V:ℝ)^(r+4)) ∧
    1-2/(Fintype.card V:ℝ)^Q≤
      (rawMarkedRetentionLaw π d hd g p k
        ((densities.1.trans_le densities.2.1).le)
        ((densities.1.trans_le densities.2.2.1).le)
        densities.2.2.2.2.2.2.2.2 q hq hQ s hs hS).probability
        (fun z=>let H:Bool→V→U→Prop := retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) g (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) g)) z.2 g j
          MarkedHostExtensionCounts
            (fun e:MarkedSampleArc P π (3*d) (fun e=>z.1 (Sum.inl e)) false=>e.val.1) (fun e=>e.val.2)
            (fun e:MarkedSampleArc P π (3*d) (fun e=>z.1 (Sum.inl e)) true=>e.val.1) (fun e=>e.val.2)
            (H false) (H true) π (3*d) r
            ((pmin^4*γ/4)*Fintype.card V) ((pmin^(r+11)*ω/2)*Fintype.card V)∧
          Nonempty (MarkedCommonPairCycleProfiles
          (fun e:MarkedSampleArc P π (3*d) (fun e=>z.1 (Sum.inl e)) false=>e.val.1) (fun e=>e.val.2)
          (fun e:MarkedSampleArc P π (3*d) (fun e=>z.1 (Sum.inl e)) true=>e.val.1) (fun e=>e.val.2)
          (fun v u=>retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) g
            (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) g)) z.2 g j false v u)
          (fun v u=>retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) g
            (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) g)) z.2 g j true v u)
          π (3*d) r ((sstar/((r+4:ℕ):ℝ))^2) (min bc bp)
          (successorWeightLower k₀ (α₀/2)/2)
          (2*successorWeightUpper k₀ (α₀/2)/pstar^(2*(r+4)+1)) η)) := by
  intro pstar pmin γ
  have hpstar:0<pstar:=by dsimp[pstar];positivity
  have hpmin:0<pmin:=lt_min hpstar (by norm_num)
  have hpmin1:pmin≤1:= (min_le_right _ _).trans (by norm_num)
  have hγ:0<γ:=lt_min hα₀ (by norm_num)
  have hγ1:γ≤1:= (min_le_right _ _).trans (by norm_num)
  have hγmargin:1/2+γ/2≤1/2+α₀:=by
    have hh:γ≤α₀:=min_le_left _ _
    linarith only [hh,hα₀]
  let pret:=ω*sstar/(2*((r+4:ℕ):ℝ))
  have hpret:0<pret:=by dsimp[pret];positivity
  obtain ⟨bc,bp,hbc,hbp,hbase⟩:=marked_common_completion_profile_realization k₀ r hr hlen α₀ ρstar sstar ω (Q+1) hα₀ hρstar hsstar hω hmargin
  refine ⟨bc,bp,hbc,hbp,?_⟩
  intro η hη
  obtain ⟨δ,hδ,hbase⟩:=hbase η hη
  refine ⟨δ,hδ,?_⟩
  intro d hd
  obtain ⟨Np,hNp,hbase⟩:=hbase d hd
  obtain ⟨Ne,hNe,hext⟩:=marked_retained_extension_event r d (Q+1) hd ω γ pmin pret hω hγ hγ1 hpmin hpmin1 hpret
  refine ⟨max 3 (max Np Ne),by omega,?_⟩
  intro V U Γ Color _ _ _ _ _ _ _ hn hUlo hUhi P π hπ D hDlo hDhi hnear hmin
  obtain ⟨weight,hw,hbase⟩:=hbase V U Γ Color (by omega) hUlo hUhi P π hπ D hDlo hDhi hnear hmin
  refine ⟨weight,hw,?_⟩
  intro ρ s₀ hρlo hρhi hslo hshi densities p k q hq hQ s hs hS g j hq₀ hs₀
  obtain ⟨hweights,hprofile⟩:=hbase ρ s₀ hρlo hρhi hslo hshi q hq hQ s hs hS g j hq₀ hs₀
  have hcount:=hext V U Γ Color (by omega) hUhi hUlo P π hπ
    (fun v=>(mul_le_mul_of_nonneg_right hγmargin (Nat.cast_nonneg _)).trans (hmin v))
    p k (densities.1.trans_le densities.2.1).le (densities.1.trans_le densities.2.2.1).le
    densities.2.2.2.2.2.2.2.2
    ((min_le_left _ _).trans ((min_le_left _ _).trans densities.2.1))
    ((min_le_left _ _).trans ((min_le_left _ _).trans densities.2.2.1))
    q hq hQ s hs hS g j (s₀/((r+4:ℕ):ℝ)) hq₀
    (marked_common_start_mass (r+4) (by omega) ω sstar s₀ (Fintype.card V) (Fintype.card U) hω hsstar hslo (Nat.cast_nonneg _) hUlo)
    (by
      intro u
      rw [hq₀]
      have hstar1:sstar≤1:=hslo.trans (hshi.trans (by norm_num))
      have hsquare:sstar*sstar≤s₀:=by nlinarith only [mul_nonneg hsstar.le (sub_nonneg.mpr hstar1),hslo]
      exact (min_le_left _ _).trans ((min_le_right _ _).trans
        (div_le_div_of_nonneg_right hsquare (by positivity))))
    (by
      intro u
      rw [hs₀]
      exact (min_le_left _ _).trans ((min_le_left _ _).trans densities.2.2.2.1))
  refine ⟨hweights,?_⟩
  let μ:=rawMarkedRetentionLaw π d hd g p k
    (densities.1.trans_le densities.2.1).le (densities.1.trans_le densities.2.2.1).le
    densities.2.2.2.2.2.2.2.2 q hq hQ s hs hS
  have hh:=(sub_le_sub_right hcount (2/(Fintype.card V:ℝ)^(Q+1))).trans
    (finiteLaw_good_intersection μ _ _ (2/(Fintype.card V:ℝ)^(Q+1)) hprofile)
  have hn3:3≤Fintype.card V:=by omega
  have hnum:=scaled_inverse_power_le (Fintype.card V) Q (by omega) 3 (by exact_mod_cast hn3)
  have hnum':(1/(Fintype.card V:ℝ)^(Q+1))+(2/(Fintype.card V:ℝ)^(Q+1))≤1/(Fintype.card V:ℝ)^Q:=by
    convert hnum using 1 <;> ring
  change 1-2/(Fintype.card V:ℝ)^Q≤μ.probability _
  have hdouble:1/(Fintype.card V:ℝ)^Q≤2/(Fintype.card V:ℝ)^Q:=
    div_le_div_of_nonneg_right (by norm_num) (by positivity)
  apply le_trans ?_ hh
  linarith only [hnum',hdouble]

end Oberwolfach

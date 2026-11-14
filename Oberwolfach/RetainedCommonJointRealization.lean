module

public import Oberwolfach.RetainedCommonJointWitness
public import Oberwolfach.CommonWitnessMargins
public import Oberwolfach.SuccessorWeightFamilies

@[expose] public section

/-! Construct the shared parent weighting and the complete retained common
witness. The order threshold is uniform over the host and all permitted
marginal arrays. One selector per pair supplies every estimate jointly. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3400000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem retainedMarked_common_joint_realization
    (k₀ r : ℕ) (hr : 1≤r) (hlen : r+4+1=(k₀+2)*2)
    (β astar pstar pret ω : ℝ) (Q : ℕ)
    (hβ : 0<β) (hastar : 0<astar) (hpstar : 0<pstar)
    (hpret : 0<pret) (hω : 0<ω) :
    ∃ bc bp : ℝ,0<bc ∧ 0<bp ∧ ∀ η : ℝ,0<η →
    ∃ δ : ℝ,0<δ ∧ ∀ d : ℕ,∀ hd : 2≤d,
    ∃ N : ℕ,1≤N ∧ ∀ (V U Γ Color : Type)
      [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [LinearOrder V] [Nonempty V] [DecidableEq U],
      N≤Fintype.card V → ω*Fintype.card V≤(Fintype.card U:ℝ) → Fintype.card U≤Fintype.card V →
    ∀ (P : SimpleGraph V) (π : Equiv.Perm V),
      (∀ x l,0<l → l<2*d+1 → (π^l) x≠x) →
    ∀ D : ℝ,(Fintype.card V:ℝ)/2≤D → D≤2*Fintype.card V →
      (∀ v,|(P.degree v:ℝ)-D|≤δ*Fintype.card V) →
      (∀ v,(successorCycleRatio k₀+β)*Fintype.card V≤(P.degree v:ℝ)) →
    ∃ weight : (Fin (r+4+1)→V)→ℝ,
      SuccessorSequenceWeightConditions P π (3*d) D (η/4)
        (successorWeightLower k₀ β) (successorWeightUpper k₀ β) weight ∧
    ∀ (p k s₀ : ℝ) (hp : 0<p) (hk : 0<k) (hphys : 2*p+2*k≤1),
      0<s₀ → pstar≤p → pstar≤k →
      pstar≤s₀*s₀/((r+4:ℕ):ℝ) → s₀*s₀/((r+4:ℕ):ℝ)≤1 →
      astar≤(s₀/((r+4:ℕ):ℝ))*(s₀/((r+4:ℕ):ℝ)) → astar≤s₀*s₀/((r+4:ℕ):ℝ) →
    ∀ (q : U→Γ→ℝ) (hq : ∀ u a,0≤q u a) (hQ : ∀ u,∑ a,q u a≤1/8)
      (s : U→Color→ℝ) (hs : ∀ u j,0≤s u j)
      (hS : ∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ a,q u a))
      (g : Γ) (j : Color),(∀ u,q u g=s₀/((r+4:ℕ):ℝ)) → (∀ u,s u j=s₀) →
      pret*Fintype.card V≤(s₀/((r+4:ℕ):ℝ))*Fintype.card U →
    (∀ C : Fin (r+4+1)→V,
      SuccessorSequenceValid P π C → PermutationSeparated π (3*d) C →
      (successorWeightLower k₀ β/2)/(Fintype.card V:ℝ)^(r+4)≤
        weight C/(D*p^(r+4)*k*(s₀*s₀/((r+4:ℕ):ℝ))^(r+4)) ∧
      weight C/(D*p^(r+4)*k*(s₀*s₀/((r+4:ℕ):ℝ))^(r+4))≤
        (2*successorWeightUpper k₀ β/pstar^(2*(r+4)+1))/(Fintype.card V:ℝ)^(r+4)) ∧
    1-2/(Fintype.card V:ℝ)^Q≤
      (rawMarkedRetentionLaw π d hd g p k hp.le hk.le hphys q hq hQ s hs hS).probability
        (fun z=>∀ u u',u≠u' → ∃ κ,
          CommonWitnessEstimates P π d r D p k s₀ η η η bc bp weight z.1
            (retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) g
              (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) g)) z.2 g j) κ u u') := by
  let α := min β (1/2)
  have hα : 0<α := lt_min hβ (by norm_num)
  have hα1 : α≤1/2 := min_le_right _ _
  have hαβ : α≤β := min_le_left _ _
  obtain ⟨hA,hB⟩ := successorWeightConstants_pos k₀ β hβ
  let B := successorWeightUpper k₀ β
  let C := 10*((r+4:ℕ)+1:ℝ)^4*(2*B/pstar^(2*(r+4)+1))
  let bc₀ := pstar^(r+5)*(α*(astar/2)/4)^(r+5)/2
  let bp₀ := pstar^(r+7)*(α*(astar/2)/4)^(r+4)/2
  have hC : 0≤C := by dsimp [C,B];positivity
  have hbc : 0<bc₀ := by dsimp [bc₀];positivity
  have hbp : 0<bp₀ := by dsimp [bp₀];positivity
  refine ⟨bc₀/2,bp₀/2,by positivity,by positivity,?_⟩
  intro η hη
  obtain ⟨ζ,hζ,hsize,hover,hload,hcycle,hpath⟩ := commonWitness_error_margins r C bc₀ bp₀ η hC hbc hbp hη
  obtain ⟨δ,hδ,hweights⟩ := successor_sequence_weight_existence k₀ β hβ (η/4) (by positivity)
  refine ⟨δ,hδ,?_⟩
  intro d hd
  obtain ⟨NW,hNW⟩ := hweights (3*d)
  obtain ⟨M,NR,hM1,hNR1,hret⟩ := retainedMarked_common_joint_witness_event r hr α astar pstar B
    (η/4) (η/4) pret ζ hα hα1 hastar hpstar hB (by positivity) (by positivity) hpret hζ d Q hd
  let N := max 1 (max NW (max NR (max M (Nat.ceil ((M:ℝ)/ω)))))
  refine ⟨N,le_max_left _ _,?_⟩
  intro V U Γ Color _ _ _ _ _ _ _ hn huLo hu P π hnoshort D hDlo hDhi hnear hmin
  have hNW' : NW≤Fintype.card V := by dsimp [N] at hn;omega
  have hNR' : NR≤Fintype.card V := by dsimp [N] at hn;omega
  have hMV : M≤Fintype.card V := by dsimp [N] at hn;omega
  have hceil : Nat.ceil ((M:ℝ)/ω)≤Fintype.card V := by dsimp [N] at hn;omega
  have hMU : M≤Fintype.card U := by
    have hh : (M:ℝ)/ω≤(Fintype.card V:ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hceil)
    have hh' := (div_le_iff₀ hω).mp hh
    have hh'' : (M:ℝ)≤Fintype.card U := by nlinarith only [hh',huLo]
    exact_mod_cast hh''
  have hP : ∀ v,(1/2+α)*Fintype.card V≤(P.degree v:ℝ) := by
    intro v
    exact (mul_le_mul_of_nonneg_right (add_le_add (successorCycleRatio_half_le k₀) hαβ)
      (Nat.cast_nonneg _)).trans (hmin v)
  have hex := hNW V hNW' P π D hDlo hDhi hnear hmin
  rw [← hlen] at hex
  obtain ⟨weight,hw⟩ := hex
  refine ⟨weight,hw,?_⟩
  intro p k s₀ hp hk hphys hs₀ hpmin hkmin hsmin hs1 hqclass hsclass q hq hQ s hs hS g j hq₀ hs₀' hmass
  constructor
  · intro C hvalid hsep
    have hnpos : 0<Fintype.card V := by dsimp [N] at hn;omega
    exact ⟨successor_seed_positive_lower hw (by omega) hnpos hDlo hDhi p k
      (s₀*s₀/((r+4:ℕ):ℝ)) pstar hpstar hpmin hkmin hsmin (by linarith) (by linarith) hs1 hA.le hB.le C hvalid hsep,
      (successor_seed_nonneg_upper hw (by omega) hnpos hDlo hDhi p k
      (s₀*s₀/((r+4:ℕ):ℝ)) pstar hpstar hpmin hkmin hsmin (by linarith) (by linarith) hs1 hB.le C).2⟩
  · have hh := hret V U Γ Color hNR' hMV hMU hu P π hP hnoshort p k hp hk hphys hpmin hkmin
      q hq hQ s hs hS g j s₀ D (η/4) (successorWeightLower k₀ β) hs₀ hq₀ hs₀' hsmin hs1
      hqclass hsclass hmass weight hw hDlo hDhi
    apply hh.trans
    apply finiteLaw_probability_mono
    intro z hz u u' huu
    obtain ⟨κ,hκ⟩ := hz u u' huu
    exact ⟨κ,commonWitnessEstimates_mono P π d r D p k s₀ weight z.1 _ κ u u'
      hsize hover hload hcycle hpath hκ⟩

end Oberwolfach

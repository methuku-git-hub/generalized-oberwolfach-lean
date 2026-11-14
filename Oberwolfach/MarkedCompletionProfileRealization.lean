module

public import Oberwolfach.CommonCompletionRealization
public import Oberwolfach.MarkedCommonWitnessProfiles
public import Oberwolfach.MarkedProfileMonotonicity

@[expose] public section

/-! The retained completion experiment supplies the actual common-cycle
profiles used by the marked absorber. Count and density lower bounds
precede the error tolerance and all actual sampling marginals. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_common_completion_profile_realization
    (k₀ r : ℕ) (hr : 1≤r) (hlen : r+4+1=(k₀+2)*2)
    (α₀ ρstar sstar ω : ℝ) (Q : ℕ) (hα₀ : 0<α₀)
    (hρstar : 0<ρstar) (hsstar : 0<sstar) (hω : 0<ω)
    (hmargin : successorCycleRatio k₀+α₀/2≤1/2+α₀) :
    let pstar := min (ρstar*sstar/(2*((r+4:ℕ):ℝ))) (sstar*sstar/((r+4:ℕ):ℝ))
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
        (fun z=>Nonempty (MarkedCommonPairCycleProfiles
          (fun e:MarkedSampleArc P π (3*d) (fun e=>z.1 (Sum.inl e)) false=>e.val.1) (fun e=>e.val.2)
          (fun e:MarkedSampleArc P π (3*d) (fun e=>z.1 (Sum.inl e)) true=>e.val.1) (fun e=>e.val.2)
          (fun v u=>retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) g
            (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) g)) z.2 g j false v u)
          (fun v u=>retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) g
            (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) g)) z.2 g j true v u)
          π (3*d) r ((sstar/((r+4:ℕ):ℝ))^2) (min bc bp)
          (successorWeightLower k₀ (α₀/2)/2)
          (2*successorWeightUpper k₀ (α₀/2)/pstar^(2*(r+4)+1)) η)) := by
  intro pstar
  obtain ⟨bc,bp,hbc,hbp,hbase⟩:=marked_common_completion_realization k₀ r hr hlen α₀ ρstar sstar ω Q hα₀ hρstar hsstar hω hmargin
  refine ⟨bc,bp,hbc,hbp,?_⟩
  intro η hη
  obtain ⟨δ,hδ,hbase⟩:=hbase η hη
  refine ⟨δ,hδ,?_⟩
  intro d hd
  obtain ⟨N,hN,hbase⟩:=hbase d hd
  refine ⟨N,hN,?_⟩
  intro V U Γ Color _ _ _ _ _ _ _ hn hUlo hUhi P π hπ D hDlo hDhi hnear hmin
  obtain ⟨weight,hw,hbase⟩:=hbase V U Γ Color hn hUlo hUhi P π hπ D hDlo hDhi hnear hmin
  refine ⟨weight,hw,?_⟩
  intro ρ s₀ hρlo hρhi hslo hshi densities p k q hq hQ s hs hS g j hq₀ hs₀
  obtain ⟨hweights,hevent⟩:=hbase ρ s₀ hρlo hρhi hslo hshi q hq hQ s hs hS g j hq₀ hs₀
  refine ⟨hweights,hevent.trans ?_⟩
  apply finiteLaw_probability_mono
  intro z hz
  let H:=retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) g
    (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) g)) z.2 g j
  obtain ⟨Profiles⟩:=marked_common_witness_profiles P π d r D p k s₀ η bc bp
    (successorWeightLower k₀ (α₀/2)/2) (2*successorWeightUpper k₀ (α₀/2)/pstar^(2*(r+4)+1))
    weight z.1 H hweights hz
  refine ⟨Profiles.lowerDensity ?_⟩
  have h0:0≤sstar/((r+4:ℕ):ℝ):=by positivity
  exact pow_le_pow_left₀ h0 (div_le_div_of_nonneg_right hslo (by positivity)) 2

end Oberwolfach

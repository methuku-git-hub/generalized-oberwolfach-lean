module

public import Oberwolfach.RetainedCommonJointRealization
public import Oberwolfach.CommonMarkedDensityBounds

@[expose] public section

/-! The common-witness construction with the density formulas actually
used in marked completion. All positive count constants precede the error
tolerance, separation length, host and actual marginal arrays. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3400000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_common_completion_realization
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
        (fun z=>∀ u u',u≠u' → ∃ κ,
          CommonWitnessEstimates P π d r D p k s₀ η η η bc bp weight z.1
            (retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) g
              (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) g)) z.2 g j) κ u u') := by
  intro pstar
  let astar := (sstar/((r+4:ℕ):ℝ))*(sstar/((r+4:ℕ):ℝ))
  let pret := ω*sstar/(2*((r+4:ℕ):ℝ))
  have hpstar : 0<pstar := by dsimp [pstar];positivity
  have hastar : 0<astar := by dsimp [astar];positivity
  have hpret : 0<pret := by dsimp [pret];positivity
  obtain ⟨bc,bp,hbc,hbp,hreal⟩ := retainedMarked_common_joint_realization k₀ r hr hlen
    (α₀/2) astar pstar pret ω Q (by positivity) hastar hpstar hpret hω
  refine ⟨bc,bp,hbc,hbp,?_⟩
  intro η hη
  obtain ⟨δ,hδ,hδreal⟩ := hreal η hη
  refine ⟨δ,hδ,?_⟩
  intro d hd
  obtain ⟨N,hN,hNreal⟩ := hδreal d hd
  refine ⟨N,hN,?_⟩
  intro V U Γ Color _ _ _ _ _ _ _ hn huLo hu P π hnoshort D hDlo hDhi hnear hmin
  have hmin' : ∀ v,(successorCycleRatio k₀+α₀/2)*Fintype.card V≤(P.degree v:ℝ) :=
    fun v=>(mul_le_mul_of_nonneg_right hmargin (Nat.cast_nonneg _)).trans (hmin v)
  obtain ⟨weight,hw,hweight⟩ := hNreal V U Γ Color hn huLo hu P π hnoshort D hDlo hDhi hnear hmin'
  refine ⟨weight,hw,?_⟩
  intro ρ s₀ hρlo hρhi hslo hshi densities p k q hq hQ s hs hS g j hq₀ hs₀'
  obtain ⟨hps,has,hpp,hpk,hpsbar,hsbar1,hqa,hsa,hp,hk,hphys⟩ :=
    marked_common_density_bounds (r+4) (by omega) ρ s₀ ρstar sstar hρstar hsstar hρlo hρhi hslo hshi
  have hmass := marked_common_start_mass (r+4) (by omega) ω sstar s₀
    (Fintype.card V) (Fintype.card U) hω hsstar hslo (Nat.cast_nonneg _) huLo
  exact hweight p k s₀ hp hk hphys (hsstar.trans_le hslo) hpp hpk hpsbar hsbar1 hqa hsa
    q hq hQ s hs hS g j hq₀ hs₀' hmass

end Oberwolfach

module

public import Oberwolfach.RetainedCommonWeightWitness
public import Oberwolfach.SuccessorWeightFamilies

@[expose] public section

/-! Construct the shared parent weighting before sampling and choose a
uniform order threshold for its common-witness loads after retention.
This proves the weighted component of the common-witness input; it does
not assert the additional thinned cycle/path counts needed for absorption. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem retainedMarked_common_weight_realization
    (k₀ m : ℕ) (hlen : m+1=(k₀+2)*2) (β τ pstar ε pret ζ ω : ℝ) (Q : ℕ)
    (hβ : 0<β) (hτ : 0<τ) (hpstar : 0<pstar) (hε : 0<ε)
    (hpret : 0<pret) (hζ : 0<ζ) (hω : 0<ω) :
    ∃ δ : ℝ,0<δ ∧ ∀ d : ℕ,∀ hd : 2≤d,∃ N : ℕ,1≤N ∧
    ∀ (V U Γ Color : Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [Nonempty V] [DecidableEq U],
    N≤Fintype.card V → ω*Fintype.card V≤(Fintype.card U:ℝ) → Fintype.card U≤Fintype.card V →
    ∀ (P : SimpleGraph V) (π : Equiv.Perm V),
      (∀ x l,0<l → l<2*d+1 → (π^l) x≠x) →
    ∀ D : ℝ,(Fintype.card V:ℝ)/2≤D → D≤2*Fintype.card V →
      (∀ v,|(P.degree v:ℝ)-D|≤δ*Fintype.card V) →
      (∀ v,(successorCycleRatio k₀+β)*Fintype.card V≤(P.degree v:ℝ)) →
    ∃ weight : (Fin (m+1)→V)→ℝ,
      SuccessorSequenceWeightConditions P π (3*d) D τ
        (successorWeightLower k₀ β) (successorWeightUpper k₀ β) weight ∧
    ∀ (p k s₀ : ℝ) (hp : 0<p) (hk : 0<k) (hphys : 2*p+2*k≤1),
      0<s₀ → pstar≤p → pstar≤k → pstar≤s₀*s₀/m → p≤1 → k≤1 → s₀*s₀/m≤1 →
    ∀ (q : U→Γ→ℝ) (hq : ∀ u a,0≤q u a) (hQ : ∀ u,∑ a,q u a≤1/8)
      (s : U→Color→ℝ) (hs : ∀ u j,0≤s u j)
      (hS : ∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ a,q u a))
      (g : Γ) (j : Color),(∀ u,q u g=s₀/m) → (∀ u,s u j=s₀) →
      pret*Fintype.card V≤(s₀/m)*Fintype.card U →
    1-2/(Fintype.card V:ℝ)^Q≤
    (rawMarkedRetentionLaw π d hd g p k hp.le hk.le hphys q hq hQ s hs hS).probability
      (fun z=>∀ u u',u≠u' → ∃ κ,CommonPotentialSpokeLoads P π d m D p k (s₀*s₀/m) weight
        (τ+ε+10*((m:ℝ)+1)^4*(2*successorWeightUpper k₀ β/pstar^(2*m+1))*ζ) z.1
        (retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) g
          (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) g)) z.2 g j) κ u u') := by
  have hm : 3≤m := by omega
  obtain ⟨hA,hB⟩ := successorWeightConstants_pos k₀ β hβ
  obtain ⟨δ,hδ,hweights⟩ := successor_sequence_weight_existence k₀ β hβ τ hτ
  refine ⟨δ,hδ,?_⟩
  intro d hd
  obtain ⟨NW,hNW⟩ := hweights (3*d)
  obtain ⟨M,NR,hM1,hNR1,hret⟩ := retainedMarked_common_weight_event m d hm hd
    (successorWeightUpper k₀ β) pstar ε Q pret ζ hB hpstar hε hpret hζ
  let c := commonWeightLoadExponent m d (2*successorWeightUpper k₀ β/pstar^(2*m+1)) ε
  have hc : 0<c := commonWeightLoadExponent_pos m d _ ε (by positivity) hε
  obtain ⟨NE,hNE⟩ := eventually_stretchedExp_le_inv_pow 8 4 hc (p:=1) (by norm_num) Q
  let N := max 1 (max NW (max NR (max M (max NE (Nat.ceil ((M:ℝ)/ω))))))
  refine ⟨N,le_max_left _ _,?_⟩
  intro V U Γ Color _ _ _ _ _ _ _ hn huLo hu P π hnoshort D hDlo hDhi hnear hmin
  have hNW' : NW≤Fintype.card V := by dsimp [N] at hn;omega
  have hNR' : NR≤Fintype.card V := by dsimp [N] at hn;omega
  have hMV : M≤Fintype.card V := by dsimp [N] at hn;omega
  have hNE' : NE≤Fintype.card V := by dsimp [N] at hn;omega
  have hceil : Nat.ceil ((M:ℝ)/ω)≤Fintype.card V := by dsimp [N] at hn;omega
  have hMU : M≤Fintype.card U := by
    have hh : (M:ℝ)/ω≤(Fintype.card V:ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hceil)
    have hh' := (div_le_iff₀ hω).mp hh
    have hh'' : (M:ℝ)≤Fintype.card U := by nlinarith only [hh',huLo]
    exact_mod_cast hh''
  have hex := hNW V hNW' P π D hDlo hDhi hnear hmin
  rw [← hlen] at hex
  obtain ⟨weight,hw⟩ := hex
  refine ⟨weight,hw,?_⟩
  intro p k s₀ hp hk hphys hs₀ hpmin hkmin hsmin hp1 hk1 hs1 q hq hQ s hs hS g j hq₀ hs₀' hmass
  have hh := hret V U Γ Color hNR' hMV hMU hu P π hnoshort D τ (successorWeightLower k₀ β)
    weight hw hDlo hDhi p k s₀ hp hk hphys hs₀ hpmin hkmin hsmin hp1 hk1 hs1
    q hq hQ s hs hS g j hq₀ hs₀' hmass
  have htail := hNE (Fintype.card V) hNE'
  norm_num only [Real.rpow_ofNat,Real.rpow_one] at htail
  have hpow : (Fintype.card V:ℝ)^(-(Q:ℝ))=1/(Fintype.card V:ℝ)^Q := by
    rw [Real.rpow_neg (Nat.cast_nonneg _),Real.rpow_natCast,inv_eq_one_div]
  rw [hpow] at hh
  change 8*(Fintype.card V:ℝ)^4*Real.exp (-c*Fintype.card V)≤1/(Fintype.card V:ℝ)^Q at htail
  change 1-8*(Fintype.card V:ℝ)^4*Real.exp (-c*Fintype.card V)-1/(Fintype.card V:ℝ)^Q≤_ at hh
  calc
    1-2/(Fintype.card V:ℝ)^Q = 1-1/(Fintype.card V:ℝ)^Q-1/(Fintype.card V:ℝ)^Q := by ring
    _ ≤ _ := (sub_le_sub_right (sub_le_sub_left htail 1) _).trans hh

end Oberwolfach

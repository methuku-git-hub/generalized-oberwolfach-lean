module

public import Oberwolfach.MarkedReferenceAfterPhysicalDeletion
public import Oberwolfach.MarkedCommonConfigurationsAfterPhysicalDeletion

@[expose] public section

/-! The full-domain degree, cut, configuration and neighbourhood inputs
for the next cover-down step, with one explicit target accuracy. The
reference arrays and original targets are unchanged by the deletion. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color : Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [LinearOrder V] [DecidableEq U]

theorem marked_spoke_reference_change_after_deletion
    (π : Equiv.Perm V) (d : ℕ) (σ : RawMarkedOutcome V U Γ Color)
    (g : Γ) (j : Color) (H : Bool→V→U→Prop)
    (DR : SimpleGraph V) (DS : SimpleGraph (V⊕U)) (eR eC δ : ℝ)
    (hrow : ∀ b x,(∑ u,if ¬(rawMarkedPairSpokes π d σ g j b x u↔H b x u) then (1:ℝ) else 0)≤eR)
    (hcol : ∀ b u,(∑ x,if ¬(rawMarkedPairSpokes π d σ g j b x u↔H b x u) then (1:ℝ) else 0)≤eC)
    (hDS : ∀ z,(DS.degree z:ℝ)≤δ) :
    (∀ b x,(∑ u,if ¬(rawMarkedPairSpokes π d (rawMarkedDeleteRims σ DR.edgeFinset) g j b x u↔
      markedDeletePhysicalSpokes H DS b x u) then (1:ℝ) else 0)≤eR+δ) ∧
    (∀ b u,(∑ x,if ¬(rawMarkedPairSpokes π d (rawMarkedDeleteRims σ DR.edgeFinset) g j b x u↔
      markedDeletePhysicalSpokes H DS b x u) then (1:ℝ) else 0)≤eC+δ) := by
  have tri (a b c : Prop) : (if ¬(a↔c) then (1:ℝ) else 0)≤
      (if ¬(a↔b) then (1:ℝ) else 0)+(if ¬(b↔c) then (1:ℝ) else 0) := by
    by_cases ha:a <;> by_cases hb:b <;> by_cases hc:c <;> simp [ha,hb,hc]
  constructor
  · intro b x
    have hchange := (marked_spoke_physical_deletion_row_change H DS Finset.univ b x).trans (hDS (Sum.inl x))
    calc
      _ ≤ (∑ u,if ¬(rawMarkedPairSpokes π d σ g j b x u↔H b x u) then (1:ℝ) else 0)+
          (∑ u,if ¬(H b x u↔markedDeletePhysicalSpokes H DS b x u) then (1:ℝ) else 0) := by
        rw [←Finset.sum_add_distrib]
        apply Finset.sum_le_sum
        intro u _
        exact tri (rawMarkedPairSpokes π d σ g j b x u) (H b x u) (markedDeletePhysicalSpokes H DS b x u)
      _ ≤ eR+δ := add_le_add (hrow b x) hchange
  · intro b u
    have hchange := (marked_spoke_physical_deletion_column_change H DS Finset.univ b u).trans (hDS (Sum.inr u))
    calc
      _ ≤ (∑ x,if ¬(rawMarkedPairSpokes π d σ g j b x u↔H b x u) then (1:ℝ) else 0)+
          (∑ x,if ¬(H b x u↔markedDeletePhysicalSpokes H DS b x u) then (1:ℝ) else 0) := by
        rw [←Finset.sum_add_distrib]
        apply Finset.sum_le_sum
        intro x _
        exact tri (rawMarkedPairSpokes π d σ g j b x u) (H b x u) (markedDeletePhysicalSpokes H DS b x u)
      _ ≤ eC+δ := add_le_add (hcol b u) hchange

theorem marked_reference_input_stability
    (r h : ℕ) (P : SimpleGraph V) (π : Equiv.Perm V) (d : ℕ) (g : Γ) (j : Color)
    (D p k s₀ t₀ β ε κ γ ζ omega : ℝ) (hζ : 0≤ζ) (hγ : 0≤γ)
    (hn : 0<Fintype.card V) (hU : omega*Fintype.card V≤(Fintype.card U:ℝ))
    (hε : ε+ζ≤κ) (hcommon : ε+4*ζ≤κ) (hrows : ε+2*h*ζ≤κ) (hidx : ε+h*ζ≤κ)
    (hspoke : ζ≤(κ-ε)*omega) (hke : ε≤κ)
    (hstat : 2*ζ≤(3/4)*γ*p^2) (hcut : ζ≤γ*min p k/8)
    (q : U→Γ→ℝ) (s : U→Color→ℝ) (σ : RawMarkedOutcome V U Γ Color) (H : Bool→V→U→Prop)
    (hStats : MarkedReferenceStatistics P π d g j D ε κ γ p k s₀ t₀ σ)
    (hCuts : MarkedReferenceCutFamilies P π d g j γ p k t₀ σ)
    (hCommon : MarkedCommonConfigurationsWithSpokes r P π d β ε σ H)
    (hRows : MarkedRowsWithSpokes P π d h Finset.univ p k q s g j (ε*Fintype.card V) σ H)
    (hIndices : MarkedIndicesWithSpokes π d h Finset.univ q s g j (ε*Fintype.card V) σ H)
    (hrow : ∀ b x,(∑ u,if ¬(rawMarkedPairSpokes π d σ g j b x u↔H b x u) then (1:ℝ) else 0)≤ε*Fintype.card U)
    (hcol : ∀ b u,(∑ x,if ¬(rawMarkedPairSpokes π d σ g j b x u↔H b x u) then (1:ℝ) else 0)≤ε*Fintype.card V)
    (DR : SimpleGraph V) (DS : SimpleGraph (V⊕U))
    (hDR : ∀ x,(DR.degree x:ℝ)≤ζ*Fintype.card V)
    (hDS : ∀ z,(DS.degree z:ℝ)≤ζ*Fintype.card V) :
    let σ' := rawMarkedDeleteRims σ DR.edgeFinset
    let H' := markedDeletePhysicalSpokes H DS;
    MarkedReferenceStatistics P π d g j D κ κ (γ/2) p k s₀ t₀ σ' ∧
    MarkedReferenceCutFamilies P π d g j (γ/2) p k t₀ σ' ∧
    MarkedCommonConfigurationsWithSpokes r P π d β κ σ' H' ∧
    MarkedRowsWithSpokes P π d h Finset.univ p k q s g j (κ*Fintype.card V) σ' H' ∧
    MarkedIndicesWithSpokes π d h Finset.univ q s g j (κ*Fintype.card V) σ' H' ∧
    (∀ b x,(∑ u,if ¬(rawMarkedPairSpokes π d σ' g j b x u↔H' b x u) then (1:ℝ) else 0)≤κ*Fintype.card U) ∧
    (∀ b u,(∑ x,if ¬(rawMarkedPairSpokes π d σ' g j b x u↔H' b x u) then (1:ℝ) else 0)≤κ*Fintype.card V) := by
  intro σ' H'
  have hn0 : (Fintype.card V:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hn
  have hnle : (0:ℝ)≤Fintype.card V := Nat.cast_nonneg _
  have hr := marked_reference_statistics_after_physical_deletion P π d g j D ε κ γ (γ/2) p k s₀ t₀ ζ σ DR hDR
    (by nlinarith only [hstat]) hStats
  have he := mul_le_mul_of_nonneg_right hε hnle
  have hstats : MarkedReferenceStatistics P π d g j D κ κ (γ/2) p k s₀ t₀ σ' := by
    refine ⟨⟨?_,hr.1.2⟩,hr.2⟩
    intro b x
    exact ⟨(hr.1.1 b x).1.trans he,(hr.1.1 b x).2.trans he⟩
  have hcuts := marked_reference_cuts_after_physical_deletion P π d g j γ (γ/2) p k t₀ ζ
    (by linarith only [hγ]) hζ (by
      intro b
      have hb : min p k≤(if b then k else p) := by cases b;exact min_le_left _ _;exact min_le_right _ _
      have hb' := mul_le_mul_of_nonneg_left hb hγ
      nlinarith only [hcut,hb']) σ DR hDR hCuts
  have hc := marked_common_configurations_after_physical_deletion r P π d β ε (ζ*Fintype.card V)
    (mul_nonneg hζ hnle) hn σ H DR DS hDR hDS hCommon
  have hec : ε+4*(ζ*Fintype.card V)/(Fintype.card V:ℝ)=ε+4*ζ := by field_simp
  rw [hec] at hc
  have hcommon' : MarkedCommonConfigurationsWithSpokes r P π d β κ σ' H' := by
    constructor
    · intro C hC
      have hh := hc.1 C hC
      have hl := mul_le_mul_of_nonneg_left hcommon (show (0:ℝ)≤(r+5:ℕ)*Fintype.card V by positivity)
      nlinarith only [hh,hl]
    constructor
    · intro u hu
      have hh := hc.2.1 u hu
      have hl := mul_le_mul_of_nonneg_left hcommon (show (0:ℝ)≤2*(r+5:ℕ)*(Fintype.card V:ℝ)^(r+5) by positivity)
      nlinarith only [hh,hl]
    · intro v v' hv u hu b
      have hh := hc.2.2 v v' hv u hu b
      have hl := mul_le_mul_of_nonneg_left hcommon (show (0:ℝ)≤2*(r+4:ℕ)*(Fintype.card V:ℝ)^(r+4) by positivity)
      nlinarith only [hh,hl]
  obtain ⟨hrows',hidx'⟩ := marked_neighbourhoods_after_physical_deletion P π d h Finset.univ Finset.univ
    p k q s g j (ε*Fintype.card V) (ε*Fintype.card V) (ζ*Fintype.card V) (ζ*Fintype.card V) (ζ*Fintype.card V)
    (mul_nonneg hζ hnle) (mul_nonneg hζ hnle) (mul_nonneg hζ hnle) σ H hRows hIndices DR DS hDR
    (fun x=>hDS (Sum.inl x)) (fun u=>hDS (Sum.inr u))
  obtain ⟨hsr,hsc⟩ := marked_spoke_reference_change_after_deletion π d σ g j H DR DS
    (ε*Fintype.card U) (ε*Fintype.card V) (ζ*Fintype.card V) hrow hcol hDS
  have hRowBudget : ε*Fintype.card V+h*(ζ*Fintype.card V+ζ*Fintype.card V)≤κ*Fintype.card V := by
    nlinarith only [mul_le_mul_of_nonneg_right hrows hnle]
  have hIdxBudget : ε*Fintype.card V+h*(ζ*Fintype.card V)≤κ*Fintype.card V := by
    nlinarith only [mul_le_mul_of_nonneg_right hidx hnle]
  have hSpokeBudget : ε*Fintype.card U+ζ*Fintype.card V≤κ*Fintype.card U := by
    have hs := mul_le_mul_of_nonneg_right hspoke hnle
    have hu := mul_le_mul_of_nonneg_left hU (sub_nonneg.mpr hke)
    nlinarith only [hs,hu]
  refine ⟨hstats,hcuts,hcommon',?_,?_,?_,?_⟩
  · intro S T J hS hT hJ hinj
    exact (hrows' S T J hS hT hJ hinj).trans_le hRowBudget
  · intro J hJ hsep
    exact (hidx' J hJ hsep).trans_le hIdxBudget
  · intro b x
    exact (hsr b x).trans hSpokeBudget
  · intro b u
    exact (hsc b u).trans (by nlinarith only [he])

end Oberwolfach

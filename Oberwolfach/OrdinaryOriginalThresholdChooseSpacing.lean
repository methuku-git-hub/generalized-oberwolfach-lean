module

public import Oberwolfach.OrdinaryOriginalThresholdAfterSpacing

@[expose] public section
/-! The requested spacing bound can be chosen after the matching tolerance
while retaining the full original selector at the chosen spacing. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach

theorem ordinary_original_threshold_choose_spacing
    (L rstar:ℕ) (βfreq ρ₀ α:ℝ) (hr:3 ≤ rstar) (hβfreq:0<βfreq) (hβ1:βfreq ≤ 1)
    (hρ₀:0<ρ₀) (hα:0<α) (m k:ℕ)
    (hAt:OrdinaryOriginalThresholdFamilyAt L rstar βfreq ρ₀ α hr hβfreq hβ1 hρ₀ hα m k)
    (θ:ℝ) (hθ:0<θ) (hθ1:θ ≤ 1/100) (dNeed:ℕ):
    ∃βList lamList ζDel smin:ℝ,0<βList ∧ βList ≤ 1 ∧ 0<lamList ∧ 0<ζDel ∧ 0<smin ∧ smin=βfreq/200 ∧
    ∃d K rank:ℕ,dNeed ≤ d ∧ 2 ≤ d ∧ 3 ≤ K ∧ rstar ≤ K ∧ 2 ≤ rank ∧ 2*(m+1) ≤ rank ∧
      (∀i:Fin K,2*(longPaddedSeedExponent i+2) ≤ rank) ∧
      1/θ ≤ (d:ℝ) ∧ 1/(4*(d:ℝ)) ≤ 5*θ^2/256 ∧ 1/(2*(K:ℝ)) ≤ βfreq ∧
      5/(((m:ℝ)+1)*(d:ℝ)+5)+((m:ℝ)+1)*(d:ℝ)/(K:ℝ) ≤ θ/2 ∧
      OrdinaryOriginalThresholdAfterSpacing rstar m k d K rank βfreq ρ₀ α θ βList lamList ζDel smin :=by
  obtain ⟨_,_,_,_,_,hselect⟩:=hAt
  obtain ⟨βList,lamList,ζDel,smin,hβList,hβList1,hlamList,hζDel,hsmin,hsminEq,hspacing⟩:=hselect θ hθ hθ1
  obtain ⟨d,K,rank,hNeed,hd,hK,hrK,hrank,hrankm,hrankO,hdθ,hspace,hβK,hcap,hpost⟩:=hspacing dNeed
  exact ⟨βList,lamList,ζDel,smin,hβList,hβList1,hlamList,hζDel,hsmin,hsminEq,
    d,K,rank,hNeed,hd,hK,hrK,hrank,hrankm,hrankO,hdθ,hspace,hβK,hcap,hpost⟩
end Oberwolfach

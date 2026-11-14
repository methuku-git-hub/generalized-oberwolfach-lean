module

public import Oberwolfach.CommonJointWitnessEvent
public import Oberwolfach.CommonSelectedClassChanges
public import Oberwolfach.RetainedCommonWeightWitness

@[expose] public section

/-! Transfer of the complete common witness with one fixed selector.
Physical edges and coefficient functions do not change. Class sizes,
overlap, potential loads and actual cycle/path counts have explicit losses. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color : Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

def CommonWitnessEstimates (P : SimpleGraph V) (π : Equiv.Perm V) (d r : ℕ)
    (D p k s₀ ηsize ηoverlap ηload βcycle βpath : ℝ) (weight : (Fin (r+4+1)→V)→ℝ)
    (σ : RawMarkedOutcome V U Γ Color) (H : Bool→V→U→Prop) (κ : V→Bool) (u u' : U) : Prop :=
  let T := commonSelectedClass H κ u u'
  (∀ b,|((T b).card:ℝ)-(if b then (s₀/((r+4:ℕ):ℝ))*(s₀/((r+4:ℕ):ℝ)) else s₀*s₀/((r+4:ℕ):ℝ))*Fintype.card V|≤ηsize*Fintype.card V) ∧
  (((T false∩(T true).image π).card:ℝ)≤ηoverlap*Fintype.card V) ∧
  CommonPotentialSpokeLoads P π d (r+4) D p k (s₀*s₀/((r+4:ℕ):ℝ)) weight ηload σ H κ u u' ∧
  (βcycle*(Fintype.card V:ℝ)^(r+5)≤
    (Fintype.card (MarkedSampleCommonCycleWithSpokes P π d (r+4) σ (selectedSpokes H κ) ![u,u']):ℝ)) ∧
  (∀ v v' : V,v≠v' → ∀ b : Bool,
    βpath*(Fintype.card V:ℝ)^(r+4)≤
      (Fintype.card (MarkedSampleCommonPathWithSpokes P π d (r+3) σ (selectedSpokes H κ) ![u,u'] b v v'):ℝ))

theorem rawCommonWitness_transfer
    (P : SimpleGraph V) (π : Equiv.Perm V) (d r : ℕ) (hr : 1≤r) (hn : 0<Fintype.card V)
    (α astar pstar D p k s₀ τ A B εsize εload ζ : ℝ) (hB : 0≤B) (hζ : 0≤ζ)
    (hpstar : 0<pstar) (hpmin : pstar≤p) (hkmin : pstar≤k)
    (hsmin : pstar≤s₀*s₀/((r+4:ℕ):ℝ)) (hp1 : p≤1) (hk1 : k≤1) (hs1 : s₀*s₀/((r+4:ℕ):ℝ)≤1)
    (weight : (Fin (r+4+1)→V)→ℝ) (hw : SuccessorSequenceWeightConditions P π (3*d) D τ A B weight)
    (hDlo : (Fintype.card V:ℝ)/2≤D) (hDhi : D≤2*Fintype.card V)
    (g : Γ) (j : Color) (σ : RawMarkedOutcome V U Γ Color)
    (H' : Bool→V→U→Prop) (κ : V→Bool) (u u' : U)
    (hraw : RawCommonWitness P π d r α astar pstar D p k s₀ εsize (τ+εload) weight g j u u' σ κ)
    (hc : ∀ b z,(∑ x,if ¬(rawMarkedPairSpokes π d σ g j b x z↔H' b x z) then (1:ℝ) else 0)≤ζ*Fintype.card V) :
    CommonWitnessEstimates P π d r D p k s₀ (εsize+2*ζ) (4*ζ)
      (τ+εload+10*((r+4:ℕ)+1:ℝ)^4*(2*B/pstar^(2*(r+4)+1))*ζ)
      (pstar^(r+5)*(α*(astar/2)/4)^(r+5)/2-2*(r+5:ℕ)*ζ)
      (pstar^(r+7)*(α*(astar/2)/4)^(r+4)/2-2*(r+4:ℕ)*ζ) weight σ H' κ u u' := by
  let H := rawMarkedPairSpokes π d σ g j
  let T := commonSelectedClass H κ u u'
  let T' := commonSelectedClass H' κ u u'
  have hnR : (0:ℝ)<Fintype.card V := Nat.cast_pos.mpr hn
  have hδ : 0≤ζ*Fintype.card V := mul_nonneg hζ (Nat.cast_nonneg _)
  have hsel := selectedSpokes_change_columns H H' κ (ζ*Fintype.card V) hc
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro b
    have hh := commonSelectedClass_card_change H H' κ u u' (ζ*Fintype.card V) hc b
    have hb := hraw.2.2.1 b
    change |((T b).card:ℝ)-(if b then (s₀/((r+4:ℕ):ℝ))*(s₀/((r+4:ℕ):ℝ)) else s₀*s₀/((r+4:ℕ):ℝ))*Fintype.card V|≤εsize*Fintype.card V at hb
    exact (abs_sub_le _ _ _).trans ((add_le_add hh hb).trans_eq (by ring))
  · have hh := commonSelectedClass_overlap_change π H H' κ u u' (ζ*Fintype.card V) hc hraw.1.2.1
    exact hh.trans_eq (by ring)
  · have hh := commonPotentialSpokeLoads_change P π d (r+4) (by omega) hn D τ A B p k
      (s₀*s₀/((r+4:ℕ):ℝ)) pstar hB hDlo hDhi hpstar hpmin hkmin hsmin hp1 hk1 hs1 weight hw
      (τ+εload) (ζ*Fintype.card V) hδ σ H H' κ u u' hraw.2.2.2 hc
    have he : τ+εload+10*(((r+4:ℕ):ℝ)+1)^4*(2*B/pstar^(2*(r+4)+1))*(ζ*Fintype.card V)/Fintype.card V=
        τ+εload+10*(((r+4:ℕ):ℝ)+1)^4*(2*B/pstar^(2*(r+4)+1))*ζ := by field_simp
    rw [he] at hh
    exact hh
  · have hbase := hraw.2.1.1
    have hmap := selectedBase_card_le_common_cycle P π d (r+4) σ H κ ![u,u']
    have hlo : (pstar^(r+5)*(α*(astar/2)/4)^(r+5)/2)*(Fintype.card V:ℝ)^(r+5)≤
        (Fintype.card (MarkedSampleCommonCycleWithSpokes P π d (r+4) σ (selectedSpokes H κ) ![u,u']):ℝ) :=
      hbase.trans (by exact_mod_cast hmap)
    have hl := commonMarkedCycle_spoke_changes
      (fun e : MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false=>e.val.1) (fun e=>e.val.2)
      (fun e : MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true=>e.val.1) (fun e=>e.val.2)
      (r+4) π (3*d) (selectedSpokes H κ) (selectedSpokes H' κ) u u' (ζ*Fintype.card V) hsel
    have he : 2*(((r+4:ℕ):ℝ)+1)*(ζ*Fintype.card V)*(Fintype.card V:ℝ)^(r+4)=
        2*(r+5:ℕ)*ζ*(Fintype.card V:ℝ)^(r+5) := by
      simp only [Nat.cast_add,Nat.cast_ofNat,show r+5=(r+4)+1 by omega,pow_succ]
      ring
    rw [he] at hl
    change (Fintype.card (MarkedSampleCommonCycleWithSpokes P π d (r+4) σ (selectedSpokes H κ) ![u,u']):ℝ)-
      Fintype.card (MarkedSampleCommonCycleWithSpokes P π d (r+4) σ (selectedSpokes H' κ) ![u,u'])≤_ at hl
    nlinarith only [hlo,hl]
  · intro v v' hv b
    have hbase := hraw.2.1.2 v v' hv b
    have hmap := selectedPath_card_le_common_path P π d (r+3) σ H κ ![u,u'] (by omega) b v v'
    have hlo : (pstar^(r+7)*(α*(astar/2)/4)^(r+4)/2)*(Fintype.card V:ℝ)^(r+4)≤
        (Fintype.card (MarkedSampleCommonPathWithSpokes P π d (r+3) σ (selectedSpokes H κ) ![u,u'] b v v'):ℝ) :=
      hbase.trans (by exact_mod_cast hmap)
    have hl := rootFirstCommonMarkedPath_spoke_changes
      (fun e : MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false=>e.val.1) (fun e=>e.val.2)
      (fun e : MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true=>e.val.1) (fun e=>e.val.2)
      ((r+3)+1) π (3*d) (selectedSpokes H κ) (selectedSpokes H' κ) b v v' u u' (ζ*Fintype.card V) hsel
    have he : 2*((r+3+1:ℕ):ℝ)*(ζ*Fintype.card V)*(Fintype.card V:ℝ)^(r+3+1-1)=
        2*(r+4:ℕ)*ζ*(Fintype.card V:ℝ)^(r+4) := by
      simp only [Nat.add_sub_cancel,show r+4=(r+3)+1 by omega,pow_succ]
      ring
    rw [he] at hl
    change (Fintype.card (MarkedSampleCommonPathWithSpokes P π d (r+3) σ (selectedSpokes H κ) ![u,u'] b v v'):ℝ)-
      Fintype.card (MarkedSampleCommonPathWithSpokes P π d (r+3) σ (selectedSpokes H' κ) ![u,u'] b v v')≤_ at hl
    nlinarith only [hlo,hl]

end Oberwolfach

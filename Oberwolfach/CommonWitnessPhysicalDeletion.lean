module

public import Oberwolfach.CommonPotentialPhysicalDeletion
public import Oberwolfach.CommonWitnessTransfer
public import Oberwolfach.MarkedSampleCommonPhysicalDeletion
public import Oberwolfach.MarkedPathRestrictionCounts

@[expose] public section

/-! A fixed common-hub witness survives bounded physical deletions. The
selector and parent coefficients are not resampled, the original domain
and normalization are retained, and the loss is charged directly to the
realized deleted degrees. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 16000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem common_witness_after_physical_deletion
    (P:SimpleGraph V) (π:Equiv.Perm V) (d r:ℕ) (hr:1≤r) (hn:0<Fintype.card V)
    (D τ A B p k s₀ pstar:ℝ) (hB:0≤B)
    (hDlo:(Fintype.card V:ℝ)/2≤D) (hDhi:D≤2*Fintype.card V)
    (hpstar:0<pstar) (hp:pstar≤p) (hk:pstar≤k) (hs:pstar≤s₀*s₀/((r+4:ℕ):ℝ))
    (hp1:p≤1) (hk1:k≤1) (hs1:s₀*s₀/((r+4:ℕ):ℝ)≤1)
    (weight:(Fin (r+4+1)→V)→ℝ) (hw:SuccessorSequenceWeightConditions P π (3*d) D τ A B weight)
    (es eo el bc bp delta:ℝ) (hdelta:0≤delta)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop) (κ:V→Bool) (u u':U)
    (h:CommonWitnessEstimates P π d r D p k s₀ es eo el bc bp weight σ H κ u u')
    (DR:SimpleGraph V) (DS:SimpleGraph (V⊕U))
    (hrim:∀ x,(DR.degree x:ℝ)≤delta) (hcol:∀ z,(DS.degree (Sum.inr z):ℝ)≤delta) :
    CommonWitnessEstimates P π d r D p k s₀
      (es+2*delta/Fintype.card V) eo
      (el+20*((r+4:ℕ)+1:ℝ)^4*(2*B/pstar^(2*(r+4)+1))*delta/Fintype.card V)
      (bc-3*(r+5:ℕ)*delta/Fintype.card V)
      (bp-4*(r+5:ℕ)*delta/Fintype.card V)
      weight (rawMarkedDeleteRims σ DR.edgeFinset) (markedDeletePhysicalSpokes H DS) κ u u' := by
  let H':=markedDeletePhysicalSpokes H DS
  let n:ℝ:=Fintype.card V
  have hnR:0<n:=by dsimp [n];exact_mod_cast hn
  have hn0:n≠0:=ne_of_gt hnR
  have hc:∀ b z,(∑ x,if ¬(H b x z↔H' b x z) then (1:ℝ) else 0)≤delta:=by
    intro b z
    simpa using (marked_spoke_physical_deletion_column_change H DS Finset.univ b z).trans (hcol z)
  have hsub (b:Bool):commonSelectedClass H' κ u u' b⊆commonSelectedClass H κ u u' b:=by
    intro v hv
    simp only [commonSelectedClass,Finset.mem_filter,Finset.mem_univ,true_and,commonThinnedSpokes] at hv ⊢
    exact ⟨hv.1.1,hv.2.1.1,hv.2.2⟩
  have hoverlap:((commonSelectedClass H' κ u u' false∩(commonSelectedClass H' κ u u' true).image π).card:ℝ)≤
      ((commonSelectedClass H κ u u' false∩(commonSelectedClass H κ u u' true).image π).card:ℝ):=by
    exact_mod_cast Finset.card_le_card (Finset.inter_subset_inter (hsub false) (Finset.image_subset_image (hsub true)))
  have hsel: selectedSpokes H' κ = markedDeletePhysicalSpokes (selectedSpokes H κ) DS:=by
    funext b v z
    apply propext
    simp only [H',selectedSpokes,markedDeletePhysicalSpokes]
    tauto
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro b
    have hh:=commonSelectedClass_card_change H H' κ u u' delta hc b
    have hb:=h.1 b
    have hcalc: (es+2*delta/n)*n=es*n+2*delta:=by field_simp <;> ring
    rw [hcalc]
    exact (abs_sub_le ((commonSelectedClass H' κ u u' b).card:ℝ)
      ((commonSelectedClass H κ u u' b).card:ℝ)
      ((if b then (s₀/((r+4:ℕ):ℝ))*(s₀/((r+4:ℕ):ℝ)) else s₀*s₀/((r+4:ℕ):ℝ))*Fintype.card V)).trans
      ((add_le_add hh hb).trans_eq (by ring))
  · exact hoverlap.trans h.2.1
  · have hh:=common_potential_loads_after_physical_deletion P π d (r+4) (by omega) hn
      D τ A B p k (s₀*s₀/((r+4:ℕ):ℝ)) pstar hB hDlo hDhi hpstar hp hk hs hp1 hk1 hs1
      weight hw el delta delta hdelta hdelta σ H κ u u' h.2.2.1 DR DS hrim hcol
    convert hh using 1 <;> simp only [Nat.cast_add,Nat.cast_ofNat,H'] <;> ring
  · have hb:=h.2.2.2.1
    have hl:=marked_sample_common_cycle_physical_deletion P π d (r+4) (by omega)
      σ (selectedSpokes H κ) DR DS delta hrim hcol u u'
    change (Fintype.card (MarkedSampleCommonCycleWithSpokes P π d (r+4) σ (selectedSpokes H κ) ![u,u']):ℝ)-
      Fintype.card (MarkedSampleCommonCycleWithSpokes P π d (r+4)
        (rawMarkedDeleteRims σ DR.edgeFinset) (markedDeletePhysicalSpokes (selectedSpokes H κ) DS) ![u,u'])≤_ at hl
    rw [←hsel] at hl
    have he:(bc-3*(r+5:ℕ)*delta/n)*n^(r+5)=bc*n^(r+5)-3*(r+5:ℕ)*delta*n^(r+4):=by
      rw [show r+5=(r+4)+1 by omega,pow_succ];field_simp <;> ring
    change _ ≤ (Fintype.card (MarkedSampleCommonCycleWithSpokes P π d (r+4)
      (rawMarkedDeleteRims σ DR.edgeFinset) (selectedSpokes H' κ) ![u,u']):ℝ)
    rw [he]
    simp only [Nat.cast_add,Nat.cast_ofNat] at hl hb ⊢
    nlinarith only [hl,hb]
  · intro v v' hv b
    have hb:=h.2.2.2.2 v v' hv b
    have hl:=marked_sample_common_path_physical_deletion P π d (r+3+1) (by omega)
      σ (selectedSpokes H κ) DR DS delta hrim hcol
      ((markedRootOrder (r+3+1) b).symm 0) v v' u u'
    have heOld:Fintype.card (MarkedSampleCommonPathWithSpokes P π d (r+3) σ (selectedSpokes H κ) ![u,u'] b v v')=
      Fintype.card (CanonicalCommonMarkedPath _ _ _ _ (r+3+1) π (3*d)
        (selectedSpokes H κ false) (selectedSpokes H κ true) ((markedRootOrder (r+3+1) b).symm 0) v v' u u'):=
      Fintype.card_congr (rootFirstCommonMarkedPathCanonicalEquiv b v v' u u')
    have heNew:Fintype.card (MarkedSampleCommonPathWithSpokes P π d (r+3)
      (rawMarkedDeleteRims σ DR.edgeFinset) (markedDeletePhysicalSpokes (selectedSpokes H κ) DS) ![u,u'] b v v')=
      Fintype.card (CanonicalCommonMarkedPath _ _ _ _ (r+3+1) π (3*d)
        (markedDeletePhysicalSpokes (selectedSpokes H κ) DS false)
        (markedDeletePhysicalSpokes (selectedSpokes H κ) DS true)
        ((markedRootOrder (r+3+1) b).symm 0) v v' u u'):=
      Fintype.card_congr (rootFirstCommonMarkedPathCanonicalEquiv b v v' u u')
    dsimp only at hl
    rw [←heOld,←heNew,←hsel] at hl
    have he:(bp-4*(r+5:ℕ)*delta/n)*n^(r+4)=bp*n^(r+4)-4*(r+5:ℕ)*delta*n^(r+3):=by
      rw [show r+4=(r+3)+1 by omega,pow_succ];field_simp <;> ring
    change _ ≤ (Fintype.card (MarkedSampleCommonPathWithSpokes P π d (r+3)
      (rawMarkedDeleteRims σ DR.edgeFinset) (selectedSpokes H' κ) ![u,u'] b v v'):ℝ)
    rw [he]
    simp only [Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat] at hl hb ⊢
    nlinarith only [hl,hb]

end Oberwolfach

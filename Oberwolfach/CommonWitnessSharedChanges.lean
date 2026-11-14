module

public import Oberwolfach.CommonWitnessPhysicalDeletion
public import Oberwolfach.CommonPotentialSharedChanges
public import Oberwolfach.CommonSelectedClassOverlapSharedChanges
public import Oberwolfach.MarkedSharedChangeSubhost
public import Oberwolfach.MarkedCommonConfigurationMonotonicity

@[expose] public section
/-! Transfer a fixed common-hub witness across shared physical changes.
The selector and weight are fixed before the later corrected host. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem common_witness_after_shared_changes
    (P:SimpleGraph V) (π:Equiv.Perm V) (d r:ℕ) (hr:1≤r) (hn:0<Fintype.card V)
    (D τweight A B p k s₀ pstar:ℝ) (hB:0≤B)
    (hDlo:(Fintype.card V:ℝ)/2≤D) (hDhi:D≤2*Fintype.card V)
    (hpstar:0<pstar) (hp:pstar≤p) (hk:pstar≤k) (hs:pstar≤s₀*s₀/((r+4:ℕ):ℝ))
    (hp1:p≤1) (hk1:k≤1) (hs1:s₀*s₀/((r+4:ℕ):ℝ)≤1)
    (weight:(Fin (r+4+1)→V)→ℝ) (hw:SuccessorSequenceWeightConditions P π (3*d) D τweight A B weight)
    (es eo el bc bp delta:ℝ) (hdelta:0≤delta)
    (σ σnew:RawMarkedOutcome V U Γ Color) (H Hnew:Bool→V→U→Prop) (κ:V→Bool) (u u':U)
    (h:CommonWitnessEstimates P π d r D p k s₀ es eo el bc bp weight σ H κ u u')
    (FR:SimpleGraph V) (FS:SimpleGraph (V⊕U))
    (hchangeR:∀a,¬(rawMarkedPairRims P π d σ a↔rawMarkedPairRims P π d σnew a)→markedPairPhysical π a∈FR.edgeFinset)
    (hchangeS:∀b v z,¬(H b v z↔Hnew b v z)→FS.Adj (Sum.inl v) (Sum.inr z))
    (hrim:∀x,(FR.degree x:ℝ)≤delta) (hcol:∀z,(FS.degree (Sum.inr z):ℝ)≤delta):
    CommonWitnessEstimates P π d r D p k s₀
      (es+2*delta/Fintype.card V) (eo+4*delta/Fintype.card V)
      (el+20*((r+4:ℕ)+1:ℝ)^4*(2*B/pstar^(2*(r+4)+1))*delta/Fintype.card V)
      (bc-3*(r+5:ℕ)*delta/Fintype.card V)
      (bp-4*(r+5:ℕ)*delta/Fintype.card V) weight σnew Hnew κ u u':=by
  let n:ℝ:=Fintype.card V
  have hn0:n≠0:=by dsimp [n];exact_mod_cast Nat.ne_of_gt hn
  obtain ⟨_,hscol⟩:=marked_spoke_physical_change_incidence H Hnew FS hchangeS
  have hc:∀b z,(∑ x,if ¬(H b x z↔Hnew b x z) then (1:ℝ) else 0)≤delta:=by
    intro b z
    have hh:=(hscol b z).trans (hcol z)
    apply le_trans ?_ hh
    apply le_of_eq
    apply Finset.sum_congr rfl
    intro x _
    simp only [bipAdj]
    split_ifs <;> rfl
  have hdel:=common_witness_after_physical_deletion P π d r hr hn D τweight A B p k s₀ pstar hB
    hDlo hDhi hpstar hp hk hs hp1 hk1 hs1 weight hw es eo el bc bp delta hdelta σ H κ u u' h FR FS hrim hcol
  have hload:=common_potential_loads_after_shared_changes P π d (r+4) (by omega) hn D τweight A B p k
    (s₀*s₀/((r+4:ℕ):ℝ)) pstar hB hDlo hDhi hpstar hp hk hs hp1 hk1 hs1
    weight hw el delta delta hdelta hdelta σ σnew H Hnew κ u u' h.2.2.1 FR FS hchangeR hchangeS hrim hcol
  obtain ⟨hR,hS⟩:=marked_shared_change_subhost P π d σ σnew H Hnew FR FS hchangeR hchangeS
  let σ₀:=rawMarkedDeleteRims σ FR.edgeFinset
  let H₀:=markedDeletePhysicalSpokes H FS
  let E₀:=MarkedSampleArc P π (3*d) (fun e=>σ₀ (Sum.inl e)) false
  let K₀:=MarkedSampleArc P π (3*d) (fun e=>σ₀ (Sum.inl e)) true
  let E':=MarkedSampleArc P π (3*d) (fun e=>σnew (Sum.inl e)) false
  let K':=MarkedSampleArc P π (3*d) (fun e=>σnew (Sum.inl e)) true
  have hE:∀ e:E₀,∃ e':E',e'.val.1=e.val.1∧e'.val.2=e.val.2:=by
    intro e;exact ⟨⟨e.val,hR false e.val.1 e.val.2 e.property⟩,rfl,rfl⟩
  have hK:∀ e:K₀,∃ e':K',e'.val.1=e.val.1∧e'.val.2=e.val.2:=by
    intro e;exact ⟨⟨e.val,hR true e.val.1 e.val.2 e.property⟩,rfl,rfl⟩
  have hselected:∀b v z,selectedSpokes H₀ κ b v z→selectedSpokes Hnew κ b v z:=by
    intro b v z hs
    exact ⟨hS b v z hs.1,hs.2⟩
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro b
    have hh:=commonSelectedClass_card_change H Hnew κ u u' delta hc b
    have he:(es+2*delta/n)*n=es*n+2*delta:=by field_simp <;> ring
    rw [he]
    exact (abs_sub_le ((commonSelectedClass Hnew κ u u' b).card:ℝ)
      ((commonSelectedClass H κ u u' b).card:ℝ)
      ((if b then (s₀/((r+4:ℕ):ℝ))*(s₀/((r+4:ℕ):ℝ)) else s₀*s₀/((r+4:ℕ):ℝ))*Fintype.card V)).trans
      ((add_le_add hh (h.1 b)).trans_eq (by ring))
  · have hh:=common_selected_class_overlap_shared_changes π H Hnew κ u u' delta hc
    have he:(eo+4*delta/n)*n=eo*n+4*delta:=by field_simp <;> ring
    rw [he]
    linarith only [hh,h.2.1]
  · convert hload using 1 <;> simp only [Nat.cast_add,Nat.cast_ofNat] <;> ring
  · let F:=marked_common_cycle_host_inclusion
      (fun e:E₀=>e.val.1) (fun e=>e.val.2) (fun e:K₀=>e.val.1) (fun e=>e.val.2)
      (fun e:E'=>e.val.1) (fun e=>e.val.2) (fun e:K'=>e.val.1) (fun e=>e.val.2)
      π (3*d) (selectedSpokes H₀ κ) (selectedSpokes Hnew κ) hE hK hselected (r+4) u u'
    have hm:Fintype.card (MarkedSampleCommonCycleWithSpokes P π d (r+4) σ₀ (selectedSpokes H₀ κ) ![u,u'])≤
        Fintype.card (MarkedSampleCommonCycleWithSpokes P π d (r+4) σnew (selectedSpokes Hnew κ) ![u,u']):=
      Fintype.card_le_of_injective F F.injective
    exact hdel.2.2.2.1.trans (by exact_mod_cast hm)
  · intro v v' hv b
    let F:=marked_common_path_host_inclusion
      (fun e:E₀=>e.val.1) (fun e=>e.val.2) (fun e:K₀=>e.val.1) (fun e=>e.val.2)
      (fun e:E'=>e.val.1) (fun e=>e.val.2) (fun e:K'=>e.val.1) (fun e=>e.val.2)
      π (3*d) (selectedSpokes H₀ κ) (selectedSpokes Hnew κ) hE hK hselected (r+3+1) b v v' u u'
    have hm:Fintype.card (MarkedSampleCommonPathWithSpokes P π d (r+3) σ₀ (selectedSpokes H₀ κ) ![u,u'] b v v')≤
        Fintype.card (MarkedSampleCommonPathWithSpokes P π d (r+3) σnew (selectedSpokes Hnew κ) ![u,u'] b v v'):=
      Fintype.card_le_of_injective F F.injective
    exact (hdel.2.2.2.2 v v' hv b).trans (by exact_mod_cast hm)
end Oberwolfach

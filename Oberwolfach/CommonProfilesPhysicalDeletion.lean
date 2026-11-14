module

public import Oberwolfach.CommonWitnessPhysicalDeletion
public import Oberwolfach.CommonWitnessMargins
public import Oberwolfach.MarkedCommonFixedWitnessProfiles

@[expose] public section

/-! Construct common-pair absorber profiles after an arbitrary bounded
physical deletion from one fixed family of original witnesses. The selector
for each pair and every cycle coefficient are inherited from the original
outcome; the only losses are the displayed deterministic degree costs. -/
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

theorem common_pair_profiles_after_physical_deletion
    (P:SimpleGraph V) (π:Equiv.Perm V) (d r:ℕ) (hr:1≤r) (hn:0<Fintype.card V)
    (D τ A B p k s₀ pstar blo bhi:ℝ) (hB:0≤B)
    (hDlo:(Fintype.card V:ℝ)/2≤D) (hDhi:D≤2*Fintype.card V)
    (hpstar:0<pstar) (hp:pstar≤p) (hk:pstar≤k) (hs:pstar≤s₀*s₀/((r+4:ℕ):ℝ))
    (hp1:p≤1) (hk1:k≤1) (hs1:s₀*s₀/((r+4:ℕ):ℝ)≤1)
    (weight:(Fin (r+4+1)→V)→ℝ) (hw:SuccessorSequenceWeightConditions P π (3*d) D τ A B weight)
    (hweight:∀ C:Fin (r+4+1)→V,SuccessorSequenceValid P π C→PermutationSeparated π (3*d) C→
      blo/(Fintype.card V:ℝ)^(r+4)≤weight C/(D*p^(r+4)*k*(s₀*s₀/((r+4:ℕ):ℝ))^(r+4)) ∧
      weight C/(D*p^(r+4)*k*(s₀*s₀/((r+4:ℕ):ℝ))^(r+4))≤bhi/(Fintype.card V:ℝ)^(r+4))
    (es eo el bc bp delta:ℝ) (hdelta:0≤delta)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop) (κ:U→U→V→Bool)
    (h:∀ u u':U,u≠u'→CommonWitnessEstimates P π d r D p k s₀ es eo el bc bp weight σ H (κ u u') u u')
    (DR:SimpleGraph V) (DS:SimpleGraph (V⊕U))
    (hrim:∀ x,(DR.degree x:ℝ)≤delta) (hcol:∀ z,(DS.degree (Sum.inr z):ℝ)≤delta) :
    let n:ℝ:=Fintype.card V
    let es':=es+2*delta/n
    let el':=el+20*((r+4:ℕ)+1:ℝ)^4*(2*B/pstar^(2*(r+4)+1))*delta/n
    let bc':=bc-3*(r+5:ℕ)*delta/n
    let bp':=bp-4*(r+5:ℕ)*delta/n
    let eps':=max es' (max eo el')
    let σ':=rawMarkedDeleteRims σ DR.edgeFinset
    let H':=markedDeletePhysicalSpokes H DS;
    Nonempty (MarkedCommonPairCycleProfiles
      (fun e:MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) false=>e.val.1) (fun e=>e.val.2)
      (fun e:MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) true=>e.val.1) (fun e=>e.val.2)
      (H' false) (H' true) π (3*d) r ((s₀/((r+4:ℕ):ℝ))^2) (min bc' bp') blo bhi eps') := by
  intro n es' el' bc' bp' eps' σ' H'
  apply marked_common_fixed_witness_profiles P π d r D p k s₀ eps' bc' bp' blo bhi weight σ' H' hweight κ
  intro u u' hne
  have hh:=common_witness_after_physical_deletion P π d r hr hn D τ A B p k s₀ pstar hB
    hDlo hDhi hpstar hp hk hs hp1 hk1 hs1 weight hw es eo el bc bp delta hdelta σ H (κ u u') u u' (h u u' hne) DR DS hrim hcol
  apply commonWitnessEstimates_mono P π d r D p k s₀ weight σ' H' (κ u u') u u'
    (le_max_left _ _) ((le_max_left _ _).trans (le_max_right _ _))
    ((le_max_right _ _).trans (le_max_right _ _)) le_rfl le_rfl
  exact hh

end Oberwolfach

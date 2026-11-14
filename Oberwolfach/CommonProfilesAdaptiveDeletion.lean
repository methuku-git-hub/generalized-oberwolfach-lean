module

public import Oberwolfach.CommonProfilesPhysicalDeletion
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

theorem common_pair_profiles_for_all_physical_deletions
    (P:SimpleGraph V) (π:Equiv.Perm V) (d r:ℕ) (hr:1≤r) (hn:0<Fintype.card V)
    (D τ A B p k s₀ pstar blo bhi:ℝ) (hB:0≤B)
    (hDlo:(Fintype.card V:ℝ)/2≤D) (hDhi:D≤2*Fintype.card V)
    (hpstar:0<pstar) (hp:pstar≤p) (hk:pstar≤k) (hs:pstar≤s₀*s₀/((r+4:ℕ):ℝ))
    (hp1:p≤1) (hk1:k≤1) (hs1:s₀*s₀/((r+4:ℕ):ℝ)≤1)
    (weight:(Fin (r+4+1)→V)→ℝ) (hw:SuccessorSequenceWeightConditions P π (3*d) D τ A B weight)
    (hweight:∀ C:Fin (r+4+1)→V,SuccessorSequenceValid P π C→PermutationSeparated π (3*d) C→
      blo/(Fintype.card V:ℝ)^(r+4)≤weight C/(D*p^(r+4)*k*(s₀*s₀/((r+4:ℕ):ℝ))^(r+4)) ∧
      weight C/(D*p^(r+4)*k*(s₀*s₀/((r+4:ℕ):ℝ))^(r+4))≤bhi/(Fintype.card V:ℝ)^(r+4))
    (es eo el bc bp:ℝ)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (h:∀ u u':U,u≠u'→∃ κ,CommonWitnessEstimates P π d r D p k s₀ es eo el bc bp weight σ H κ u u') :
    ∃ κ:U→U→V→Bool,
      (∀ u u':U,u≠u'→CommonWitnessEstimates P π d r D p k s₀ es eo el bc bp weight σ H (κ u u') u u') ∧
    ∀ (delta:ℝ),0≤delta→∀ (DR:SimpleGraph V) (DS:SimpleGraph (V⊕U)),
      (∀ x,(DR.degree x:ℝ)≤delta)→(∀ z,(DS.degree (Sum.inr z):ℝ)≤delta)→
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
  let κ:U→U→V→Bool:=fun u u'=>if hne:u≠u' then Classical.choose (h u u' hne) else fun _=>true
  have hκ:∀ u u':U,u≠u'→CommonWitnessEstimates P π d r D p k s₀ es eo el bc bp weight σ H (κ u u') u u':=by
    intro u u' hne
    dsimp only [κ]
    rw [dif_pos hne]
    exact Classical.choose_spec (h u u' hne)
  refine ⟨κ,hκ,?_⟩
  intro delta hdelta DR DS hrim hcol
  exact common_pair_profiles_after_physical_deletion P π d r hr hn D τ A B p k s₀ pstar blo bhi hB
    hDlo hDhi hpstar hp hk hs hp1 hk1 hs1 weight hw hweight es eo el bc bp delta hdelta σ H κ hκ DR DS hrim hcol

end Oberwolfach

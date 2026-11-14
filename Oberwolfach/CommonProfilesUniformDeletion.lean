module

public import Oberwolfach.CommonProfilesAdaptiveDeletion
public import Oberwolfach.CommonPhysicalProfileMargins
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

theorem common_pair_profiles_with_preselected_deletion_margin
    (P:SimpleGraph V) (π:Equiv.Perm V) (d r:ℕ) (hr:1≤r) (hn:0<Fintype.card V)
    (D τ A B p k s₀ pstar blo bhi:ℝ) (hB:0≤B)
    (hDlo:(Fintype.card V:ℝ)/2≤D) (hDhi:D≤2*Fintype.card V)
    (hpstar:0<pstar) (hp:pstar≤p) (hk:pstar≤k) (hs:pstar≤s₀*s₀/((r+4:ℕ):ℝ))
    (hp1:p≤1) (hk1:k≤1) (hs1:s₀*s₀/((r+4:ℕ):ℝ)≤1)
    (weight:(Fin (r+4+1)→V)→ℝ) (hw:SuccessorSequenceWeightConditions P π (3*d) D τ A B weight)
    (hweight:∀ C:Fin (r+4+1)→V,SuccessorSequenceValid P π C→PermutationSeparated π (3*d) C→
      blo/(Fintype.card V:ℝ)^(r+4)≤weight C/(D*p^(r+4)*k*(s₀*s₀/((r+4:ℕ):ℝ))^(r+4)) ∧
      weight C/(D*p^(r+4)*k*(s₀*s₀/((r+4:ℕ):ℝ))^(r+4))≤bhi/(Fintype.card V:ℝ)^(r+4))
    (es eo el bc bp η ζ:ℝ) (hζ:0<ζ)
    (hes:es≤η/2) (heo:eo≤η/2) (hel:el≤η/2)
    (hsize:η/2+2*ζ≤η)
    (hload:η/2+20*((r+4:ℕ)+1:ℝ)^4*(2*B/pstar^(2*(r+4)+1))*ζ≤η)
    (hcycle:bc/2≤bc-3*(r+5:ℕ)*ζ) (hpath:bp/2≤bp-4*(r+5:ℕ)*ζ)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (h:∀ u u':U,u≠u'→∃ κ,CommonWitnessEstimates P π d r D p k s₀ es eo el bc bp weight σ H κ u u') :
    ∃ κ:U→U→V→Bool,
      (∀ u u':U,u≠u'→CommonWitnessEstimates P π d r D p k s₀ es eo el bc bp weight σ H (κ u u') u u') ∧
    ∀ (DR:SimpleGraph V) (DS:SimpleGraph (V⊕U)),
      (∀ x,(DR.degree x:ℝ)≤ζ*Fintype.card V)→(∀ z,(DS.degree (Sum.inr z):ℝ)≤ζ*Fintype.card V)→
    let σ':=rawMarkedDeleteRims σ DR.edgeFinset
    let H':=markedDeletePhysicalSpokes H DS;
    Nonempty (MarkedCommonPairCycleProfiles
      (fun e:MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) false=>e.val.1) (fun e=>e.val.2)
      (fun e:MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) true=>e.val.1) (fun e=>e.val.2)
      (H' false) (H' true) π (3*d) r ((s₀/((r+4:ℕ):ℝ))^2) (min bc bp/2) blo bhi η)
 := by
  let K:ℝ:=((r+4:ℕ)+1:ℝ)^4*(2*B/pstar^(2*(r+4)+1))
  have hloadK:η/2+20*K*ζ≤η:=by
    convert hload using 1 <;> simp only [K,Nat.cast_add,Nat.cast_ofNat] <;> ring
  obtain ⟨κ,hκ,hprofiles⟩:=common_pair_profiles_for_all_physical_deletions P π d r hr hn
    D τ A B p k s₀ pstar blo bhi hB hDlo hDhi hpstar hp hk hs hp1 hk1 hs1 weight hw hweight es eo el bc bp σ H h
  refine ⟨κ,hκ,?_⟩
  intro DR DS hrim hcol σ' H'
  have hnR:0<(Fintype.card V:ℝ):=by exact_mod_cast hn
  have hn0:(Fintype.card V:ℝ)≠0:=ne_of_gt hnR
  have hδ:0≤ζ*Fintype.card V:=by positivity
  obtain ⟨profile⟩:=hprofiles (ζ*Fintype.card V) hδ DR DS hrim hcol
  have heps:max (es+2*(ζ*Fintype.card V)/(Fintype.card V:ℝ))
      (max eo (el+20*K*(ζ*Fintype.card V)/(Fintype.card V:ℝ)))≤η:=by
    rw [max_le_iff,max_le_iff]
    have he1:2*(ζ*Fintype.card V)/(Fintype.card V:ℝ)=2*ζ:=by field_simp
    have he2:20*K*(ζ*Fintype.card V)/(Fintype.card V:ℝ)=20*K*ζ:=by field_simp
    rw [he1,he2]
    constructor
    · linarith only [hes,hsize]
    constructor
    · linarith only [heo,hsize,hζ]
    · linarith only [hel,hloadK]
  have hbeta:min bc bp/2≤min (bc-3*(r+5:ℕ)*(ζ*Fintype.card V)/(Fintype.card V:ℝ))
      (bp-4*(r+5:ℕ)*(ζ*Fintype.card V)/(Fintype.card V:ℝ)):=by
    have he1:3*((r+5:ℕ):ℝ)*(ζ*Fintype.card V)/(Fintype.card V:ℝ)=3*(r+5:ℕ)*ζ:=by field_simp
    have he2:4*((r+5:ℕ):ℝ)*(ζ*Fintype.card V)/(Fintype.card V:ℝ)=4*(r+5:ℕ)*ζ:=by field_simp
    rw [he1,he2]
    have hm1:min bc bp/2≤bc/2:=by have hh:=min_le_left bc bp;linarith
    have hm2:min bc bp/2≤bp/2:=by have hh:=min_le_right bc bp;linarith
    exact le_min (hm1.trans hcycle) (hm2.trans hpath)
  refine ⟨(profile.lowerCount hbeta).mono_error ?_⟩
  convert heps using 1 <;> simp only [K,Nat.cast_add,Nat.cast_ofNat] <;> ring

end Oberwolfach

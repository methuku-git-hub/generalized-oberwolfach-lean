module

public import Oberwolfach.CommonProfilesUniformDeletion
public import Oberwolfach.MarkedHostCountsPhysicalDeletionReal
public import Oberwolfach.MarkedFiniteAbsorberProperty
public import Oberwolfach.MarkedSampleCycleValidity
public import Oberwolfach.MarkedSampleHostInterfaces

@[expose] public section

/-! Construct finite absorbers in every later bounded physical deletion of
one fixed sampled host. The coefficients, domains and common-pair selectors
are inherited from the original host. The deletion tolerance is chosen
before the host, its sample and every later deletion. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 30000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_finite_absorbers_after_physical_deletion
    (l:ℕ) (hl:2≤l) (ρ σ q₀ bc bp blo bhi B pstar:ℝ)
    (hρ:0<ρ) (hσ:0<σ) (hq:0<q₀) (hbc:0<bc) (hbp:0<bp)
    (hblo:0<blo) (hbhi:0<bhi) (hB:0<B) (hpstar:0<pstar) :
    ∃ ε ζ:ℝ,0<ε ∧ 0<ζ ∧ ∀ size:ℕ,∃ a₀ b₀:ℕ,∀ f d:ℕ,2≤d→∃ N:ℕ,1≤N ∧
    ∀ (V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [DecidableEq U],N≤Fintype.card V→
    ∀ (P:SimpleGraph V) (π:Equiv.Perm V) (D τ A p k s₀:ℝ),
      (Fintype.card V:ℝ)/2≤D → D≤2*Fintype.card V →
      pstar≤p → pstar≤k → pstar≤s₀*s₀/((l+4:ℕ):ℝ) →
      p≤1 → k≤1 → s₀*s₀/((l+4:ℕ):ℝ)≤1 → q₀≤(s₀/((l+4:ℕ):ℝ))^2 →
    ∀ (weight:(Fin (l+4+1)→V)→ℝ),
      SuccessorSequenceWeightConditions P π (3*d) D τ A B weight →
      (∀ C:Fin (l+4+1)→V,SuccessorSequenceValid P π C→PermutationSeparated π (3*d) C→
        blo/(Fintype.card V:ℝ)^(l+4)≤weight C/(D*p^(l+4)*k*(s₀*s₀/((l+4:ℕ):ℝ))^(l+4)) ∧
        weight C/(D*p^(l+4)*k*(s₀*s₀/((l+4:ℕ):ℝ))^(l+4))≤bhi/(Fintype.card V:ℝ)^(l+4)) →
    ∀ (σBase:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop),
      (∀ v u,¬(H false v u∧H true v u)) →
      (∀ u u':U,u≠u'→∃ κ,CommonWitnessEstimates P π d l D p k s₀ (ε/2) (ε/2) (ε/2) bc bp weight σBase H κ u u') →
      MarkedHostExtensionCounts
        (fun e:MarkedSampleArc P π (3*d) (fun a=>σBase (Sum.inl a)) false=>e.val.1) (fun e=>e.val.2)
        (fun e:MarkedSampleArc P π (3*d) (fun a=>σBase (Sum.inl a)) true=>e.val.1) (fun e=>e.val.2)
        (H false) (H true) π (3*d) l (ρ*Fintype.card V) (σ*Fintype.card V) →
    ∃ κ:U→U→V→Bool,
      (∀ u u':U,u≠u'→CommonWitnessEstimates P π d l D p k s₀ (ε/2) (ε/2) (ε/2) bc bp weight σBase H (κ u u') u u') ∧
    ∀ (DR:SimpleGraph V) (DS:SimpleGraph (V⊕U)),
      (∀ x,(DR.degree x:ℝ)≤ζ*Fintype.card V) →
      (∀ z,(DS.degree z:ℝ)≤ζ*Fintype.card V) →
    let σ':=rawMarkedDeleteRims σBase DR.edgeFinset
    let H':=markedDeletePhysicalSpokes H DS;
    MarkedFiniteAbsorberProperty
      (fun e:MarkedSampleArc P π (3*d) (fun a=>σ' (Sum.inl a)) false=>e.val.1) (fun e=>e.val.2)
      (fun e:MarkedSampleArc P π (3*d) (fun a=>σ' (Sum.inl a)) true=>e.val.1) (fun e=>e.val.2)
      (H' false) (H' true) π (3*d) l ε size a₀ b₀ f := by
  let β:=min bc bp/2
  have hβ:0<β:=by dsimp [β];positivity
  obtain ⟨ε,hε,habs⟩:=marked_finite_remainder_absorber l hl (ρ/2) (σ/2) q₀ β blo bhi
    (by positivity) (by positivity) hq hβ hblo hbhi
  let K:ℝ:=((l+4:ℕ)+1:ℝ)^4*(2*B/pstar^(2*(l+4)+1))
  have hK:0≤K:=by dsimp [K];positivity
  obtain ⟨ζp,hζp,hsize,hload,hcycle,hpath⟩:=common_physical_profile_margins l K bc bp ε hK hbc hbp hε
  let ζ:=min ζp (min (ρ/8) (σ/(2*(l+11:ℕ))))
  have hζ:0<ζ:=by dsimp [ζ];positivity
  have hζp':ζ≤ζp:=min_le_left _ _
  have hζρ:ζ≤ρ/8:=(min_le_right _ _).trans (min_le_left _ _)
  have hζσ:ζ≤σ/(2*(l+11:ℕ)):=(min_le_right _ _).trans (min_le_right _ _)
  have hsize':ε/2+2*ζ≤ε:=by linarith only [hsize,hζp']
  have hload':ε/2+20*K*ζ≤ε:=by nlinarith only [hload,mul_nonneg hK (sub_nonneg.mpr hζp')]
  have hcycle':bc/2≤bc-3*(l+5:ℕ)*ζ:=by
    have hmul:=mul_nonneg (show (0:ℝ)≤3*((l+5:ℕ):ℝ) by positivity) (sub_nonneg.mpr hζp')
    nlinarith only [hcycle,hmul]
  have hpath':bp/2≤bp-4*(l+5:ℕ)*ζ:=by
    have hmul:=mul_nonneg (show (0:ℝ)≤4*((l+5:ℕ):ℝ) by positivity) (sub_nonneg.mpr hζp')
    nlinarith only [hpath,hmul]
  have hρζ:4*ζ≤ρ/2:=by linarith only [hζρ]
  have hσζ:((l+11:ℕ):ℝ)*ζ≤σ/2:=by
    have hh:0<2*((l+11:ℕ):ℝ):=by positivity
    have ht:ζ*(2*((l+11:ℕ):ℝ))≤σ:=(le_div_iff₀ hh).mp hζσ
    nlinarith only [ht]
  refine ⟨ε,ζ,hε,hζ,?_⟩
  intro size
  obtain ⟨a₀,b₀,habs⟩:=habs size
  refine ⟨a₀,b₀,?_⟩
  intro f d hd
  obtain ⟨N,habs⟩:=habs f (3*d)
  refine ⟨max N 1,by omega,?_⟩
  intro V U Γ Color _ _ _ _ _ _ hn P π D τ A p k s₀ hDlo hDhi hp hk hs hp1 hk1 hs1 hq0
    weight hw hweight σBase H htypes hwitness hcounts
  have hnpos:0<Fintype.card V:=by omega
  have hnR:0<(Fintype.card V:ℝ):=by exact_mod_cast hnpos
  have hload'':ε/2+20*((l+4:ℕ)+1:ℝ)^4*(2*B/pstar^(2*(l+4)+1))*ζ≤ε:=by
    convert hload' using 1 <;> simp only [K,Nat.cast_add,Nat.cast_ofNat] <;> ring
  obtain ⟨κ,hκ,hprofiles⟩:=common_pair_profiles_with_preselected_deletion_margin P π d l (by omega) hnpos
    D τ A B p k s₀ pstar blo bhi hB.le hDlo hDhi hpstar hp hk hs hp1 hk1 hs1 weight hw hweight
    (ε/2) (ε/2) (ε/2) bc bp ε ζ hζ le_rfl le_rfl le_rfl hsize' hload'' hcycle' hpath' σBase H hwitness
  refine ⟨κ,hκ,?_⟩
  intro DR DS hrim hspoke σ' H'
  obtain ⟨Profiles⟩:=hprofiles DR DS hrim (fun u=>hspoke (Sum.inr u))
  have hδ:0≤ζ*Fintype.card V:=by positivity
  have Counts:=marked_sample_host_extensions_after_physical_deletion_real P π d l σBase H
    (ρ*Fintype.card V) (σ*Fintype.card V) (ζ*Fintype.card V) hδ DR DS hrim hspoke hcounts
  have hρmargin:(ρ/2)*Fintype.card V≤ρ*Fintype.card V-4*(ζ*Fintype.card V):=by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hρζ) hnR.le]
  have hσmargin:(σ/2)*Fintype.card V≤σ*Fintype.card V-(l+11:ℕ)*(ζ*Fintype.card V):=by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hσζ) hnR.le]
  have hσmargin':(σ/2)*Fintype.card V≤σ*Fintype.card V-((l:ℝ)+11)*(ζ*Fintype.card V):=by
    simpa only [Nat.cast_add,Nat.cast_ofNat] using hσmargin
  have Counts':=Counts.lowerBounds hρmargin hσmargin'
  have Profiles':=Profiles.lowerDensity hq0
  change MarkedFiniteAbsorberProperty _ _ _ _ (H' false) (H' true) π (3*d) l ε size a₀ b₀ f
  intro AR SR hdiv hsizeR hsp W Z F₀ hF hFedges hZ hZsize hWsize
  apply habs V U _ _ (by omega) _ _ _ _ (H' false) (H' true) π (by omega) AR SR hdiv hsizeR hsp ?_
    W Z F₀ hF hFedges hZ Counts' (markedSampleArc_physical_injective P π (3*d) (fun a=>σ' (Sum.inl a)))
    hZsize hWsize ?_ Profiles'
  · intro a ha
    cases a with
    | inl a=>exact marked_sample_host_arc_separated P π (3*d) (fun e=>σ' (Sum.inl e)) false a
    | inr a=>exact marked_sample_host_arc_separated P π (3*d) (fun e=>σ' (Sum.inl e)) true a
  · intro v u hK h0
    exact htypes v u ⟨h0.1,hK.1⟩

end Oberwolfach

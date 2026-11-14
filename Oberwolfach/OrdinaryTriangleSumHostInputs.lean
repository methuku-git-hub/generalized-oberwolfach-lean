module

public import Oberwolfach.OrdinaryTwoDomainBigEditBounds
public import Oberwolfach.OrdinaryTwoDomainTargetHost
public import Oberwolfach.OrdinaryTwoDomainSampledSpokes
public import Oberwolfach.OrdinaryTwoDomainHostGeometry

@[expose] public section
/-! All edit, forbidden-host and spoke-support hypotheses for the auxiliary
triangle event are discharged from the same original raw sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [LinearOrder U]

theorem ordinary_triangle_sum_host_inputs
    (P F Q:SimpleGraph V) (J:V→U→Prop) (π:Equiv.Perm V) (σ:Equiv.Perm (V⊕U))
    (b D d:ℕ) (hcomm:∀v,Sum.inl (π v)=σ (Sum.inl v))
    (hF:permutationConflictGraph π b≤F) (hD:∀v,F.degree v≤D) (hQ:Q≤P\F)
    (sample:RawWheelOutcome (V⊕U) (V⊕U) Γ Color) (j:Color) (A:Finset V) (B:Finset U)
    (L:ℝ) (hL:0≤L):
    let e:V↪V⊕U:=⟨Sum.inl,Sum.inl_injective⟩
    let f:U↪V⊕U:=⟨Sum.inr,Sum.inr_injective⟩
    let small:=ordinaryRawRestrictPair e f sample
    let R:=rawWheelGraph P small\F
    let H:=rawWheelSpokes π d small j;
    (∀v,((changed (R.neighborFinset v) (Q.neighborFinset v)).card:ℝ)≤L) →
    (∀v,((changed (Finset.univ.filter (H v)) (Finset.univ.filter (J v))).card:ℝ)≤L) →
    (∀u,((changed (Finset.univ.filter (fun v=>H v u)) (Finset.univ.filter (fun v=>J v u))).card:ℝ)≤L) →
    let P':=P.map e
    let F':=ordinaryTwoDomainConflict F σ b
    let R':=rawWheelGraph P' sample\F'
    let H':=bipartiteRelationGraph (ordinarySumRimSet (V:=V) (U:=U)) (ordinarySumHubSet (V:=V) B)
      (ordinary_sum_domains_disjoint B) (rawWheelSpokes σ d sample j)
    let Q':=Q.map e
    let J':=ordinaryPhysicalSpokeGraph (fun v u=>u∈B∧J v u)
    let A':=A.image (Sum.inl:V→V⊕U)
    let B':=ordinarySumHubSet (V:=V) B
    let L':=L+D+2*b;
    Q'≤P'\F' ∧ (∀z,(F'.degree z:ℝ)≤L') ∧
    (∀z,((changed (A'∩R'.neighborFinset z) (A'∩Q'.neighborFinset z)).card:ℝ)≤L') ∧
    (∀z,((changed (B'∩H'.neighborFinset z) (B'∩J'.neighborFinset z)).card:ℝ)≤L') ∧
    (∀z∈B',((changed (A'∩H'.neighborFinset z) (A'∩J'.neighborFinset z)).card:ℝ)≤L') ∧
    (∀z,((R'\Q').degree z:ℝ)≤L') ∧ (∀z,((Q'\R').degree z:ℝ)≤L') ∧
    (∀z,((H'\J').degree z:ℝ)≤L') ∧ (∀z,((J'\H').degree z:ℝ)≤L') ∧
    (∀a∈ordinarySumRimSet (V:=V) (U:=U),J'.neighborFinset a⊆B'):=by
  intro e f small R H hR hrow hcol P' F' R' H' Q' J' A' B' L'
  have hbound:L≤L':=by
    dsimp [L']
    have hh:(0:ℝ)≤D+2*b:=by positivity
    linarith
  have hRim:=ordinary_two_domain_sampled_rims P F π σ b D hcomm hF hD sample
  have hSpoke:=ordinary_two_domain_sampled_spokes B π σ hcomm d sample j
  have heR:R'=R.map e:=hRim.2.symm
  have heH:H'=ordinaryPhysicalSpokeGraph (fun v u=>u∈B∧H v u):=hSpoke
  have hb:=ordinary_two_domain_big_edit_bounds R Q H J A B L hL
    (by intro v;convert hR v using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
    (by intro v;convert hrow v using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
    (by intro u;convert hcol u using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
  have hd:∀z,(F'.degree z:ℝ)≤L':=by
    intro z
    have hh:=(ordinary_two_domain_conflict_properties F π σ b D hcomm hF hD).2.2 z
    have hh':(F'.degree z:ℝ)≤(D:ℝ)+2*b:=by exact_mod_cast hh
    dsimp [L'];linarith
  have hhost:Q'≤P'\F':=ordinary_two_domain_target_host P F Q π σ b D hcomm hF hD hQ
  have hdom:∀a∈ordinarySumRimSet (V:=V) (U:=U),J'.neighborFinset a⊆B':=
    (ordinary_sum_hosts_supported Q J B).2.2.2
  refine ⟨hhost,hd,?_,?_,?_,?_,?_,?_,?_,hdom⟩
  · intro z;convert (hb.1 z).trans hbound using 1 <;> congr! 10 <;> first | exact heR | exact heH | rfl | exact Subsingleton.elim _ _
  · intro z;convert (hb.2.1 z).trans hbound using 1 <;> congr! 10 <;> first | exact heR | exact heH | rfl | exact Subsingleton.elim _ _
  · intro z hz;convert (hb.2.2.1 z hz).trans hbound using 1 <;> congr! 10 <;> first | exact heR | exact heH | rfl | exact Subsingleton.elim _ _
  · intro z;convert (hb.2.2.2.1 z).trans hbound using 1 <;> congr! 10 <;> first | exact heR | exact heH | rfl | exact Subsingleton.elim _ _
  · intro z;convert (hb.2.2.2.2.1 z).trans hbound using 1 <;> congr! 10 <;> first | exact heR | exact heH | rfl | exact Subsingleton.elim _ _
  · intro z;convert (hb.2.2.2.2.2.1 z).trans hbound using 1 <;> congr! 10 <;> first | exact heR | exact heH | rfl | exact Subsingleton.elim _ _
  · intro z;convert (hb.2.2.2.2.2.2 z).trans hbound using 1 <;> congr! 10 <;> first | exact heR | exact heH | rfl | exact Subsingleton.elim _ _
end Oberwolfach

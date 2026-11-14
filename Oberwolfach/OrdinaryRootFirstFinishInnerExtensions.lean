module

public import Oberwolfach.OrdinaryRootFirstInnerExtensionCounts
public import Oberwolfach.OrdinaryRootFirstPrecoverSelectionData
public import Oberwolfach.OrdinaryRootFirstCleanupRemainder
public import Oberwolfach.OrdinaryRootFirstPostCleanupCounts
public import Oberwolfach.OrdinaryGeneralSampledRemainderLocalCleared
public import Oberwolfach.BoundaryDegreeAfterPacking

@[expose] public section
/-! Finish the actual root-first cleaned host using pairing and support
tests formed from the earlier pre-cover parent on the same coins. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 24000000
set_option synthInstance.maxSize 8192
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]

theorem ordinary_root_first_finish_from_inner_extension_counts
    (m:ℕ) (hm:3≤m) (P Q Qfactor F:SimpleGraph V) (H Hfactor:V→U→Prop)
    (π:Equiv.Perm V) (d:ℕ) (X T:Finset V) (Z W:Finset U) (η ell t ν:ℝ)
    (D:OrdinaryRootCoverData Q F H X T Z W (m+1) η ell) (σ:Sym2 (V⊕U)→Bool)
    (O:OrdinaryRootFirstCleanupOutcome Q F H X T Z W (m+1) η ell t ν D σ)
    (pR pH p density tR tH Ledit βe₀ βh₀ βe βh ρ ζ εsup:ℝ)
    (s:U→Color→ℝ) (j:Color) (raw:RawWheelOutcome V U Γ Color)
    (ht:0≤t) (hp:0≤p) (hQF:Disjoint Q F)
    (hbal:∀v,Q.degree v=2*(Finset.univ.filter (H v)).card)
    (hdiv:∀u,(m+1)∣(Finset.univ.filter (fun v=>H v u)).card)
    (profile:OrdinaryCleanupParentProfiles P Q F H π d X Z pR pH density tR tH Ledit βe₀ βh₀ s j raw)
    (hmE:βe*Fintype.card (V⊕U)+3*max η ell≤βe₀*Fintype.card (V⊕U))
    (hmH:βh*Fintype.card (V⊕U)+2*ell≤βh₀*Fintype.card (V⊕U)):
    let K:=O.context;
    let Q₂:=ordinaryRootFirstCleanRemainderRim Q F H X T Z W (m+1) η ell t ν D σ O;
    let H₂:=ordinaryRootFirstCleanRemainderSpokes Q F H X T Z W (m+1) η ell t ν D σ O;
    BoundaryReserveSupportGood (ordinaryBoundaryGraph Q H X Z) p εsup σ→
    OrdinaryBoundaryExtensionGood (Q\K.cover.rim) (fun v u=>H v u∧¬K.cover.spokes v u) X βe p σ→
    OrdinaryBoundaryHubPairGood (fun v u=>H v u∧¬K.cover.spokes v u) Z βh p σ→
    MixedFreshPairingAvoidingEvent m p ρ ζ Qfactor F (ordinaryPhysicalGraph Qfactor Hfactor)
      (ordinaryPhysicalGraph F (fun _ _=>False)) (Function.Embedding.inl:V↪V⊕U)
      (ordinaryBoundaryHubSet H Z X) (fun i=>(ordinaryBoundaryRimSet Q X i).image Sum.inl)
      (fun i=>(ordinaryBoundaryRowSet H X Z i).image Sum.inr)
      (fun j=>hubSpokeCoin j.val) (fun i=>physicalIncidentCoin (Sum.inl i.val)) σ→
    ordinaryPhysicalGraph Qfactor Hfactor≤spanningRestriction (ordinaryPhysicalGraph Q H) (ordinaryInnerVertices X Z)→
    (p+εsup)*Fintype.card (V⊕U)+(t+ν)≤ρ*Fintype.card (V⊕U)→
    (p^2+εsup)*Fintype.card (V⊕U)+2*(t+ν)≤ρ^2*Fintype.card (V⊕U)→
    (∀j:{u:U // u∉Z},t+ν+ell≤ζ*(p*(ordinaryBoundaryHubSet H Z X j).card))→
    t+ν+ell≤ζ*(p*Fintype.card (V⊕U))→
    (∀j:{u:U // u∉Z},2*(ρ*Real.sqrt ρ*Fintype.card (V⊕U))+
      2*(Nat.ceil (4*(ρ*Real.sqrt ρ*Fintype.card (V⊕U))):ℝ)+(ν+η)≤ζ*(p*(ordinaryBoundaryHubSet H Z X j).card))→
    2*(ρ*Real.sqrt ρ*Fintype.card (V⊕U))+
      2*(Nat.ceil (4*(ρ*Real.sqrt ρ*Fintype.card (V⊕U))):ℝ)+(ν+η)≤ζ*(p*Fintype.card (V⊕U))→
    ∀(Dmax Kcap:ℕ),0<Kcap→ρ*Fintype.card (V⊕U)≤(Dmax:ℝ)→
    ∀Lconf:ℝ,0≤Lconf→(∀v,(F.degree v:ℝ)≤Lconf)→
    ((Fintype.card (Σi:{v:V // v∉X},ordinaryBoundaryRowSet H₂ X Z i)*(m+1):ℕ):ℝ)/(Kcap:ℝ)+
      (((m+1:ℕ):ℝ)+3)*(Lconf+1)+2*(2*(ρ*Fintype.card (V⊕U))+2*((Kcap+Dmax:ℕ):ℝ))+
      (Dmax:ℝ)+((Dmax*(m+1):ℕ):ℝ)+3*Dmax<βe*Fintype.card (V⊕U)-3*ν-T.card→
    Nonempty (OrdinaryRootFirstFinishData Q F H X T Z W (m+1) η ell t ν D σ O
      (2*(ρ*Fintype.card (V⊕U))+((3*(Kcap+Dmax)+Dmax*(m+1):ℕ):ℝ))):=by
  intro K Q₂ H₂ hsample hevent hhevent hgood hbase hdeg hpair hscaleY hscaleZ hbudgetY hbudgetZ
    Dmax Kcap hKcap hDmax Lconf hLconf hF hcompletion
  let C:=ordinaryRootFirstPrecoverPrior Q F H X T Z W (m+1) η ell t K σ
  let E:=ordinaryPhysicalGraph K.cover.rim K.cover.spokes
  let J:=ordinaryPhysicalGraph (wheelFamilyRim O.cleanup.wheels) (wheelFamilySpokes O.cleanup.wheels)
  let Klocal:=J⊔spanningRestriction E (ordinaryInnerVertices X Z)
  have hf:=ordinary_root_first_precover_selection_data Q Qfactor F H Hfactor X T Z W (m+1) η ell t ν D σ O ht hbase
  have hr:=ordinary_root_first_cleanup_remainder Q F H X T Z W (m+1) η ell t ν D σ O hbal hdiv
  have hb:=boundary_degree_after_packing (ordinaryBoundaryGraph Q H X Z) C J σ p εsup (t+ν)
    hp hsample hf.1 hf.2.2.2.1
  have hQF':Disjoint Q₂ F:=hQF.mono_left (show Q₂≤Q from sdiff_le.trans (sdiff_le.trans sdiff_le))
  have hQdeg:∀w:V⊕U,(ordinaryBoundaryGraph Q₂ H₂ X Z).degree w≤Dmax:=by
    intro w
    have hsub:((ordinaryBoundaryGraph Q₂ H₂ X Z).degree w:ℝ)≤
        ((((ordinaryBoundaryGraph Q H X Z\C)\J).degree w):ℝ):=by
      exact_mod_cast SimpleGraph.degree_le_of_le hf.2.2.1 (v:=w)
    have hbound:=hsub.trans ((hb w).trans (hdeg.trans hDmax))
    exact_mod_cast hbound
  have hcounts:=ordinary_root_first_inner_extension_counts P Q F H π d X T Z W (m+1) η ell t ν D σ O
    pR pH density tR tH Ledit βe₀ βh₀ βe βh s j raw profile hmE hmH
  have hcount:∀i,∀z∈ordinaryBoundaryRowSet H₂ X Z i,∀v∈X,∀w∈X,
      βe*Fintype.card (V⊕U)-3*ν≤(((X.filter (fun a=>H₂ a z))∩Q₂.neighborFinset v∩Q₂.neighborFinset w).card:ℝ):=by
    intro i z hz v hv w hw
    have hzZ:z∈Z:=(Finset.mem_filter.mp hz).1
    convert hcounts z hzZ v hv w hw using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  have hbal₂:∀v,Q₂.degree v=2*(Finset.univ.filter (H₂ v)).card:=by
    intro v;convert hr.2.1 v using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  have hdiv₂:∀u,(m+1)∣(Finset.univ.filter (fun v=>H₂ v u)).card:=by
    intro u;convert hr.2.2.1 u using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  obtain ⟨Rfin,Sfin,hR,hS,hhost,hdec,hinside,hsp,_,_,_,hcost,hstar,_⟩:=
    ordinary_general_sampled_remainder_cleared_roots_local_changes m hm Q Qfactor Q₂ F H Hfactor H₂ X T Z W
      K.root_sub K.hub_sub C J (J⊔E) Klocal σ p ρ ζ εsup (t+ν) (t+ν+ell) (ν+η) hgood hp hsample
      hf.1 hf.2.1 hf.2.2.1 hf.2.2.2.1
      (by intro j;convert hf.2.2.2.2.1 (Sum.inr j.val) (by simpa [ordinaryInnerVertices_right] using j.property)
        using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
      (by intro i;convert hf.2.2.2.2.1 (Sum.inl i.val) (by simpa [ordinaryInnerVertices_left] using i.property)
        using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
      (by intro w;convert hf.2.2.2.2.2.1 w using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _) hf.2.2.2.2.2.2
      hr.2.2.2.2.2.1 hr.2.2.2.2.2.2.1 hr.2.2.2.2.2.2.2 hr.2.2.2.1 hr.2.2.2.2.1 hbal₂ hdiv₂
      hdeg hpair hscaleY hscaleZ hbudgetY hbudgetZ hQF' Dmax Kcap hKcap hQdeg Lconf
      (βe*Fintype.card (V⊕U)-3*ν) hLconf hF hcount (by linarith only [hcompletion])
  refine ⟨⟨Rfin,Sfin,hR,hS,hhost,hdec,?_,?_,hcost,hstar⟩⟩
  · exact (SimpleGraph.support_mono hinside).trans (spanningRestriction_support Q₂ X)
  · intro v u hvu
    exact ⟨(hsp v u hvu).2.1,(hsp v u hvu).2.2⟩
end Oberwolfach

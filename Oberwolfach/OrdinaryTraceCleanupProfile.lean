module

public import Oberwolfach.OrdinaryTraceRawPairEdits
public import Oberwolfach.OrdinaryRawRowsPairRestriction
public import Oberwolfach.OrdinaryRawDomainPairRestriction
public import Oberwolfach.OrdinaryInducedTargetNeighbourCount
public import Oberwolfach.OrdinaryCleanupProfileFromDeepSample

@[expose] public section
/-! An ambient common sample and a protected trace supply the actual cleanup
profile on the next induced pair, with the initial and latest edit costs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem ordinary_trace_cleanup_profile
    (P Q F:SimpleGraph V) (H:V→U→Prop) (π:Equiv.Perm V) (d:ℕ)
    (j:Color) (σ:RawWheelOutcome V U Γ Color)
    (X T:ℕ→Finset V) (Z W:ℕ→Finset U) (cost deepCost:ℕ→ℝ) (i:ℕ)
    (A:Finset (Sym2 V⊕(V×U))) (G:SimpleGraph V) (Hs:V→U→Prop)
    (ρ:Equiv.Perm ↥(X i)) (hcomm:∀x:↥(X i),(ρ x).val=π x.val)
    (D:Finset ↥(X i)) (E:Finset ↥(Z i))
    (pR pH density tR tH L βe βh:ℝ) (s:U→Color→ℝ)
    (hpR:0≤pR) (hpR1:pR≤1) (hpH:0≤pH) (hdensity:1/2≤density) (hs:∀u,s u j=pH)
    (hQF:Disjoint Q F)
    (hbase:∀w:V⊕U,((changed ((ordinaryPhysicalGraph (rawWheelGraph P σ)
      (rawWheelSpokes π d σ j)).neighborFinset w) ((ordinaryPhysicalGraph Q H).neighborFinset w)).card:ℝ)≤L)
    (htrace:OrdinaryProtectedTrace Q H X T Z W cost deepCost (i+1) A)
    (hstate:ordinaryHostResources G Hs=A)
    (hX:∀j < i,X i⊆T j) (hZ:∀j < i,Z i⊆W j):
    let V₁:=↥(X i);let U₁:=↥(Z i);
    let f:V₁↪V:=⟨Subtype.val,Subtype.val_injective⟩;
    let g:U₁↪U:=⟨Subtype.val,Subtype.val_injective⟩;
    (∀v:V₁,density*(D.image f).card≤(((D.image f)∩P.neighborFinset (f v)).card:ℝ))→
    RawOrdinaryRows P π d 3 (D.image f) pR s j tR σ→
    RawOrdinaryDomainIndices F π d 3 (E.image g) pH j tH σ→
    βe*Fintype.card (V₁⊕U₁)+tR+3*(L+cost i)≤pR^2*pH*(2*density-1)*D.card→
    βh*Fintype.card (V₁⊕U₁)+tH+2*(L+cost i)≤pH^2*E.card→
    OrdinaryCleanupParentProfiles (P.induce ((X i):Set V)) (G.induce ((X i):Set V)) (F.induce ((X i):Set V))
      (fun (v:V₁) (u:U₁)=>Hs v.val u.val) ρ d D E pR pH density tR tH (L+cost i) βe βh
      (fun u=>s (g u)) j (ordinaryRawRestrictPair f g σ):=by
  intro V₁ U₁ f g hmin hrows hcols hext hhub
  have hle:G≤Q:=by
    obtain ⟨R,S,hist,_,_⟩:=htrace
    have hG: G=ordinaryHistoryRim Q R S (i+1):=
      (ordinaryHostResources_injective G (ordinaryHistoryRim Q R S (i+1)) Hs
        (ordinaryHistorySpokes H R S (i+1)) (hstate.trans hist.symm)).1
    rw [hG]
    intro v w hvw
    exact hvw.1
  have hdis:Disjoint (G.induce ((X i):Set V)) (F.induce ((X i):Set V)):=by
    apply disjoint_iff_inf_le.mpr
    intro v w hvw
    exact (disjoint_iff_inf_le.mp hQF) ⟨hle hvw.1,hvw.2⟩
  have hm:∀v:V₁,density*D.card≤((D∩(P.induce ((X i):Set V)).neighborFinset v).card:ℝ):=by
    intro v
    have hh:=hmin v
    rw [Finset.card_image_of_injective _ f.injective,←ordinary_comap_target_neighbour_card P f D v] at hh
    exact hh
  have hr:=ordinary_raw_rows_pair_restriction f g P π ρ hcomm d 3 D pR s j tR σ hrows
  have hc:=ordinary_raw_domain_pair_restriction f g F π ρ hcomm d 3 E pH j tH σ hcols
  have he:=ordinary_trace_raw_pair_edits P Q H π d j σ X T Z W cost deepCost i A G Hs ρ hcomm L hbase htrace hstate hX hZ
  refine ⟨hpR,hpR1,hpH,hdensity,(fun u=>hs (g u)),hdis,?_,?_,?_,?_,?_,?_,hext,hhub⟩
  · intro v
    convert hm v using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  · intro S J hS hJ
    have hh:=hr S J (by omega) (by omega)
    convert hh using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  · intro S hS hfree
    have hh:=hc S hS hfree
    convert hh using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  · intro v
    convert he.1 v using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  · intro u
    convert he.2.2 u using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  · intro v
    convert he.2.1 v using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
end Oberwolfach

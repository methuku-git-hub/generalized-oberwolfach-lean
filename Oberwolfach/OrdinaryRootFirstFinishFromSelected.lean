module

public import Oberwolfach.OrdinaryRootFirstFinishData
public import Oberwolfach.OrdinaryRootFirstCleanupRemainder
public import Oberwolfach.OrdinaryGeneralCanonicalRemainderClearedRoots

@[expose] public section
/-! Selected boundary factors on the actual cleaned host give the final
root-free finish; all packing and size budgets remain explicit. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_root_first_finish_from_selected
    (m:ℕ) (hm:3≤m) (Q F:SimpleGraph V) (H:V→U→Prop)
    (X Tdeep:Finset V) (Z Wdeep:Finset U) (η ell t ν:ℝ)
    (D:OrdinaryRootCoverData Q F H X Tdeep Z Wdeep (m+1) η ell) (σ:Sym2 (V⊕U)→Bool)
    (O:OrdinaryRootFirstCleanupOutcome Q F H X Tdeep Z Wdeep (m+1) η ell t ν D σ)
    (hQF:Disjoint Q F)
    (hbal:∀v,Q.degree v=2*(Finset.univ.filter (H v)).card)
    (hdiv:∀u,(m+1)∣(Finset.univ.filter (fun v=>H v u)).card):
    let Q₂:=ordinaryRootFirstCleanRemainderRim Q F H X Tdeep Z Wdeep (m+1) η ell t ν D σ O;
    let H₂:=ordinaryRootFirstCleanRemainderSpokes Q F H X Tdeep Z Wdeep (m+1) η ell t ν D σ O;
    ∀(T:{u:U // u∉Z}→Finset V) (Kcap Dmax:ℕ),0<Kcap→
    (∀i,(ordinaryBoundaryRowSet H₂ X Z i).card≤Dmax)→
    (∀j,(ordinaryBoundaryHubSet H₂ Z X j).card≤Dmax)→
    (∀v,(Finset.univ.filter (fun i=>v∈ordinaryBoundaryRimSet Q₂ X i)).card≤Dmax)→
    (∀z,(Finset.univ.filter (fun i=>z∈ordinaryBoundaryRowSet H₂ X Z i)).card≤Dmax)→
    ∀(Lconf limit bcount:ℝ),0≤Lconf→(∀v,(F.degree v:ℝ)≤Lconf)→
    (∀i,∀z∈ordinaryBoundaryRowSet H₂ X Z i,∀v∈X,∀w∈X,
      bcount≤(((X.filter (fun a=>H₂ a z))∩Q₂.neighborFinset v∩Q₂.neighborFinset w).card:ℝ))→
    ((Fintype.card (Σi:{v:V // v∉X},ordinaryBoundaryRowSet H₂ X Z i)*(m+1):ℕ):ℝ)/(Kcap:ℝ)+
      (((m+1:ℕ):ℝ)+3)*(Lconf+1)+2*(limit+2*((Kcap+Dmax:ℕ):ℝ))+
      (Dmax:ℝ)+((Dmax*(m+1):ℕ):ℝ)+3*Dmax<bcount-Tdeep.card→
    OrdinaryPairingSelectedFactors m Q₂ F H₂ (ordinaryBoundaryRimSet Q₂ X) (ordinaryBoundaryRowSet H₂ X Z)
      T (ordinaryBoundaryHubSet H₂ Z X) limit→
    Nonempty (OrdinaryRootFirstFinishData Q F H X Tdeep Z Wdeep (m+1) η ell t ν D σ O
      (limit+((3*(Kcap+Dmax)+Dmax*(m+1):ℕ):ℝ))):=by
  intro Q₂ H₂ T Kcap Dmax hKcap hBsize hYsize hmemA hmemB Lconf limit bcount hLconf hF hcount hbudget C
  have hc:=ordinary_root_first_cleanup_remainder Q F H X Tdeep Z Wdeep (m+1) η ell t ν D σ O hbal hdiv
  have hdis:Disjoint Q₂ F:=hQF.mono_left (show Q₂≤Q from sdiff_le.trans (sdiff_le.trans sdiff_le))
  have hbal₂:∀v,Q₂.degree v=2*(Finset.univ.filter (H₂ v)).card:=by
    intro v;convert hc.2.1 v using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  have hdiv₂:∀u,(m+1)∣(Finset.univ.filter (fun v=>H₂ v u)).card:=by
    intro u;convert hc.2.2.1 u using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  obtain ⟨R,S,hR,hS,hhost,hdec,hinside,hsp,_,_,_,hcost,hstar,_⟩:=
    ordinary_general_canonical_boundary_remainder_cleared_roots m hm Q₂ F H₂ X Tdeep Z Wdeep
      O.context.root_sub O.context.hub_sub hdis hc.2.2.2.2.2.1 hc.2.2.2.2.2.2.1 hc.2.2.2.2.2.2.2
      hc.2.2.2.1 hc.2.2.2.2.1 hbal₂ hdiv₂ T Kcap Dmax hKcap hBsize hYsize hmemA hmemB
      Lconf limit bcount hLconf hF hcount hbudget C
  refine ⟨⟨R,S,hR,hS,hhost,hdec,?_,?_,hcost,hstar⟩⟩
  · exact (SimpleGraph.support_mono hinside).trans (spanningRestriction_support Q₂ X)
  · intro v u hu
    exact ⟨(hsp v u hu).2.1,(hsp v u hu).2.2⟩
end Oberwolfach

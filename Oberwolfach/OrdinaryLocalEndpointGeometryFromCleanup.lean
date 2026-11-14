module

public import Oberwolfach.OrdinaryEndpointPairingGeometryFromCleanup
public import Oberwolfach.OrdinaryPhysicalInnerEndpointDomain

@[expose] public section
/-! The existing sampled cleanup profile gives the endpoint geometry on
the actual fixed inner physical domain, with local-scale size bounds. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]

theorem ordinary_local_endpoint_geometry_from_cleanup
    (P Q F:SimpleGraph V) (H:V→U→Prop) (A:Finset V) (B:Finset U)
    (π:Equiv.Perm V) (d:ℕ) (j:Color) (s:U→Color→ℝ)
    (pR pH density tR tH L βe βh a η:ℝ) (σ:RawWheelOutcome V U Γ Color)
    (profile:OrdinaryCleanupParentProfiles P Q F H π d A B pR pH density tR tH L βe βh s j σ)
    (hA:A.Nonempty)
    (hRsize:∀x,a*(ordinaryPhysicalInnerDomain A B).card≤((A∩Q.neighborFinset x).card:ℝ))
    (hHsize:∀x,a*(ordinaryPhysicalInnerDomain A B).card≤((B.filter (H x)).card:ℝ))
    (hrow:∀x,(tH+2*L)+pH*(tH+L)≤η*(B.filter (H x)).card)
    (hcol:∀x,(tR+2*L)+pH*(tR+L)≤η*(A∩Q.neighborFinset x).card)
    (hcodeg:∀x,(tH+3*L)+pH^2*(tH+L)≤η*(B.filter (H x)).card):
    let S:=fun i:{v:V // v∉A}=>(ordinaryBoundaryRimSet Q A i).image (Sum.inl:V→V⊕U);
    let R:=fun i:{v:V // v∉A}=>(ordinaryBoundaryRowSet H A B i).image (Sum.inr:U→V⊕U);
    let G:=ordinaryPhysicalGraph (spanningRestriction Q A) (fun v u=>H v u∧v∈A∧u∈B);
    let K:=ordinaryPhysicalGraph F (fun _ _=>False);
    (∀i,S i⊆ordinaryPhysicalInnerDomain A B) ∧ (∀i,R i⊆ordinaryPhysicalInnerDomain A B) ∧
    (∀i,Disjoint (S i) (R i)) ∧
    (∀i,a*(ordinaryPhysicalInnerDomain A B).card≤((S i).card:ℝ) ∧
      a*(ordinaryPhysicalInnerDomain A B).card≤((R i).card:ℝ)) ∧
    (∀i v,v∈S i→|(((R i)∩G.neighborFinset v).card:ℝ)-pH*(R i).card|≤η*(R i).card) ∧
    (∀i u,u∈R i→|(((S i)∩G.neighborFinset u).card:ℝ)-pH*(S i).card|≤η*(S i).card) ∧
    (∀i v,v∈S i→∀w,w∈S i→v≠w→¬K.Adj v w→
      ((((R i)∩G.neighborFinset v)∩G.neighborFinset w).card:ℝ)≤(pH^2+η)*(R i).card):=by
  intro S R G K
  have hn:0<Fintype.card (V⊕U):=Fintype.card_pos_iff.mpr ⟨Sum.inl hA.choose⟩
  have hnR:0<(Fintype.card (V⊕U):ℝ):=by exact_mod_cast hn
  let c:ℝ:=a*(ordinaryPhysicalInnerDomain A B).card/Fintype.card (V⊕U)
  have hc:c*Fintype.card (V⊕U)=a*(ordinaryPhysicalInnerDomain A B).card:=by
    dsimp [c]
    exact div_mul_cancel₀ _ hnR.ne'
  have hrs:∀x,c*Fintype.card (V⊕U)≤((A∩Q.neighborFinset x).card:ℝ):=by
    intro x;rw [hc];exact hRsize x
  have hhs:∀x,c*Fintype.card (V⊕U)≤((B.filter (H x)).card:ℝ):=by
    intro x;rw [hc];exact hHsize x
  have hh:=ordinary_endpoint_pairing_geometry_from_cleanup P Q F H A B π d j s pR pH density tR tH L βe βh c η σ
    profile hrs hhs hrow hcol hcodeg
  have hdom:=ordinary_physical_inner_endpoint_domains Q H A B
  refine ⟨hdom.1,hdom.2,hh.1,?_,hh.2.2.1,hh.2.2.2.1,hh.2.2.2.2⟩
  intro i
  simpa only [hc] using hh.2.1 i
end Oberwolfach

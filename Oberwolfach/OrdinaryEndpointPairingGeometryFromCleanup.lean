module

public import Oberwolfach.OrdinaryEndpointSpokeRelativeProfiles
public import Oberwolfach.OrdinaryEndpointRimRelativeProfiles
public import Oberwolfach.OrdinaryEndpointPairingPhysicalCounts
public import Oberwolfach.OrdinaryBoundaryRootSets

@[expose] public section
/-! The endpoint degree and codegree requirements for the general-length
    fresh pairing theorem hold on the actual edited cleanup host. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 12000000
set_option synthInstance.maxSize 8192
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]

theorem ordinary_endpoint_pairing_geometry_from_cleanup
    (P Q F:SimpleGraph V) (H:V→U→Prop) (A:Finset V) (B:Finset U)
    (π:Equiv.Perm V) (d:ℕ) (j:Color) (s:U→Color→ℝ)
    (pR pH density tR tH L βe βh a η:ℝ) (σ:RawWheelOutcome V U Γ Color)
    (profile:OrdinaryCleanupParentProfiles P Q F H π d A B pR pH density tR tH L βe βh s j σ)
    (hRsize:∀x,a*Fintype.card (V⊕U)≤((A∩Q.neighborFinset x).card:ℝ))
    (hHsize:∀x,a*Fintype.card (V⊕U)≤((B.filter (H x)).card:ℝ))
    (hrow:∀x,(tH+2*L)+pH*(tH+L)≤η*(B.filter (H x)).card)
    (hcol:∀x,(tR+2*L)+pH*(tR+L)≤η*(A∩Q.neighborFinset x).card)
    (hcodeg:∀x,(tH+3*L)+pH^2*(tH+L)≤η*(B.filter (H x)).card):
    let S:=fun i:{v:V // v∉A}=>(ordinaryBoundaryRimSet Q A i).image (Sum.inl:V→V⊕U);
    let T:=fun i:{v:V // v∉A}=>(ordinaryBoundaryRowSet H A B i).image (Sum.inr:U→V⊕U);
    let Pinner:=ordinaryPhysicalGraph (spanningRestriction Q A) (fun v u=>H v u∧v∈A∧u∈B);
    let Fphys:=ordinaryPhysicalGraph F (fun _ _=>False);
    (∀i,Disjoint (S i) (T i)) ∧
    (∀i,a*Fintype.card (V⊕U)≤((S i).card:ℝ) ∧ a*Fintype.card (V⊕U)≤((T i).card:ℝ)) ∧
    (∀i v,v∈S i→|(((T i)∩Pinner.neighborFinset v).card:ℝ)-pH*(T i).card|≤η*(T i).card) ∧
    (∀i u,u∈T i→|(((S i)∩Pinner.neighborFinset u).card:ℝ)-pH*(S i).card|≤η*(S i).card) ∧
    (∀i v,v∈S i→∀w,w∈S i→v≠w→¬Fphys.Adj v w→
      ((((T i)∩Pinner.neighborFinset v)∩Pinner.neighborFinset w).card:ℝ)≤(pH^2+η)*(T i).card):=by
  intro S T Pinner Fphys
  have hspoke:=ordinary_endpoint_spoke_relative_profiles P Q F H A B π d j s pR pH density tR tH L βe βh σ profile
  have hrim:=ordinary_endpoint_rim_relative_profiles P Q F H A B π d j s pR pH density tR tH L βe βh σ profile
  have hScard (i:{v:V // v∉A}):(S i).card=(A∩Q.neighborFinset i.val).card:=by
    simp only [S,ordinaryBoundaryRimSet,Finset.card_image_of_injective _ Sum.inl_injective,Finset.inter_comm]
  have hTcard (i:{v:V // v∉A}):(T i).card=(B.filter (H i.val)).card:=by
    simp only [T,ordinaryBoundaryRowSet,Finset.card_image_of_injective _ Sum.inr_injective]
  constructor
  · intro i
    exact ordinary_boundary_root_domains_disjoint Q H A B i
  constructor
  · intro i
    simpa only [hScard,hTcard] using And.intro (hRsize i.val) (hHsize i.val)
  constructor
  · intro i v hv
    obtain ⟨v,hv,rfl⟩:=Finset.mem_image.mp hv
    have hv':v∈Q.neighborFinset i.val∩A:=by simpa [S,ordinaryBoundaryRimSet] using hv
    have hvA:= (Finset.mem_inter.mp hv').2
    have hQ:=(Q.mem_neighborFinset i.val v).mp (Finset.mem_inter.mp hv').1
    have he:(((T i)∩Pinner.neighborFinset (Sum.inl v)).card:ℝ)=
        ((B.filter (fun u=>H i.val u∧H v u)).card:ℝ):=by
      simpa [T,Pinner,ordinaryBoundaryRowSet] using (ordinary_endpoint_pairing_physical_counts Q H A B i.val).1 v hvA
    rw [he,hTcard]
    exact (hspoke.1 i.val v hQ).trans (hrow i.val)
  constructor
  · intro i u hu
    obtain ⟨u,hu,rfl⟩:=Finset.mem_image.mp hu
    have hu':u∈B.filter (H i.val):=by simpa [T,ordinaryBoundaryRowSet] using hu
    have huB: u∈B:=(Finset.mem_filter.mp hu').1
    have he:(((S i)∩Pinner.neighborFinset (Sum.inr u)).card:ℝ)=
        ((A.filter (fun v=>Q.Adj i.val v∧H v u)).card:ℝ):=by
      simpa [S,Pinner,ordinaryBoundaryRimSet,Finset.inter_comm] using
        (ordinary_endpoint_pairing_physical_counts Q H A B i.val).2.1 u huB
    rw [he,hScard]
    exact (hrim.2 i.val u).trans (hcol i.val)
  · intro i v hv w hw hvw hfree
    obtain ⟨v,hv,rfl⟩:=Finset.mem_image.mp hv
    obtain ⟨w,hw,rfl⟩:=Finset.mem_image.mp hw
    have hv':v∈Q.neighborFinset i.val∩A:=by simpa [S,ordinaryBoundaryRimSet] using hv
    have hw':w∈Q.neighborFinset i.val∩A:=by simpa [S,ordinaryBoundaryRimSet] using hw
    have hvA: v∈A:=(Finset.mem_inter.mp hv').2
    have hwA: w∈A:=(Finset.mem_inter.mp hw').2
    have hQv:=(Q.mem_neighborFinset i.val v).mp (Finset.mem_inter.mp hv').1
    have hQw:=(Q.mem_neighborFinset i.val w).mp (Finset.mem_inter.mp hw').1
    have hvw':v≠w:=fun h=>hvw (by rw [h])
    have hfree':¬F.Adj v w:=by simpa [Fphys,ordinaryPhysicalGraph] using hfree
    have he:((((T i)∩Pinner.neighborFinset (Sum.inl v))∩Pinner.neighborFinset (Sum.inl w)).card:ℝ)=
        ((B.filter (fun u=>H i.val u∧H v u∧H w u)).card:ℝ):=by
      simpa [T,Pinner,ordinaryBoundaryRowSet] using
        (ordinary_endpoint_pairing_physical_counts Q H A B i.val).2.2 v hvA w hwA
    rw [he,hTcard]
    have hh:=(hspoke.2 i.val v w hQv hQw hvw' hfree').trans (hcodeg i.val)
    have hu:=(abs_le.mp hh).2
    nlinarith only [hu]
end Oberwolfach

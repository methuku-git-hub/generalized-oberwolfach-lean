module

public import Oberwolfach.OrdinaryTriangleNormalizedMixedProbability
public import Oberwolfach.OrdinaryTriangleRootFirstSampleEvent
public import Oberwolfach.OrdinaryPhysicalInnerEndpointDomain
public import Oberwolfach.BoundaryReserveSupportEvent
public import Oberwolfach.PhysicalWheelFamilies

@[expose] public section
/-! An inner-scale hub and endpoint probability bound supplies the ordinary
triangle fresh event on the same ambient coins, with a support event. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 24000000
set_option synthInstance.maxSize 8192
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_triangle_fresh_sample_from_inner
    (p εsup:ℝ) (hp:0<p) (hp1:p≤1) (hsup:0<εsup) (q:ℕ):∃N:ℕ,
    ∀(V U:Type) [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
      (Q F:SimpleGraph V) (H:V→U→Prop) (A:Finset V) (B:Finset U) (ζh ζe:ℝ),
    N≤A.card→
    let Pinner:=ordinaryPhysicalGraph (spanningRestriction Q A) (fun v u=>H v u∧v∈A∧u∈B);
    let Fphys:=ordinaryPhysicalGraph F (fun _ _=>False);
    let S:=fun i:{v:V // v∉A}=>(ordinaryBoundaryRimSet Q A i).image (Sum.inl:V→V⊕U);
    let T:=fun i:{v:V // v∉A}=>(ordinaryBoundaryRowSet H A B i).image (Sum.inr:U→V⊕U);
    let W:Type:={w:V⊕U // w∈ordinaryPhysicalInnerDomain A B};
    let μ:=FiniteLaw.pi (fun _:Sym2 (V⊕U)=>FiniteLaw.retentionCoin p hp.le hp1);
    1-1/(A.card:ℝ)^(q+1)≤μ.probability (OrdinaryNormalizedHubFactorEvent 2 Q F H A B p ζh)→
    1-1/(Fintype.card W:ℝ)^(q+1)≤μ.probability
      (EndpointTriangleNormalizedFactorEvent Pinner Fphys S T
        (fun i=>physicalIncidentCoin (Sum.inl i.val)) p ζe)→
    1-1/(A.card:ℝ)^q-1/(Fintype.card (V⊕U):ℝ)^q≤
      μ.probability (OrdinaryTriangleFreshFactorSample Q (spanningRestriction Q A) F H
        (fun v u=>H v u∧v∈A∧u∈B) A B p (min ζh ζe) εsup):=by
  obtain ⟨Nf,hNf⟩:=ordinary_triangle_normalized_mixed_probability p hp hp1 q
  obtain ⟨Ns,hNs⟩:=boundary_reserve_support_high_probability εsup hsup q
  refine ⟨max Nf Ns,?_⟩
  intro V U _ _ _ _ Q F H A B ζh ζe hn Pinner Fphys S T W μ hhub hend
  have hAV:A.card≤Fintype.card V:=Finset.card_le_univ A
  have hVW:Fintype.card V≤Fintype.card (V⊕U):=Fintype.card_le_of_injective Sum.inl Sum.inl_injective
  have hW:Fintype.card W=A.card+B.card:=by
    simp only [W,Fintype.card_coe,ordinary_physical_inner_domain_card]
  have hmap:(spanningRestriction Q A).map (Function.Embedding.inl:V↪V⊕U)≤Pinner:=by
    rw [graph_map_inl_physical]
    intro x y hxy
    cases x <;> cases y <;> simpa [Pinner,ordinaryPhysicalGraph] using hxy
  have hfactor:=hNf V U {v:V // v∉A} Q F H A B Pinner Fphys S T
    (fun i=>physicalIncidentCoin (Sum.inl i.val)) (ordinary_boundary_root_domains_disjoint Q H A B)
    ζh ζe (Fintype.card W) (by omega) (by omega) hmap hhub hend
  have hsupport:=hNs (V⊕U) (by omega) (ordinaryBoundaryGraph Q H A B) p hp.le hp1
  have hi:=finiteLaw_intersection_lower μ _ _ (1/(A.card:ℝ)^q)
    (1/(Fintype.card (V⊕U):ℝ)^q) hfactor hsupport
  apply hi.trans
  apply finiteLaw_probability_mono
  intro σ hσ
  exact ⟨hσ.2,hσ.1⟩
end Oberwolfach

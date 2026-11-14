module

public import Oberwolfach.OrdinaryBoundaryHubSubsetChoicesSurvive
public import Oberwolfach.OrdinaryFreeHubExtensions
public import Oberwolfach.OrdinaryBoundarySubsetExtensionsSurvivePacking
public import Oberwolfach.OrdinaryDeepSafeSubsetExtensions
public import Oberwolfach.OrdinaryRootFirstCleanupFacts
public import Oberwolfach.OrdinaryBoundaryCleanupCountsFromSamples

@[expose] public section
/-! Once the same reserve satisfies its local events, the lifted packing
preserves the corresponding extension and hub-choice counts. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_root_first_cleanup_both_free_counts_from_events
    (Q F:SimpleGraph V) (H:V→U→Prop) (X T:Finset V) (Z W:Finset U) (r:ℕ) (η ell t:ℝ)
    (K:OrdinaryRootFirstPackingContext Q F H X T Z W r η ell t) (ht:0≤t)
    (βe βh p:ℝ) (hW:(W.card:ℝ)≤(βh/2)*Fintype.card (V⊕U)) (σ:Sym2 (V⊕U)→Bool)
    (hreserve:K.reserve=retainedGraph (ordinaryBoundaryGraph (Q\K.cover.rim)
      (fun v u=>H v u∧¬K.cover.spokes v u) X Z) σ)
    (hevent:OrdinaryBoundaryExtensionGood (Q\K.cover.rim)
      (fun v u=>H v u∧¬K.cover.spokes v u) (X\T) βe p σ)
    (hhevent:OrdinaryBoundaryHubPairGood (fun v u=>H v u∧¬K.cover.spokes v u) (Z\W) (βh/2) p σ):
    let A:=Finset.univ\T;let B:=Finset.univ\W;
    let φ:A↪V:=⟨Subtype.val,Subtype.val_injective⟩;
    let ψ:B↪U:=⟨Subtype.val,Subtype.val_injective⟩;
    let Q₀:=Q\K.cover.rim;let H₀:=fun v u=>H v u∧¬K.cover.spokes v u;
    let D:=(ordinaryWheelRimGraph K.packing.wheels).map φ;
    let E:=ordinaryMappedSpokes (ordinaryPackingSpokes K.packing.wheels) φ ψ;
    let Q':=Q₀\D;let H':=fun v u=>H₀ v u∧¬E v u;
    (∀a∉X,∀c∉X,Q'.Adj a c→βh*Fintype.card (V⊕U)≤
      ((Z.filter (fun u=>H₀ a u∧H₀ c u)).card:ℝ))→
    (∀u a c,(p^3*βe/2)*Fintype.card (V⊕U)≤
      ((((X\T).filter (fun v=>H' v u))∩
        Q'.neighborFinset a∩Q'.neighborFinset c).card:ℝ)) ∧
    (∀a∉X,∀c∉X,Q'.Adj a c→(p^2*(βh/2)/2)*Fintype.card (V⊕U)≤
      (((Z\W).filter (fun u=>H' a u∧H' c u)).card:ℝ)):=by
  intro A B φ ψ Q₀ H₀ D E Q' H' hparent
  let C:=ordinaryPhysicalGraph D E
  have hs:=ordinary_root_first_packing_subhost Q F H X T Z W r η ell t K
  have hf:=ordinary_root_first_cleanup_facts Q F H X T Z W r η ell t K ht σ hreserve
  have hres:Disjoint C (retainedGraph (ordinaryBoundaryGraph Q₀ H₀ X Z) σ):=by
    rw [←hreserve]
    exact hs.2.2
  have hkeep:ordinaryPhysicalGraph Q₀ H₀\C≤ordinaryPhysicalGraph Q' H':=le_of_eq hf.1.symm
  have he:=ordinary_retained_subset_extensions_survive_packing Q₀ Q' H₀ H' X (X\T) Z Finset.sdiff_subset C σ
    (p^3*βe*Fintype.card (V⊕U)/2) hs.2.1 hres hkeep hevent
  have hparentfree:∀a∉X,∀c∉X,Q'.Adj a c→(βh/2)*Fintype.card (V⊕U)≤
      (((Z\W).filter (fun u=>H₀ a u∧H₀ c u)).card:ℝ):=by
    intro a ha c hc hac
    have hlost:=ordinary_free_hub_extension_count H₀ Z W a c
    have hold:=hparent a ha c hc hac
    let A₀:=Z.filter (fun u=>H₀ a u∧H₀ c u)
    let A₁:=(Z\W).filter (fun u=>H₀ a u∧H₀ c u)
    have hlost' : (A₀.card:ℝ)≤(A₁.card:ℝ)+W.card:=by
      convert hlost using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
    have hold' : βh*Fintype.card (V⊕U)≤(A₀.card:ℝ):=by
      convert hold using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
    have hfin : (βh/2)*Fintype.card (V⊕U)≤(A₁.card:ℝ):=by
      nlinarith only [hlost',hold',hW]
    convert hfin using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  have hh:=ordinary_retained_hub_subset_choices_survive_packing Q₀ Q' H₀ H' X Z (Z\W) Finset.sdiff_subset C σ
    ((βh/2)*Fintype.card (V⊕U)) (p^2*(βh/2)*Fintype.card (V⊕U)/2) hs.2.1 hres hkeep hhevent (by
      intro a ha c hc hac
      convert hparentfree a ha c hc hac using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
  constructor
  · intro u a c
    have hi:=he u a c
    rw [show (p^3*βe/2)*Fintype.card (V⊕U)=p^3*βe*Fintype.card (V⊕U)/2 by ring]
    convert hi using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  · intro a ha c hc hac
    have hi:=hh a ha c hc hac
    rw [show (p^2*(βh/2)/2)*Fintype.card (V⊕U)=p^2*(βh/2)*Fintype.card (V⊕U)/2 by ring]
    convert hi using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
end Oberwolfach

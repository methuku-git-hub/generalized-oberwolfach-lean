module

public import Oberwolfach.OrdinaryRootFirstCleanupFacts
public import Oberwolfach.OrdinaryCleanupDeepSafeCountsToDataExplicit

@[expose] public section
/-! Complete the sparse deep-avoiding cleanup after the actual lifted
root-first packing, given the two post-packing extension counts. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_root_first_cleanup_given_safe_counts_explicit (r:ℕ) (hr:3≤r) (bV bU ν:ℝ)
    (hbV:0<bV) (hbU:0<bU) (hν:0<ν):
    ∃τ:ℝ,τ=ordinarySparseCleanupScale r bV bU ν/2 ∧ 0<τ ∧ ∀L:ℝ,0≤L→∃N:ℕ,
    ∀(V U:Type) [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U],N≤Fintype.card (V⊕U)→
    ∀(Q F:SimpleGraph V) (H:V→U→Prop) (X T:Finset V) (Z W:Finset U)
      (η ell:ℝ) (σ:Sym2 (V⊕U)→Bool),
    Disjoint Q F→(∀v,(F.degree v:ℝ)≤L)→
    ∀(K:OrdinaryRootFirstPackingContext Q F H X T Z W r η ell (τ*Fintype.card (V⊕U))),
    K.reserve=retainedGraph (ordinaryBoundaryGraph (Q\K.cover.rim)
      (fun v u=>H v u∧¬K.cover.spokes v u) X Z) σ→
    let A:=Finset.univ\T;let B:=Finset.univ\W;
    let φ:A↪V:=⟨Subtype.val,Subtype.val_injective⟩;
    let ψ:B↪U:=⟨Subtype.val,Subtype.val_injective⟩;
    let Q₀:=Q\K.cover.rim;let H₀:=fun v u=>H v u∧¬K.cover.spokes v u;
    let D:=(ordinaryWheelRimGraph K.packing.wheels).map φ;
    let E:=ordinaryMappedSpokes (ordinaryPackingSpokes K.packing.wheels) φ ψ;
    let C:=ordinaryPhysicalGraph D E;
    let Q':=Q₀\D;let H':=fun v u=>H₀ v u∧¬E v u;
    (∀u a c,bV*Fintype.card (V⊕U)≤(((X.filter (fun v=>ordinaryDeepSafeSpokes H' T W v u))∩
      (ordinaryDeepSafeRim Q' T).neighborFinset a∩(ordinaryDeepSafeRim Q' T).neighborFinset c).card:ℝ))→
    (∀a∉X,∀c∉X,Q'.Adj a c→bU*Fintype.card (V⊕U)≤((Z.filter (fun u=>H' a u∧H' c u)).card:ℝ))→
    ∃K':OrdinaryOutsideCleanupData Q' F H' X Z C r (ν*Fintype.card (V⊕U)),
      Disjoint (ordinaryPhysicalGraph (wheelFamilyRim K'.wheels) (wheelFamilySpokes K'.wheels)) (ordinaryDeepBlocker T W):=by
  obtain ⟨τ,hτeq,hτ,hcleanup⟩:=ordinary_cleanup_deep_safe_counts_to_data_explicit r hr bV bU ν hbV hbU hν
  refine ⟨τ,hτeq,hτ,?_⟩
  intro L hL
  obtain ⟨N,hN⟩:=hcleanup L hL
  refine ⟨N,?_⟩
  intro V U _ _ _ _ hn Q F H X T Z W η ell σ hQF hF K hreserve A B φ ψ Q₀ H₀ D E C Q' H' hcount hubs
  have ht:0≤τ*Fintype.card (V⊕U):=mul_nonneg hτ.le (Nat.cast_nonneg _)
  have hfacts:=ordinary_root_first_cleanup_facts Q F H X T Z W r η ell _ K ht σ hreserve
  have hqf:Disjoint Q' F:=hQF.mono_left (show Q'≤Q from sdiff_le.trans sdiff_le)
  exact hN V U hn Q₀ Q' F H₀ H' X T Z W C σ
    K.root_sub (le_of_eq hfacts.1) hqf hF (by
      intro u a c
      convert hcount u a c using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _) (by
      intro a ha c hc hac
      convert hubs a ha c hc hac using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _) hfacts.2
end Oberwolfach

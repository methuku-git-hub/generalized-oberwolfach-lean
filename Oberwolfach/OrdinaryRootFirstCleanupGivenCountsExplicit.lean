module

public import Oberwolfach.OrdinaryRootFirstCleanupFacts
public import Oberwolfach.OrdinaryRootFirstCleanupGivenSafeCountsExplicit
public import Oberwolfach.OrdinaryDeepSafeHost

@[expose] public section
/-! Complete the sparse deep-avoiding cleanup after the actual lifted
root-first packing, given the two post-packing extension counts. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_root_first_cleanup_given_counts_explicit (r:ℕ) (hr:3≤r) (bV bU ν:ℝ)
    (hbV:0<bV) (hbU:0<bU) (hν:0<ν):
    ∃τ:ℝ,τ=ordinarySparseCleanupScale r (bV/2) bU ν/2 ∧ 0<τ ∧ ∀L:ℝ,0≤L→∃N:ℕ,
    ∀(V U:Type) [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U],N≤Fintype.card (V⊕U)→
    ∀(Q F:SimpleGraph V) (H:V→U→Prop) (X T:Finset V) (Z W:Finset U)
      (η ell:ℝ) (σ:Sym2 (V⊕U)→Bool),
    (T.card:ℝ)≤(bV/2)*Fintype.card (V⊕U)→
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
    (∀u a c,bV*Fintype.card (V⊕U)≤(((X.filter (fun v=>H' v u))∩Q'.neighborFinset a∩Q'.neighborFinset c).card:ℝ))→
    (∀a∉X,∀c∉X,Q'.Adj a c→bU*Fintype.card (V⊕U)≤((Z.filter (fun u=>H' a u∧H' c u)).card:ℝ))→
    ∃K':OrdinaryOutsideCleanupData Q' F H' X Z C r (ν*Fintype.card (V⊕U)),
      Disjoint (ordinaryPhysicalGraph (wheelFamilyRim K'.wheels) (wheelFamilySpokes K'.wheels)) (ordinaryDeepBlocker T W):=by
  obtain ⟨τ,hτeq,hτ,hcleanup⟩:=ordinary_root_first_cleanup_given_safe_counts_explicit r hr (bV/2) bU ν (by positivity) hbU hν
  refine ⟨τ,hτeq,hτ,?_⟩
  intro L hL
  obtain ⟨N,hN⟩:=hcleanup L hL
  refine ⟨N,?_⟩
  intro V U _ _ _ _ hn Q F H X T Z W η ell σ hT hQF hF K hreserve A B φ ψ Q₀ H₀ D E C Q' H' hcount hubs
  apply hN V U hn Q F H X T Z W η ell σ hQF hF K hreserve
  · intro u a c
    have hs:=ordinary_deep_safe_extensions Q' H' X T W u a c
    have hh:=hcount u a c
    change (bV/2)*Fintype.card (V⊕U)≤(((X.filter (fun v=>ordinaryDeepSafeSpokes H' T W v u))∩
      (ordinaryDeepSafeRim Q' T).neighborFinset a∩(ordinaryDeepSafeRim Q' T).neighborFinset c).card:ℝ)
    have hs' : (((X.filter (fun v=>H' v u))∩Q'.neighborFinset a∩Q'.neighborFinset c).card:ℝ) ≤
      (((X.filter (fun v=>ordinaryDeepSafeSpokes H' T W v u))∩(ordinaryDeepSafeRim Q' T).neighborFinset a∩(ordinaryDeepSafeRim Q' T).neighborFinset c).card:ℝ)+T.card := by
      convert hs using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
    nlinarith only [hs',hh,hT]
  · exact hubs
end Oberwolfach

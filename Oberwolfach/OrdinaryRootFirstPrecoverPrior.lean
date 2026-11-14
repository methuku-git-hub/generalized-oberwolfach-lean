module

public import Oberwolfach.OrdinaryRootFirstPackingAmbientFacts
public import Oberwolfach.OrdinaryRootFirstCleanupFacts
public import Oberwolfach.OrdinaryBoundaryChangeFromPacking
public import Oberwolfach.OrdinaryInnerFactorSurvival

@[expose] public section
/-! View the root-first packing against the pre-cover boundary: charge
unreserved cover-boundary edges to the prior deletion, so that the prior
still avoids the retained reserve and the inner pair. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

def ordinaryRootFirstPrecoverPrior
    (Q F:SimpleGraph V) (H:V→U→Prop) (X T:Finset V) (Z W:Finset U) (r:ℕ) (η ell t:ℝ)
    (K:OrdinaryRootFirstPackingContext Q F H X T Z W r η ell t) (σ:Sym2 (V⊕U)→Bool):SimpleGraph (V⊕U):=
  let A:=ordinaryPhysicalGraph K.cover.rim K.cover.spokes
  let B:=ordinaryPhysicalGraph (ordinaryRootFirstPackingRim Q F H X T Z W r η ell t K)
    (ordinaryRootFirstPackingSpokes Q F H X T Z W r η ell t K)
  let G:=ordinaryBoundaryGraph Q H X Z
  B⊔((A\retainedGraph G σ)⊓G)

theorem ordinary_root_first_precover_prior
    (Q F:SimpleGraph V) (H:V→U→Prop) (X T:Finset V) (Z W:Finset U) (r:ℕ) (η ell t:ℝ)
    (K:OrdinaryRootFirstPackingContext Q F H X T Z W r η ell t) (ht:0≤t) (σ:Sym2 (V⊕U)→Bool)
    (hreserve:K.reserve=retainedGraph (ordinaryBoundaryGraph (Q\K.cover.rim)
      (fun v u=>H v u∧¬K.cover.spokes v u) X Z) σ):
    let G:=ordinaryBoundaryGraph Q H X Z;
    let R:=retainedGraph G σ;
    let C:=ordinaryRootFirstPrecoverPrior Q F H X T Z W r η ell t K σ;
    Disjoint C R ∧
    Disjoint C (spanningRestriction (ordinaryPhysicalGraph Q H) (ordinaryInnerVertices X Z)) ∧
    (∀w:V⊕U,(((G\R)\C).degree w:ℝ)≤t):=by
  intro G R C
  let A:=ordinaryPhysicalGraph K.cover.rim K.cover.spokes
  let B:=ordinaryPhysicalGraph (ordinaryRootFirstPackingRim Q F H X T Z W r η ell t K)
    (ordinaryRootFirstPackingSpokes Q F H X T Z W r η ell t K)
  let Q₀:=Q\K.cover.rim
  let H₀:=fun v u=>H v u∧¬K.cover.spokes v u
  let G₀:=ordinaryBoundaryGraph Q₀ H₀ X Z
  let R₀:=retainedGraph G₀ σ
  have hs:=ordinary_root_first_packing_subhost Q F H X T Z W r η ell t K
  have ha:=ordinary_root_first_packing_ambient_facts Q F H X T Z W r η ell t K
  have hf:=ordinary_root_first_cleanup_facts Q F H X T Z W r η ell t K ht σ hreserve
  have hBphys:B≤ordinaryPhysicalGraph Q₀ H₀:=by
    apply hs.1.trans
    rw [ordinary_unreserved_physical_graph]
    exact sdiff_le.trans sdiff_le
  have hBreserve:Disjoint B R:=by
    apply disjoint_iff_inf_le.mpr
    intro a b hab
    have hb:=hBphys hab.1
    have hr':=hab.2
    have hg: G.Adj a b:=hr'.1
    have hboundary: G₀.Adj a b:=(ordinaryBoundaryGraph_adj Q₀ H₀ X Z a b).mpr
      ⟨hb,((ordinaryBoundaryGraph_adj Q H X Z a b).mp hg).2⟩
    have hr₀:R₀.Adj a b:=⟨hboundary,hr'.2⟩
    have havoid:Disjoint B R₀:=by
      change Disjoint B (retainedGraph (ordinaryBoundaryGraph (Q\K.cover.rim)
        (fun v u=>H v u∧¬K.cover.spokes v u) X Z) σ)
      rw [←hreserve]
      exact hs.2.2
    exact (disjoint_iff_inf_le.mp havoid) ⟨hab.1,hr₀⟩
  have hCres:Disjoint C R:=by
    apply disjoint_iff_inf_le.mpr
    intro a b hab
    rcases hab.1 with hB|hA
    · exact (disjoint_iff_inf_le.mp hBreserve) ⟨hB,hab.2⟩
    · exact hA.1.2 hab.2
  have hCinner:Disjoint C (spanningRestriction (ordinaryPhysicalGraph Q H) (ordinaryInnerVertices X Z)):=by
    apply disjoint_iff_inf_le.mpr
    intro a b hab
    rcases hab.1 with hB|hA
    · exact (disjoint_iff_inf_le.mp ha.2.2.2.2) ⟨hB,hab.2⟩
    · exact (ordinary_boundary_outside_inner Q H X Z hA.2).2 hab.2
  have hsub:(G\R)\C≤
      ((ordinaryPhysicalGraph Q₀ H₀\spanningRestriction (ordinaryPhysicalGraph Q₀ H₀)
        (ordinaryInnerVertices X Z))\R₀)\B:=by
    intro a b hab
    have hg:G.Adj a b:=hab.1.1
    have hnotR:¬R.Adj a b:=hab.1.2
    have hnotC:¬C.Adj a b:=hab.2
    have hnotA:¬A.Adj a b:=by
      intro hA
      apply hnotC
      exact Or.inr ⟨⟨hA,hnotR⟩,hg⟩
    have hpost:(ordinaryPhysicalGraph Q₀ H₀).Adj a b:=by
      rw [ordinary_physical_graph_typed_deletion]
      exact ⟨((ordinaryBoundaryGraph_adj Q H X Z a b).mp hg).1,hnotA⟩
    have hnotinner:¬(spanningRestriction (ordinaryPhysicalGraph Q₀ H₀) (ordinaryInnerVertices X Z)).Adj a b:=by
      intro hi
      have hh:=(spanningRestriction_adj _ _ _ _).mp hi
      rcases ((ordinaryBoundaryGraph_adj Q H X Z a b).mp hg).2 with h|h
      · exact h.1 hh.2.1
      · exact h.1 hh.2.2
    have hnotR₀:¬R₀.Adj a b:=by
      intro hR₀
      apply hnotR
      have hbd:=(ordinaryBoundaryGraph_adj Q₀ H₀ X Z a b).mp hR₀.1
      exact ⟨(ordinaryBoundaryGraph_adj Q H X Z a b).mpr
        ⟨((ordinaryBoundaryGraph_adj Q H X Z a b).mp hg).1,hbd.2⟩,hR₀.2⟩
    exact ⟨⟨⟨hpost,hnotinner⟩,hnotR₀⟩,fun hB=>hnotC (Or.inl hB)⟩
  refine ⟨hCres,hCinner,?_⟩
  intro w
  have hd:((((G\R)\C).degree w):ℝ)≤
      (((((ordinaryPhysicalGraph Q₀ H₀\spanningRestriction (ordinaryPhysicalGraph Q₀ H₀)
        (ordinaryInnerVertices X Z))\R₀)\B).degree w):ℝ):=by
    exact_mod_cast SimpleGraph.degree_le_of_le hsub (v:=w)
  apply hd.trans
  convert hf.2 w using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
end Oberwolfach

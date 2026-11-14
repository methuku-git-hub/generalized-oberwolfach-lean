module

public import Oberwolfach.OrdinaryRootFirstCleanupOutcome
public import Oberwolfach.OrdinaryRootFirstPackingSubhost
public import Oberwolfach.OrdinaryRootFirstPackingDecomposition
public import Oberwolfach.OrdinaryWheelHostLift

@[expose] public section
/-! The lifted packing is a wheel decomposition in the original host,
avoids the root-cover resources and uses no edge of the enclosing pair. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_root_first_packing_ambient_facts
    (Q F:SimpleGraph V) (H:V→U→Prop) (X T:Finset V) (Z W:Finset U) (r:ℕ) (η ell t:ℝ)
    (K:OrdinaryRootFirstPackingContext Q F H X T Z W r η ell t):
    let R:=ordinaryRootFirstPackingRim Q F H X T Z W r η ell t K;
    let S:=ordinaryRootFirstPackingSpokes Q F H X T Z W r η ell t K;
    HasResourceDecomposition (ordinaryWheelResources (P:=Q) (F:=F) (Hbase:=H) (r:=r)) (ordinaryHostResources R S) ∧
    HasOrdinaryWheelDecomposition R S r ∧
    R≤Q\K.cover.rim ∧ (∀v u,S v u→H v u∧¬K.cover.spokes v u) ∧
    Disjoint (ordinaryPhysicalGraph R S) (spanningRestriction (ordinaryPhysicalGraph Q H) (ordinaryInnerVertices X Z)):=by
  intro R S
  let Q₀:=Q\K.cover.rim
  let H₀:=fun v u=>H v u∧¬K.cover.spokes v u
  have hs:=ordinary_root_first_packing_subhost Q F H X T Z W r η ell t K
  have hphys:ordinaryPhysicalGraph R S≤ordinaryPhysicalGraph Q₀ H₀:=by
    apply hs.1.trans
    rw [ordinary_unreserved_physical_graph]
    exact sdiff_le.trans sdiff_le
  have hR:R≤Q₀:=by intro v w hvw;exact hphys (v:=Sum.inl v) (w:=Sum.inl w) hvw
  have hS:∀v u,S v u→H₀ v u:=by intro v u hvu;exact hphys (v:=Sum.inl v) (w:=Sum.inr u) hvu
  have hp:=ordinary_root_first_packing_decomposition Q F H X T Z W r η ell t K
  have hhost:=ordinary_wheel_host_decomposition_lift (show Q₀≤Q from sdiff_le) (fun _ _ h=>h.1)
    (ordinaryHostResources R S) hp.1
  have hinner:Disjoint (ordinaryPhysicalGraph R S)
      (spanningRestriction (ordinaryPhysicalGraph Q H) (ordinaryInnerVertices X Z)):=by
    apply disjoint_iff_inf_le.mpr
    intro a b hab
    have hsub:=hphys hab.1
    have hins:=(spanningRestriction_adj _ _ _ _).mp hab.2
    have hh:(spanningRestriction (ordinaryPhysicalGraph Q₀ H₀) (ordinaryInnerVertices X Z)).Adj a b:=
      (spanningRestriction_adj _ _ _ _).mpr ⟨hsub,hins.2.1,hins.2.2⟩
    exact (disjoint_iff_inf_le.mp hs.2.1) ⟨hab.1,hh⟩
  exact ⟨hhost,hp.2,hR,hS,hinner⟩
end Oberwolfach

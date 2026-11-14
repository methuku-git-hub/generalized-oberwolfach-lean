module

public import Oberwolfach.OrdinaryOutsideCleanupRootFreeWithMargins
public import Oberwolfach.OrdinaryFreeHubExtensions
public import Oberwolfach.OrdinaryOutsideCleanupWithMargins
public import Oberwolfach.OrdinaryDeepSafeHost

@[expose] public section
/-! Sparse outside cleanup can avoid an entire nested deeper pair.  The
only extra cost in a common-extension count is the number of deeper rim
vertices.  The uncovered outside--outside resources are unchanged. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_outside_cleanup_avoiding_root_star (r:ℕ) (hr:3≤r) (bV bU ν:ℝ)
    (hV:0<bV) (hU:0<bU) (hν:0<ν):
    ∃τ:ℝ,0<τ ∧ ∀(L:ℝ),0≤L→∃N:ℕ,
    ∀(V U:Type) [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U],
      N≤Fintype.card (V⊕U)→∀(Q₀ Q F:SimpleGraph V) (H₀ H:V→U→Prop)
      (X T:Finset V) (Z W:Finset U) (C:SimpleGraph (V⊕U)) (σ:Sym2 (V⊕U)→Bool),
    T⊆X→W⊆Z→(T.card:ℝ)≤(bV/2)*Fintype.card (V⊕U)→
    (W.card:ℝ)≤(bU/2)*Fintype.card (V⊕U)→
    ordinaryPhysicalGraph Q H≤ordinaryPhysicalGraph Q₀ H₀\C→Disjoint Q F→
    (∀v,(F.degree v:ℝ)≤L)→
    (∀u a c,bV*Fintype.card (V⊕U)≤(((X.filter (fun w=>H w u))∩Q.neighborFinset a∩Q.neighborFinset c).card:ℝ))→
    (∀x∉X,∀y∉X,Q.Adj x y→bU*Fintype.card (V⊕U)≤((Z.filter (fun u=>H x u∧H y u)).card:ℝ))→
    (∀w,((((ordinaryPhysicalGraph Q₀ H₀\spanningRestriction (ordinaryPhysicalGraph Q₀ H₀)
      (ordinaryInnerVertices X Z))\retainedGraph (ordinaryBoundaryGraph Q₀ H₀ X Z) σ)\C).degree w:ℝ)≤τ*Fintype.card (V⊕U))→
    ∃(Nr Ns:ℕ) (M:(Fin Nr⊕Fin Ns)→OrdinaryWheel Q F H r),
      (∀i j,i≠j→Disjoint (ordinaryWheelResources (M i)) (ordinaryWheelResources (M j))) ∧
      HasOrdinaryWheelDecomposition (wheelFamilyRim M) (wheelFamilySpokes M) r ∧
      (∀v∉X,∀w∉X,¬(Q\wheelFamilyRim M).Adj v w) ∧
      (∀v∉X,∀u∉Z,¬(H v u∧¬wheelFamilySpokes M v u)) ∧
      (∀w:V⊕U,((ordinaryPhysicalGraph (wheelFamilyRim M) (wheelFamilySpokes M)).degree w:ℝ)≤ν*Fintype.card (V⊕U)) ∧
      Disjoint (ordinaryPhysicalGraph (wheelFamilyRim M) (wheelFamilySpokes M)) C ∧
      Disjoint (ordinaryPhysicalGraph (wheelFamilyRim M) (wheelFamilySpokes M)) (ordinaryDeepRootStar T W) :=by
  obtain ⟨τ,hτ,hcleanup⟩:=ordinary_outside_cleanup_root_free_with_margins r hr (bV/2) (bU/2) ν (by positivity) (by positivity) hν
  refine ⟨τ,hτ,?_⟩
  intro L hL
  obtain ⟨N,hN⟩:=hcleanup L hL
  refine ⟨N,?_⟩
  intro V U _ _ _ _ hn Q₀ Q F H₀ H X T Z W C σ hTX hWZ hT hW hpost hQF hF hcount hubs hdegree
  have hfree:∀u a c,(bV/2)*Fintype.card (V⊕U)≤
      ((((X\T).filter (fun v=>H v u))∩Q.neighborFinset a∩Q.neighborFinset c).card:ℝ):=by
    intro u a c
    have hsurvive:=ordinary_deep_free_extension_count Q H X T u a c
    have horig:=hcount u a c
    linarith only [hsurvive,horig,hT]
  have hfreeHub:∀x∉X,∀y∉X,Q.Adj x y→(bU/2)*Fintype.card (V⊕U)≤
      (((Z\W).filter (fun u=>H x u∧H y u)).card:ℝ):=by
    intro x hx y hy hxy
    have hsurvive:=ordinary_free_hub_extension_count H Z W x y
    have horig:=hubs x hx y hy hxy
    linarith only [hsurvive,horig,hW]
  exact hN V U hn Q₀ Q F H₀ H X T Z W C σ hTX hWZ hpost hQF hF hfree hfreeHub hdegree
end Oberwolfach

module

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

theorem ordinary_outside_cleanup_avoiding_deep (r:ℕ) (hr:3≤r) (bV bU ν:ℝ)
    (hV:0<bV) (hU:0<bU) (hν:0<ν):
    ∃τ:ℝ,0<τ ∧ ∀(L:ℝ),0≤L→∃N:ℕ,
    ∀(V U:Type) [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U],
      N≤Fintype.card (V⊕U)→∀(Q₀ Q F:SimpleGraph V) (H₀ H:V→U→Prop)
      (X T:Finset V) (Z W:Finset U) (C:SimpleGraph (V⊕U)) (σ:Sym2 (V⊕U)→Bool),
    T⊆X→(T.card:ℝ)≤(bV/2)*Fintype.card (V⊕U)→
    ordinaryPhysicalGraph Q H≤ordinaryPhysicalGraph Q₀ H₀\C→Disjoint Q F→
    (∀v,(F.degree v:ℝ)≤L)→
    (∀u a c,bV*Fintype.card (V⊕U)≤(((X.filter (fun w=>H w u))∩Q.neighborFinset a∩Q.neighborFinset c).card:ℝ))→
    (∀x∉X,∀y∉X,Q.Adj x y→bU*Fintype.card (V⊕U)≤((Z.filter (fun u=>H x u∧H y u)).card:ℝ))→
    (∀w,((((ordinaryPhysicalGraph Q₀ H₀\spanningRestriction (ordinaryPhysicalGraph Q₀ H₀)
      (ordinaryInnerVertices X Z))\retainedGraph (ordinaryBoundaryGraph Q₀ H₀ X Z) σ)\C).degree w:ℝ)≤τ*Fintype.card (V⊕U))→
    ∃(Nr Ns:ℕ) (M:(Fin Nr⊕Fin Ns)→OrdinaryWheel (ordinaryDeepSafeRim Q T) F (ordinaryDeepSafeSpokes H T W) r),
      (∀i j,i≠j→Disjoint (ordinaryWheelResources (M i)) (ordinaryWheelResources (M j))) ∧
      HasOrdinaryWheelDecomposition (wheelFamilyRim M) (wheelFamilySpokes M) r ∧
      (∀v∉X,∀w∉X,¬(Q\wheelFamilyRim M).Adj v w) ∧
      (∀v∉X,∀u∉Z,¬(H v u∧¬wheelFamilySpokes M v u)) ∧
      (∀w:V⊕U,((ordinaryPhysicalGraph (wheelFamilyRim M) (wheelFamilySpokes M)).degree w:ℝ)≤ν*Fintype.card (V⊕U)) ∧
      Disjoint (ordinaryPhysicalGraph (wheelFamilyRim M) (wheelFamilySpokes M)) C ∧
      Disjoint (ordinaryPhysicalGraph (wheelFamilyRim M) (wheelFamilySpokes M)) (ordinaryDeepBlocker T W):=by
  obtain ⟨τ,hτ,hcleanup⟩:=ordinary_outside_cleanup_with_margins r hr (bV/2) bU ν (by positivity) hU hν
  refine ⟨τ,hτ,?_⟩
  intro L hL
  obtain ⟨N,hN⟩:=hcleanup L hL
  refine ⟨N,?_⟩
  intro V U _ _ _ _ hn Q₀ Q F H₀ H X T Z W C σ hTX hT hpost hQF hF hcount hubs hdegree
  let Qs:=ordinaryDeepSafeRim Q T
  let Hs:=ordinaryDeepSafeSpokes H T W
  have hsafe:ordinaryPhysicalGraph Qs Hs≤ordinaryPhysicalGraph Q₀ H₀\C:=by
    rw [show ordinaryPhysicalGraph Qs Hs=ordinaryPhysicalGraph Q H\ordinaryDeepBlocker T W from
      ordinary_deep_safe_physical Q H T W]
    exact sdiff_le.trans hpost
  have hdis:Disjoint Qs F:=hQF.mono_left sdiff_le
  have hcounts:∀u a c,(bV/2)*Fintype.card (V⊕U)≤
      (((X.filter (fun w=>Hs w u))∩Qs.neighborFinset a∩Qs.neighborFinset c).card:ℝ):=by
    intro u a c
    have hsurvive:=ordinary_deep_safe_extensions Q H X T W u a c
    have horig:=hcount u a c
    change (((X.filter (fun v=>H v u))∩Q.neighborFinset a∩Q.neighborFinset c).card:ℝ) ≤
      (((X.filter (fun v=>Hs v u))∩Qs.neighborFinset a∩Qs.neighborFinset c).card:ℝ)+T.card at hsurvive
    linarith only [hsurvive,horig,hT]
  have hhubs:∀x∉X,∀y∉X,Qs.Adj x y→bU*Fintype.card (V⊕U)≤
      ((Z.filter (fun u=>Hs x u∧Hs y u)).card:ℝ):=by
    intro x hx y hy hxy
    have he:(Z.filter (fun u=>Hs x u∧Hs y u))=(Z.filter (fun u=>H x u∧H y u)):=by
      apply Finset.filter_congr
      intro u hu
      change ordinaryDeepSafeSpokes H T W x u ∧ ordinaryDeepSafeSpokes H T W y u ↔ H x u ∧ H y u
      rw [ordinary_deep_safe_outside_spoke H X T W hTX x u hx,
        ordinary_deep_safe_outside_spoke H X T W hTX y u hy]
    rw [he]
    exact hubs x hx y hy ((ordinary_deep_safe_outside_rim Q X T hTX x y hx hy).mp hxy)
  obtain ⟨Nr,Ns,M,hpair,hdec,hR,hS,hdeg,hC⟩:=hN V U hn Q₀ Qs F H₀ Hs X Z C σ
    hsafe hdis hF hcounts hhubs hdegree
  have hblock:Disjoint (ordinaryPhysicalGraph (wheelFamilyRim M) (wheelFamilySpokes M)) (ordinaryDeepBlocker T W):=by
    have hsub:=wheelFamily_subhost M
    have hphys:ordinaryPhysicalGraph (wheelFamilyRim M) (wheelFamilySpokes M)≤ordinaryPhysicalGraph Qs Hs:=by
      intro a b hab
      cases a with
      | inl v=>cases b with
        | inl w=>exact hsub.1 hab
        | inr u=>exact hsub.2 v u hab
      | inr u=>cases b with
        | inl v=>exact hsub.2 v u hab
        | inr u'=>exact hab.elim
    apply disjoint_iff_inf_le.mpr
    intro a b hab
    have hs:=hphys hab.1
    rw [show ordinaryPhysicalGraph Qs Hs=ordinaryPhysicalGraph Q H\ordinaryDeepBlocker T W from
      ordinary_deep_safe_physical Q H T W] at hs
    exact hs.2 hab.2
  refine ⟨Nr,Ns,M,hpair,hdec,?_,?_,hdeg,hC,hblock⟩
  · intro v hv w hw h
    exact hR v hv w hw ⟨(ordinary_deep_safe_outside_rim Q X T hTX v w hv hw).mpr h.1,h.2⟩
  · intro v hv u hu h
    exact hS v hv u hu ⟨(ordinary_deep_safe_outside_spoke H X T W hTX v u hv).mpr h.1,h.2⟩
end Oberwolfach

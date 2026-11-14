module

public import Oberwolfach.OrdinaryOutsideCleanupAvoidingDeep
public import Oberwolfach.OrdinaryPackingCleanupData
public import Oberwolfach.OrdinaryWheelGeneralHostInclusion

@[expose] public section
/-! Package deep-avoiding cleanup for any certified physical remainder. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_cleanup_avoiding_deep_to_data (r:ℕ) (hr:3≤r) (bV bU ν:ℝ)
    (hbV:0<bV) (hbU:0<bU) (hν:0<ν):
    ∃τ:ℝ,0<τ ∧ ∀L:ℝ,0≤L→∃N:ℕ,
    ∀(V U:Type) [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U],N≤Fintype.card (V⊕U)→
    ∀(Q₀ Q F:SimpleGraph V) (H₀ H:V→U→Prop) (X T:Finset V) (Z W:Finset U)
      (C:SimpleGraph (V⊕U)) (σ:Sym2 (V⊕U)→Bool),
    T⊆X→(T.card:ℝ)≤(bV/2)*Fintype.card (V⊕U)→
    ordinaryPhysicalGraph Q H≤ordinaryPhysicalGraph Q₀ H₀\C→Disjoint Q F→
    (∀v,(F.degree v:ℝ)≤L)→
    (∀u a c,bV*Fintype.card (V⊕U)≤(((X.filter (fun w=>H w u))∩Q.neighborFinset a∩Q.neighborFinset c).card:ℝ))→
    (∀x∉X,∀y∉X,Q.Adj x y→bU*Fintype.card (V⊕U)≤((Z.filter (fun u=>H x u∧H y u)).card:ℝ))→
    (∀w,((((ordinaryPhysicalGraph Q₀ H₀\spanningRestriction (ordinaryPhysicalGraph Q₀ H₀)
      (ordinaryInnerVertices X Z))\retainedGraph (ordinaryBoundaryGraph Q₀ H₀ X Z) σ)\C).degree w:ℝ)≤τ*Fintype.card (V⊕U))→
    ∃K:OrdinaryOutsideCleanupData Q F H X Z C r (ν*Fintype.card (V⊕U)),
      Disjoint (ordinaryPhysicalGraph (wheelFamilyRim K.wheels) (wheelFamilySpokes K.wheels)) (ordinaryDeepBlocker T W):=by
  obtain ⟨τ,hτ,hcleanup⟩:=ordinary_outside_cleanup_avoiding_deep r hr bV bU ν hbV hbU hν
  refine ⟨τ,hτ,?_⟩
  intro L hL
  obtain ⟨N,hN⟩:=hcleanup L hL
  refine ⟨N,?_⟩
  intro V U _ _ _ _ hn Q₀ Q F H₀ H X T Z W C σ hTX hT hpost hqf hF hcount hubs hleft
  obtain ⟨Nr,Ns,M,hdis,hdec,hNoR,hNoS,hdegree,hdisC,hdeep⟩:=hN V U hn Q₀ Q F H₀ H X T Z W C σ
    hTX hT hpost hqf hF hcount hubs hleft
  let M':(Fin Nr⊕Fin Ns)→OrdinaryWheel Q F H r:=fun i=>
    ordinaryWheelIncludeHost (show ordinaryDeepSafeRim Q T≤Q from sdiff_le) (fun _ _ h=>h.1) (M i)
  have hrim:wheelFamilyRim M'=wheelFamilyRim M:=rfl
  have hspoke:wheelFamilySpokes M'=wheelFamilySpokes M:=rfl
  have hdis':∀i j,i≠j→Disjoint (ordinaryWheelResources (M' i)) (ordinaryWheelResources (M' j)):=by
    intro i j hij
    exact hdis i j hij
  let data:OrdinaryOutsideCleanupData Q F H X Z C r (ν*Fintype.card (V⊕U)) :=
    ⟨Nr,Ns,M',hdis',by simpa only [hrim,hspoke] using hdec,
      by simpa only [hrim] using hNoR,by simpa only [hspoke] using hNoS,
      by intro w;convert hdegree w using 1 <;> congr! 12 <;> exact Subsingleton.elim _ _,by simpa only [hrim,hspoke] using hdisC⟩
  exact ⟨data,by simpa only [data,hrim,hspoke] using hdeep⟩
end Oberwolfach

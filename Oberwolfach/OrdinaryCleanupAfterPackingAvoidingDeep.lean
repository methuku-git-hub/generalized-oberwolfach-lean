module

public import Oberwolfach.OrdinaryPackingPostFacts
public import Oberwolfach.OrdinaryOutsideCleanupAvoidingDeep
public import Oberwolfach.OrdinaryWheelGeneralHostInclusion

@[expose] public section
/-! Apply the sparse outside cleanup to the actual post-packing host, using
its physical remainder certificate. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
set_option synthInstance.maxSize 2048
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_cleanup_after_packing_avoiding_deep (r:ℕ) (hr:3≤r) (bV bU ν:ℝ)
    (hbV:0<bV) (hbU:0<bU) (hν:0<ν):
    ∃τ:ℝ,0<τ ∧ ∀L:ℝ,0≤L→∃N:ℕ,
    ∀(V U:Type) [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U],N≤Fintype.card (V⊕U)→
    ∀(Q F:SimpleGraph V) (H:V→U→Prop) (X T:Finset V) (Z W:Finset U) (σ:Sym2 (V⊕U)→Bool),
    T⊆X→(T.card:ℝ)≤(bV/2)*Fintype.card (V⊕U)→
    Disjoint Q F→(∀v,(F.degree v:ℝ)≤L)→
    let R:=retainedGraph (ordinaryBoundaryGraph Q H X Z) σ;
    ∀(M:OrdinaryUnreservedPackingData Q F H X Z R r (τ*Fintype.card (V⊕U))),
    OrdinaryPackingPostFacts Q F H X Z R r (τ*Fintype.card (V⊕U)) M→
    let Q':=ordinaryPackingPostRim Q F H X Z R r (τ*Fintype.card (V⊕U)) M;
    let H':=ordinaryPackingPostSpokes Q F H X Z R r (τ*Fintype.card (V⊕U)) M;
    let C:=ordinaryPackingUsedGraph Q F H X Z R r (τ*Fintype.card (V⊕U)) M;
    (∀u a c,bV*Fintype.card (V⊕U)≤(((X.filter (fun v=>H' v u))∩Q'.neighborFinset a∩Q'.neighborFinset c).card:ℝ))→
    (∀a∉X,∀c∉X,Q'.Adj a c→bU*Fintype.card (V⊕U)≤((Z.filter (fun u=>H' a u∧H' c u)).card:ℝ))→
    ∃K:OrdinaryOutsideCleanupData Q' F H' X Z C r (ν*Fintype.card (V⊕U)),
      Disjoint (ordinaryPhysicalGraph (wheelFamilyRim K.wheels) (wheelFamilySpokes K.wheels)) (ordinaryDeepBlocker T W):=by
  obtain ⟨τ,hτ,hcleanup⟩:=ordinary_outside_cleanup_avoiding_deep r hr bV bU ν hbV hbU hν
  refine ⟨τ,hτ,?_⟩
  intro L hL
  obtain ⟨N,hN⟩:=hcleanup L hL
  refine ⟨N,?_⟩
  intro V U _ _ _ _ hn Q F H X T Z W σ hTX hT hQF hF R M hpost Q' H' C hcount hubs
  have hqf:Disjoint Q' F:=hQF.mono_left (show Q'≤Q from sdiff_le)
  obtain ⟨Nr,Ns,K,hdis,hdec,hNoR,hNoS,hdegree,hdisC,hdeep⟩:=hN V U hn Q Q' F H H' X T Z W C σ
    hTX hT (le_of_eq hpost.exact_remainder) hqf hF hcount hubs hpost.unreserved_leftover
  let K':(Fin Nr⊕Fin Ns)→OrdinaryWheel Q' F H' r:=fun i=>
    ordinaryWheelIncludeHost (show ordinaryDeepSafeRim Q' T≤Q' from sdiff_le) (fun _ _ h=>h.1) (K i)
  have hrim:wheelFamilyRim K'=wheelFamilyRim K:=rfl
  have hspoke:wheelFamilySpokes K'=wheelFamilySpokes K:=rfl
  have hdis':∀i j,i≠j→Disjoint (ordinaryWheelResources (K' i)) (ordinaryWheelResources (K' j)):=by
    intro i j hij
    exact hdis i j hij
  let data:OrdinaryOutsideCleanupData Q' F H' X Z C r (ν*Fintype.card (V⊕U)) :=
    ⟨Nr,Ns,K',hdis',by simpa only [hrim,hspoke] using hdec,
      by simpa only [hrim] using hNoR,by simpa only [hspoke] using hNoS,
      by intro w;convert hdegree w using 1 <;> congr! 12 <;> exact Subsingleton.elim _ _,by simpa only [hrim,hspoke] using hdisC⟩
  exact ⟨data,by simpa only [data,hrim,hspoke] using hdeep⟩
end Oberwolfach

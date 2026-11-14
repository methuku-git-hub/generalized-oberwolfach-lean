module

public import Oberwolfach.OrdinaryPackingCleanupRootContext
public import Oberwolfach.OrdinaryGeneralRootLevelResult
public import Oberwolfach.OrdinaryFourPieceLevel
public import Oberwolfach.OrdinarySequentialHostDecompositions

@[expose] public section
/-! Assemble the approximate packing, protected cleanup, corrected root cover
and root-free boundary finish into one ordinary level decomposition. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 24000000
set_option synthInstance.maxSize 32768
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_level_from_root_context
    (Q F:SimpleGraph V) (H:V→U→Prop) (X T:Finset V) (Z W:Finset U)
    (R:SimpleGraph (V⊕U)) (m Kcap Dmax:ℕ) (t ν η ell ρ:ℝ)
    (hTX:T⊆X) (hWZ:W⊆Z)
    (hbal:∀v,Q.degree v=2*(Finset.univ.filter (H v)).card)
    (hdiv:∀u,(m+1)∣(Finset.univ.filter (fun v=>H v u)).card)
    (ctx:OrdinaryPackingCleanupRootContext Q F H X T Z W R (m+1) t ν η ell)
    (hcleanup:Disjoint (ordinaryPhysicalGraph (wheelFamilyRim ctx.cleanup.wheels) (wheelFamilySpokes ctx.cleanup.wheels))
      (ordinaryDeepBlocker T W))
    (hfinish:OrdinaryGeneralFinishHostRootClearedResult ctx.postRim F ctx.postSpokes X T Z W m Kcap Dmax ρ):
    OrdinaryGeneralRootLevelResult Q F H X T Z W m Kcap Dmax ν η ρ:=by
  let M:=ctx.packing
  let K:=ctx.cleanup
  let A:=ctx.root
  let R₁:=ordinaryWheelRimGraph M.wheels
  let S₁:=ordinaryPackingSpokes M.wheels
  let C:=ordinaryPackingUsedGraph Q F H X Z R (m+1) t M
  let Q₁:=ordinaryPackingPostRim Q F H X Z R (m+1) t M
  let H₁:=ordinaryPackingPostSpokes Q F H X Z R (m+1) t M
  let R₂:=wheelFamilyRim K.wheels
  let S₂:=wheelFamilySpokes K.wheels
  let Q₂:=ordinaryCleanupPostRim Q₁ F H₁ X Z C (m+1) ν K
  let H₂:=ordinaryCleanupPostSpokes Q₁ F H₁ X Z C (m+1) ν K
  let R₃:=A.rim
  let S₃:=A.spokes
  let Q₃:=Q₂\R₃
  let H₃:=fun v u=>H₂ v u∧¬S₃ v u
  have hm:=ordinary_packing_post_facts Q F H X Z R (m+1) t M hbal hdiv
  have hR₁:R₁≤Q:=(ordinaryWheelRimGraph_subhost M.wheels).trans (by intro v w h;exact h.1.1)
  have hS₁:∀v u,S₁ v u→H v u:=by
    intro v u h
    obtain ⟨A,hA,hu,hv⟩:=h
    have hh:ordinaryUnreservedSpokes H X Z R v u:=by rw [←hu];exact A.property.1 v hv
    exact hh.1
  have hAsub:ordinaryPhysicalGraph R₁ S₁≤ordinaryPhysicalGraph Q H:=by
    intro a b hab
    cases a with
    | inl v=>cases b with
      | inl w=>exact hR₁ hab
      | inr u=>exact hS₁ v u hab
    | inr u=>cases b with
      | inl v=>exact hS₁ v u hab
      | inr u'=>exact hab.elim
  have hQun:ordinaryUnreservedRim Q X R≤Q:=by intro v w h;exact h.1.1
  have hHun:∀v u,ordinaryUnreservedSpokes H X Z R v u→H v u:=by intro v u h;exact h.1
  have hraw₁:HasResourceDecomposition
      (ordinaryWheelResources (P:=ordinaryUnreservedRim Q X R) (F:=F)
        (Hbase:=ordinaryUnreservedSpokes H X Z R) (r:=m+1)) (ordinaryHostResources R₁ S₁):=
    ⟨M.wheels,M.disjoint,ordinaryPacking_resources M.wheels⟩
  have hhost₁:=resource_decomposition_map ordinaryWheelResources ordinaryWheelResources
    (ordinaryWheelToLarger (F:=F) (r:=m+1) hQun hHun) (ordinaryWheelToLarger_resources hQun hHun)
    (ordinaryHostResources R₁ S₁) hraw₁
  have hdec₁:=ordinaryPacking_decomposition M.wheels M.disjoint
  have hQ₁:Q₁≤Q:=sdiff_le
  have hH₁:∀v u,H₁ v u→H v u:=by intro v u h;exact h.1
  have hsub₂:=wheelFamily_subhost K.wheels
  have hhost₂:=resource_decomposition_map ordinaryWheelResources ordinaryWheelResources
    (ordinaryWheelToLarger (F:=F) (r:=m+1) hQ₁ hH₁) (ordinaryWheelToLarger_resources hQ₁ hH₁)
    (ordinaryHostResources R₂ S₂) (wheelFamily_host_decomposition K.wheels K.disjoint)
  have hQ₂:Q₂≤Q:=sdiff_le.trans hQ₁
  have hH₂:∀v u,H₂ v u→H v u:=by intro v u h;exact h.1.1
  have hhost₃:=resource_decomposition_map ordinaryWheelResources ordinaryWheelResources
    (ordinaryWheelToLarger (F:=F) (r:=m+1) hQ₂ hH₂) (ordinaryWheelToLarger_resources hQ₂ hH₂)
    (ordinaryHostResources R₃ S₃) A.host_decomposition
  have hQ₃:Q₃≤Q:=sdiff_le.trans hQ₂
  have hH₃:∀v u,H₃ v u→H v u:=by intro v u h;exact h.1.1.1
  obtain ⟨R₄,S₄,hR₄,hS₄,hhost₄,hdec₄,hnext,hnextS,hnextBal,hnextDiv,hroot,hcost,hstar,hzero⟩:=hfinish
  have hhost₄':=resource_decomposition_map ordinaryWheelResources ordinaryWheelResources
    (ordinaryWheelToLarger (F:=F) (r:=m+1) hQ₃ hH₃) (ordinaryWheelToLarger_resources hQ₃ hH₃)
    (ordinaryHostResources R₄ S₄) hhost₄
  let limit:=2*(ρ*Fintype.card (V⊕U))+((3*(Kcap+Dmax)+Dmax*(m+1):ℕ):ℝ)
  have hfour:=ordinary_four_piece_level Q R₁ R₂ R₃ R₄ F H S₁ S₂ S₃ S₄ X T Z W (m+1) ν η limit
    hTX hWZ hhost₁ hhost₂ hhost₃ hhost₄' hdec₁ K.decomposition A.decomposition hdec₄
    hAsub hsub₂.1 hsub₂.2 A.rim_sub A.spoke_sub hR₄ hS₄ hm.inner_avoided K.degree A.inner_degree hcost
    hcleanup A.avoids_deep hstar
  let Rtotal:=(((R₁⊔R₂)⊔R₃)⊔R₄)
  let Stotal:=fun v u=>((S₁ v u∨S₂ v u)∨S₃ v u)∨S₄ v u
  have hRtotal:Rtotal≤Q:=by
    intro v w hvw
    rcases hvw with ((h₁|h₂)|h₃)|h₄
    · exact hR₁ h₁
    · exact (hsub₂.1 h₂).1
    · exact ((A.rim_sub h₃).1).1
    · exact (((hR₄ h₄).1).1).1
  have hStotal:∀v u,Stotal v u→H v u:=by
    intro v u hvu
    rcases hvu with ((h₁|h₂)|h₃)|h₄
    · exact hS₁ v u h₁
    · exact (hsub₂.2 v u h₂).1
    · exact ((A.spoke_sub v u h₃).1).1
    · exact (((hS₄ v u h₄).1).1).1
  have hQnext:Q\Rtotal=Q₃\R₄:=hfour.2.2.1
  have hHnext:(fun v u=>H v u∧¬Stotal v u)=(fun v u=>H₃ v u∧¬S₄ v u):=hfour.2.2.2.1
  let Inv (G:SimpleGraph V) (J:V→U→Prop):Prop:=
    (∀v,G.degree v=2*(Finset.univ.filter (J v)).card) ∧
    (∀u,(m+1)∣(Finset.univ.filter (fun v=>J v u)).card) ∧
    ordinaryHostResources G J⊆ordinaryRootResources X Z
  have hInv:Inv (Q₃\R₄) (fun v u=>H₃ v u∧¬S₄ v u):=by
    refine ⟨?_,?_,?_⟩
    · intro v;convert hnextBal v using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _
    · intro u;convert hnextDiv u using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _
    · exact hroot
  have hInv':Inv (Q\Rtotal) (fun v u=>H v u∧¬Stotal v u):=by
    rw [hQnext,hHnext]
    exact hInv
  unfold OrdinaryGeneralRootLevelResult
  refine ⟨Rtotal,Stotal,hRtotal,hStotal,hfour.1,hfour.2.1,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [hQnext]
    intro v w hvw
    have hi:=(spanningRestriction_adj Q₃ X v w).mp (hnext hvw)
    exact (spanningRestriction_adj Q X v w).mpr ⟨hQ₃ hi.1,hi.2.1,hi.2.2⟩
  · intro v u hvu
    have hh:H₃ v u∧¬S₄ v u:=(Iff.of_eq (congrFun (congrFun hHnext v) u)).mp hvu
    have hs:=hnextS v u hh
    exact ⟨hH₃ v u hs.1,hs.2.1,hs.2.2⟩
  · intro v;convert hInv'.1 v using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _
  · intro u;convert hInv'.2.1 u using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _
  · exact hInv'.2.2
  · exact hfour.2.2.2.2.1
  · exact hfour.2.2.2.2.2.1
  · exact hfour.2.2.2.2.2.2
end Oberwolfach

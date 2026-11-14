module

public import Oberwolfach.OrdinaryHubFactorTrade

@[expose] public section

/-! Preserve the actual host and forbidden-pair condition when passing
from wheel families to decompositions. Forgetting these conditions is
available only as a separate map to universal wheels. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U I:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
    {Q F:SimpleGraph V} {H:V→U→Prop} {r:ℕ}

 theorem wheelFamily_host_decomposition [Fintype I] (W:I→OrdinaryWheel Q F H r)
    (hW:∀ i j,i≠j→Disjoint (ordinaryWheelResources (W i)) (ordinaryWheelResources (W j))):
    HasResourceDecomposition (ordinaryWheelResources (P:=Q) (F:=F) (Hbase:=H) (r:=r))
      (ordinaryHostResources (wheelFamilyRim W) (wheelFamilySpokes W)):=by
  refine ⟨Finset.univ.image W,?_,?_⟩
  · intro A hA B hB hAB
    obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp hA
    obtain ⟨j,_,rfl⟩:=Finset.mem_image.mp hB
    exact hW i j (fun he=>hAB (congrArg W he))
  · rw [wheelFamily_resources]
    ext e
    simp only [Finset.mem_biUnion,Finset.mem_image,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨C,⟨i,rfl⟩,he⟩;exact ⟨i,he⟩
    · rintro ⟨i,he⟩;exact ⟨W i,⟨i,rfl⟩,he⟩

 theorem ordinary_host_decomposition_forget (L:Finset (Sym2 V⊕(V×U)))
    (h:HasResourceDecomposition (ordinaryWheelResources (P:=Q) (F:=F) (Hbase:=H) (r:=r)) L):
    HasResourceDecomposition (ordinaryWheelResources (P:=(⊤:SimpleGraph V)) (F:=⊥)
      (Hbase:=fun (_:V) (_:U)=>True) (r:=r)) L:=
  resource_decomposition_map ordinaryWheelResources ordinaryWheelResources ordinaryWheelUniversal
    ordinaryWheelUniversal_resources L h

 theorem selected_factor_host_decomposition {T:Finset V}
    (M:Finset (LocalOrdinaryCycle Q F T r)) (A:Finset V) (u:U)
    (hM:∀ C∈M,∀ C'∈M,C≠C'→Disjoint (localOrdinaryVertices C) (localOrdinaryVertices C'))
    (hA:M.biUnion localOrdinaryVertices=A) (hH:∀ v∈A,H v u):
    HasResourceDecomposition (ordinaryWheelResources (P:=Q) (F:=F) (Hbase:=H) (r:=r))
      (ordinaryHostResources (localOrdinaryFactorGraph M) (fun v z=>v∈A∧z=u)):=by
  let j:Unit↪U:=⟨fun _=>u,fun _ _ _=>Subsingleton.elim _ _⟩
  obtain ⟨W,_,hWr,hWs,hdis,_⟩:=selected_hub_factor_wheels Q F H r
    (fun _:Unit=>T) (fun _:Unit=>A) j (fun _:Unit=>M) (fun _=>hM) (fun _=>hA)
    (fun _=>hH) (fun a b h=>False.elim (h (Subsingleton.elim a b)))
  have hrim:wheelFamilyRim W=localOrdinaryFactorGraph M:=hWr.trans (by simp)
  have hspoke:wheelFamilySpokes W=(fun v z=>v∈A∧z=u):=by
    funext v z
    apply propext
    rw [hWs]
    constructor
    · rintro ⟨_,hz,hv⟩;exact ⟨hv,hz.symm⟩
    · rintro ⟨hv,hz⟩;exact ⟨(),hz.symm,hv⟩
  have hh:=wheelFamily_host_decomposition W hdis
  rwa [hrim,hspoke] at hh

 theorem ordinary_hub_factor_host_trade {T:Finset V}
    (A Z:Finset V) (u u':U) (hu:u≠u')
    (M₀ M₁:Finset (LocalOrdinaryCycle Q F T r))
    (h₀:(∀ C∈M₀,∀ D∈M₀,C≠D→Disjoint (localOrdinaryVertices C) (localOrdinaryVertices D))∧
      M₀.biUnion localOrdinaryVertices=A)
    (h₁:(∀ C∈M₁,∀ D∈M₁,C≠D→Disjoint (localOrdinaryVertices C) (localOrdinaryVertices D))∧
      M₁.biUnion localOrdinaryVertices=A∪Z)
    (hdis:Disjoint (localOrdinaryFactorGraph M₀) (localOrdinaryFactorGraph M₁))
    (hH:∀ v∈A∪Z,H v u∧H v u'):
    let R:=localOrdinaryFactorGraph M₁⊔localOrdinaryFactorGraph M₀
    HasResourceDecomposition (ordinaryWheelResources (P:=Q) (F:=F) (Hbase:=H) (r:=r))
      (ordinaryHostResources R (fun v z=>(v∈A∪Z∧z=u)∨(v∈A∧z=u')))∧
    HasResourceDecomposition (ordinaryWheelResources (P:=Q) (F:=F) (Hbase:=H) (r:=r))
      (ordinaryHostResources R (fun v z=>(v∈A∪Z∧z=u')∨(v∈A∧z=u))):=by
  dsimp only
  have h0u:=selected_factor_host_decomposition (H:=H) M₀ A u h₀.1 h₀.2
    (fun v hv=>(hH v (Finset.mem_union_left _ hv)).1)
  have h0u':=selected_factor_host_decomposition (H:=H) M₀ A u' h₀.1 h₀.2
    (fun v hv=>(hH v (Finset.mem_union_left _ hv)).2)
  have h1u:=selected_factor_host_decomposition (H:=H) M₁ (A∪Z) u h₁.1 h₁.2 (fun v hv=>(hH v hv).1)
  have h1u':=selected_factor_host_decomposition (H:=H) M₁ (A∪Z) u' h₁.1 h₁.2 (fun v hv=>(hH v hv).2)
  rw [ordinaryHostResources_union,ordinaryHostResources_union]
  exact ⟨resource_decomposition_union _ _ _ h1u h0u'
    (ordinaryHostResources_disjoint _ _ _ _ hdis.symm (fun _ _ h=>hu (h.1.2.symm.trans h.2.2))),
    resource_decomposition_union _ _ _ h1u' h0u
    (ordinaryHostResources_disjoint _ _ _ _ hdis.symm (fun _ _ h=>hu (h.2.2.symm.trans h.1.2)))⟩

end Oberwolfach

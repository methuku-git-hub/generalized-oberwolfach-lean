module

public import Oberwolfach.OrdinaryComponentToWheel
public import Oberwolfach.ComponentFamilyPartialEmbedding
public import Oberwolfach.PartialEmbeddingInteriorGlue

@[expose] public section
/-! Glue the chosen reserved cycle components to an embedding of their
complement, preserving the component maps and every prescribed edge. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_reserved_components_glue {n r:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (F H:SimpleGraph (Fin n)) (hF:F.IsRegularOfDegree 2)
    (C:Finset F.ConnectedComponent)
    (W:↥C→UniversalOrdinaryWheel (Fin n) U r)
    (hsize:∀c:↥C,Fintype.card c.val=r)
    (hrim:∀c:↥C,ordinaryWheelRim (W c)≤H)
    (hdis:∀a b:↥C,a≠b→Disjoint (ordinaryWheelRim (W a)).support.toFinset
      (ordinaryWheelRim (W b)).support.toFinset)
    (fC:{x:Fin n // F.connectedComponentMk x∉C}↪Fin n)
    (hC:∀x y,(F.induce {x | F.connectedComponentMk x∉C}).Adj x y→H.Adj (fC x) (fC y))
    (havoid:∀(x:{x:Fin n // F.connectedComponentMk x∉C}) (c:↥C),
      fC x∉(ordinaryWheelRim (W c)).support):
    ∃f:Fin n↪Fin n,
      (∀x (hx:F.connectedComponentMk x∉C),f x=fC ⟨x,hx⟩) ∧
      (∀x y,F.Adj x y→H.Adj (f x) (f y)) ∧
      (∀c:↥C,Set.range (fun x:c.val=>f x.val)=(ordinaryWheelRim (W c)).support) ∧
      (∀c:↥C,∀x y:c.val,F.Adj x.val y.val→(ordinaryWheelRim (W c)).Adj (f x.val) (f y.val)) :=by
  have hex:∀c:↥C,∃g:c.val↪Fin n,
      Set.range g=(ordinaryWheelRim (W c)).support ∧
      ∀x y:c.val,c.val.toSimpleGraph.Adj x y↔(ordinaryWheelRim (W c)).Adj (g x) (g y):=
    fun c=>ordinary_component_to_wheel F hF c.val (hsize c) (W c)
  choose g hRange hGraph using hex
  have hGdis:∀a b:↥C,a≠b→Disjoint (Finset.univ.image (g a)) (Finset.univ.image (g b)):=by
    intro a b hab
    apply Finset.disjoint_left.mpr
    intro v hva hvb
    obtain ⟨x,_,rfl⟩:=Finset.mem_image.mp hva
    obtain ⟨y,_,hy⟩:=Finset.mem_image.mp hvb
    have ha:g a x∈(ordinaryWheelRim (W a)).support:=by rw [←hRange a];exact ⟨x,rfl⟩
    have hb:g a x∈(ordinaryWheelRim (W b)).support:=by rw [←hRange b];exact ⟨y,hy⟩
    exact Finset.disjoint_left.mp (hdis a b hab) (by simpa using ha) (by simpa using hb)
  obtain ⟨ψ,hψ⟩:=component_family_partial_embedding F (fun c:↥C=>c.val) Subtype.val_injective g hGdis
  let D:Finset (Fin n):=Finset.univ.filter (fun x=>F.connectedComponentMk x∈C)
  have hdom:∀x:Fin n,x∈D↔∃c:↥C,x∈c.val.supp:=by
    intro x
    simp only [D,Finset.mem_filter,Finset.mem_univ,true_and,SimpleGraph.ConnectedComponent.mem_supp_iff]
    constructor
    · intro hx;exact ⟨⟨F.connectedComponentMk x,hx⟩,rfl⟩
    · rintro ⟨c,hc⟩;rw [hc];exact c.property
  let fA:{x:Fin n // x∈D}↪Fin n:=⟨fun x=>ψ ⟨x.val,(hdom x.val).1 x.property⟩,by
    intro x y h
    have hh:=ψ.injective h
    exact Subtype.ext (congrArg (fun z:{v:Fin n // ∃c:↥C,v∈c.val.supp}=>z.val) hh)⟩
  let fC':{x:Fin n // x∉D}↪Fin n:=⟨fun x=>fC ⟨x.val,by simpa [D] using x.property⟩,by
    intro x y h
    have hh:=fC.injective h
    exact Subtype.ext (congrArg (fun z:{v:Fin n // F.connectedComponentMk v∉C}=>z.val) hh)⟩
  have hAmap:∀c:↥C,∀x:c.val,fA ⟨x.val,(hdom x.val).2 ⟨c,x.property⟩⟩=g c x:=by
    intro c x
    change ψ ⟨x.val,(hdom x.val).1 ((hdom x.val).2 ⟨c,x.property⟩)⟩=g c x
    simpa using hψ c x
  have hA:∀x y (hx:x∈D) (hy:y∈D),F.Adj x y→H.Adj (fA ⟨x,hx⟩) (fA ⟨y,hy⟩):=by
    intro x y hx hy hxy
    let c:↥C:=⟨F.connectedComponentMk x,by simpa [D] using hx⟩
    have hxC:x∈c.val.supp:=by simp [c]
    have hyC:y∈c.val.supp:=by
      change F.connectedComponentMk y=F.connectedComponentMk x
      exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hxy).symm
    have hxMap:fA ⟨x,hx⟩=g c ⟨x,hxC⟩:=by simpa using hAmap c ⟨x,hxC⟩
    have hyMap:fA ⟨y,hy⟩=g c ⟨y,hyC⟩:=by simpa using hAmap c ⟨y,hyC⟩
    rw [hxMap,hyMap]
    apply hrim c
    exact (hGraph c ⟨x,hxC⟩ ⟨y,hyC⟩).1 hxy
  have hdisAC:∀x (hx:x∈D) y (hy:y∉D),fA ⟨x,hx⟩≠fC' ⟨y,hy⟩:=by
    intro x hx y hy heq
    obtain ⟨c,hxc⟩:=(hdom x).1 hx
    have hxmap:fA ⟨x,hx⟩=g c ⟨x,hxc⟩:=by simpa using hAmap c ⟨x,hxc⟩
    have hm:g c ⟨x,hxc⟩∈(ordinaryWheelRim (W c)).support:=by
      rw [←hRange c];exact ⟨⟨x,hxc⟩,rfl⟩
    rw [←hxmap,heq] at hm
    exact havoid ⟨y,by simpa [D] using hy⟩ c hm
  have hneigh:∀x,x∈D→∀y,F.Adj x y→y∈D:=by
    intro x hx y hxy
    have heq:F.connectedComponentMk y=F.connectedComponentMk x:=(SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hxy).symm
    simpa [D,heq] using hx
  obtain ⟨f,hOn,hOff,hEdges⟩:=partial_embeddings_glue_across_interior F H D D (by rfl) fA fC' hA
    (by intro x y hx hy hxy;exact hC ⟨x,by simpa [D] using hx⟩ ⟨y,by simpa [D] using hy⟩ hxy)
    (by intro x hx hxnot;exact False.elim (hxnot hx)) hdisAC hneigh
  refine ⟨f,?_,hEdges,?_,?_⟩
  · intro x hx
    exact hOff x (by simpa [D] using hx)
  · intro c
    have heq:∀x:c.val,f x.val=g c x:=by
      intro x
      have hx:x.val∈D:=(hdom x.val).2 ⟨c,x.property⟩
      rw [hOn x.val hx]
      simpa using hAmap c x
    ext v
    simp only [Set.mem_range]
    constructor
    · rintro ⟨x,rfl⟩
      rw [heq]
      rw [←hRange c]
      exact ⟨x,rfl⟩
    · intro hv
      rw [←hRange c] at hv
      obtain ⟨x,rfl⟩:=hv
      exact ⟨x,heq x⟩
  · intro c x y hxy
    have hx:x.val∈D:=(hdom x.val).2 ⟨c,x.property⟩
    have hy:y.val∈D:=(hdom y.val).2 ⟨c,y.property⟩
    rw [hOn x.val hx,hOn y.val hy]
    have hxm:fA ⟨x.val,hx⟩=g c x:=by simpa using hAmap c x
    have hym:fA ⟨y.val,hy⟩=g c y:=by simpa using hAmap c y
    rw [hxm,hym]
    exact (hGraph c x y).1 hxy
end Oberwolfach

module

public import Oberwolfach.RootSeparatedFactorsPhysical

@[expose] public section
/-! Lift a rooted factor pair from an induced domain to the ambient graph,
keeping the original roots and all physical rim edges. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem root_separated_factors_ambient {V:Type} [Fintype V] [DecidableEq V]
    (G F:SimpleGraph V) (B T:Finset V) (hTB:T⊆B) (r k:ℕ)
    (hpair:ConflictFreeRootSeparatedCycleFactorPair (G.induce (B:Set V)) (F.induce (B:Set V))
      (T.subtype (fun v=>v∈B)) r k):
    ∃ S:Finset V,S⊆B ∧ S.card=k ∧ Disjoint S T ∧
      (∀ x∈S∪T,∀ y∈S∪T,¬F.Adj x y) ∧
      ∃ M₁ M₂:Finset (OrdinaryCycle G r),
        (∀ C∈M₁,∀ E∈M₁,C≠E→Disjoint (ordinaryCycleVertices G r C) (ordinaryCycleVertices G r E)) ∧
        M₁.biUnion (ordinaryCycleVertices G r)=S∪T ∧
        (∀ C∈M₂,∀ E∈M₂,C≠E→Disjoint (ordinaryCycleVertices G r C) (ordinaryCycleVertices G r E)) ∧
        M₂.biUnion (ordinaryCycleVertices G r)=S ∧
        (∀ C∈M₁,∀ E∈M₂,Disjoint C.val.val.edgeFinset E.val.val.edgeFinset) ∧
        (∀ C∈M₁,(ordinaryCycleVertices G r C∩T).card≤1):=by
  let W:Type:={v:V // v∈B}
  let Q:SimpleGraph W:=G.induce (B:Set V)
  let F':SimpleGraph W:=F.induce (B:Set V)
  let T':Finset W:=T.subtype (fun v=>v∈B)
  obtain ⟨S',hSc,hdis,hfree,M₁,M₂,hpack₁,hcover₁,hpack₂,hcover₂,hedge,hroot⟩:=
    root_separated_factors_physical Q F' T' r k hpair
  let f:W↪V:=Function.Embedding.subtype _
  let S:=S'.image f
  have hSsub:S⊆B:=by
    intro x hx;obtain ⟨x',_,rfl⟩:=Finset.mem_image.mp hx;exact x'.property
  have hScard:S.card=k:=by dsimp [S];rw [Finset.card_image_of_injective _ f.injective,hSc]
  have hTmap:T'.image f=T:=by
    ext v
    constructor
    · intro hv;obtain ⟨x,hx,rfl⟩:=Finset.mem_image.mp hv;exact Finset.mem_subtype.mp hx
    · intro hv;exact Finset.mem_image.mpr ⟨⟨v,hTB hv⟩,Finset.mem_subtype.mpr hv,rfl⟩
  have hSTdis:Disjoint S T:=by
    rw [←hTmap]
    exact (Finset.disjoint_image f.injective).mpr hdis
  have hfree':∀ x∈S∪T,∀ y∈S∪T,¬F.Adj x y:=by
    intro x hx y hy hxy
    have hxmap:x∈(S'∪T').image f:=by simpa [Finset.image_union,hTmap,S] using hx
    have hymap:y∈(S'∪T').image f:=by simpa [Finset.image_union,hTmap,S] using hy
    obtain ⟨x',hx',rfl⟩:=Finset.mem_image.mp hxmap
    obtain ⟨y',hy',rfl⟩:=Finset.mem_image.mp hymap
    exact hfree x' hx' y' hy' hxy
  have hQ:Q.map f≤G:=by
    intro v w h
    rw [SimpleGraph.map_adj] at h
    obtain ⟨a,b,hab,rfl,rfl⟩:=h
    exact hab
  let lift:=ordinaryCycleLift (r:=r) f hQ
  let M₁':=M₁.image lift
  let M₂':=M₂.image lift
  have hp₁:=ordinary_cycle_family_lift f hQ M₁ hpack₁
  have hp₂:=ordinary_cycle_family_lift f hQ M₂ hpack₂
  have hcover₁':M₁'.biUnion (ordinaryCycleVertices G r)=S∪T:=by
    change (M₁.image lift).biUnion (ordinaryCycleVertices G r)=S∪T
    rw [hp₁.2,hcover₁,Finset.image_union,hTmap]
  have hcover₂':M₂'.biUnion (ordinaryCycleVertices G r)=S:=by
    change (M₂.image lift).biUnion (ordinaryCycleVertices G r)=S
    rw [hp₂.2,hcover₂]
  refine ⟨S,hSsub,hScard,hSTdis,hfree',M₁',M₂',hp₁.1,hcover₁',hp₂.1,hcover₂',?_,?_⟩
  · intro C hC E hE
    obtain ⟨C',hC',hCC⟩:=Finset.mem_image.mp hC
    obtain ⟨E',hE',hEE⟩:=Finset.mem_image.mp hE
    subst C;subst E
    exact ordinaryCycleLift_disjoint_edges f hQ C' E' (hedge C' hC' E' hE')
  · intro C hC
    obtain ⟨C',hC',hCC⟩:=Finset.mem_image.mp hC
    subst C
    apply Finset.card_le_one.mpr
    intro x hx y hy
    have hx':=Finset.mem_inter.mp hx
    have hy':=Finset.mem_inter.mp hy
    rw [ordinaryCycleLift_vertices] at hx' hy'
    obtain ⟨x',hx'C,hx⟩:=Finset.mem_image.mp hx'.1
    obtain ⟨y',hy'C,hy⟩:=Finset.mem_image.mp hy'.1
    have hxT:x'∈T':=by
      apply Finset.mem_subtype.mpr
      change f x'∈T
      rw [hx]
      exact hx'.2
    have hyT:y'∈T':=by
      apply Finset.mem_subtype.mpr
      change f y'∈T
      rw [hy]
      exact hy'.2
    have hxy:x'=y':=Finset.card_le_one.mp (hroot C' hC') x'
      (Finset.mem_inter.mpr ⟨hx'C,hxT⟩) y' (Finset.mem_inter.mpr ⟨hy'C,hyT⟩)
    calc
      x=f x':=hx.symm
      _=f y':=congrArg f hxy
      _=y:=hy
end Oberwolfach

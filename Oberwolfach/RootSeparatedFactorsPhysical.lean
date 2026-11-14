module

public import Oberwolfach.CommonNeighborhoodConflictFreeFactors

@[expose] public section
/-! Translate the induced-subgraph factor pair to cycles in the original
physical graph, preserving root counts and conflict avoidance. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem root_separated_factors_physical {V:Type} [Fintype V] [DecidableEq V]
    (G F:SimpleGraph V) (T:Finset V) (r k:ℕ)
    (hpair:ConflictFreeRootSeparatedCycleFactorPair G F T r k):
    ∃ S:Finset V,S.card=k ∧ Disjoint S T ∧
      (∀ x∈S∪T,∀ y∈S∪T,¬F.Adj x y) ∧
      ∃ M₁ M₂:Finset (OrdinaryCycle G r),
        (∀ C∈M₁,∀ E∈M₁,C≠E→Disjoint (ordinaryCycleVertices G r C) (ordinaryCycleVertices G r E)) ∧
        M₁.biUnion (ordinaryCycleVertices G r)=S∪T ∧
        (∀ C∈M₂,∀ E∈M₂,C≠E→Disjoint (ordinaryCycleVertices G r C) (ordinaryCycleVertices G r E)) ∧
        M₂.biUnion (ordinaryCycleVertices G r)=S ∧
        (∀ C∈M₁,∀ E∈M₂,Disjoint C.val.val.edgeFinset E.val.val.edgeFinset) ∧
        (∀ C∈M₁,(ordinaryCycleVertices G r C∩T).card≤1):=by
  obtain ⟨S,hSc,hdis,hfree,M₁,M₂,hpack₁,hcover₁,hpack₂,hcover₂,hedge,hroot⟩:=hpair
  let R:=S∪T
  let W:Type:={v:V // v∈R}
  let J:SimpleGraph W:=G.induce (R:Set V)
  let S':Finset W:=S.subtype (fun v=>v∈R)
  let f:W↪V:=Function.Embedding.subtype _
  have hQ:J.map f≤G:=by
    intro v w h
    rw [SimpleGraph.map_adj] at h
    obtain ⟨a,b,hab,rfl,rfl⟩:=h
    exact hab
  let lift:=ordinaryCycleLift (r:=r) f hQ
  let M₁':=M₁.image lift
  let M₂':=M₂.image lift
  have hp₁:=ordinary_cycle_family_lift f hQ M₁ hpack₁
  have hp₂:=ordinary_cycle_family_lift f hQ M₂ hpack₂
  have huniv:(Finset.univ:Finset W).image f=R:=by
    ext v
    constructor
    · intro hv;obtain ⟨x,_,rfl⟩:=Finset.mem_image.mp hv;exact x.property
    · intro hv;exact Finset.mem_image.mpr ⟨⟨v,hv⟩,Finset.mem_univ _,rfl⟩
  have hSmap:S'.image f=S:=by
    ext v
    constructor
    · intro hv
      obtain ⟨x,hx,rfl⟩:=Finset.mem_image.mp hv
      exact Finset.mem_subtype.mp hx
    · intro hv
      have hvR:v∈R:=Finset.mem_union_left _ hv
      exact Finset.mem_image.mpr ⟨⟨v,hvR⟩,Finset.mem_subtype.mpr hv,rfl⟩
  have hcover₁':M₁'.biUnion (ordinaryCycleVertices G r)=S∪T:=by
    change (M₁.image lift).biUnion (ordinaryCycleVertices G r)=R
    rw [hp₁.2,hcover₁,huniv]
  have hcover₂':M₂'.biUnion (ordinaryCycleVertices G r)=S:=by
    change (M₂.image lift).biUnion (ordinaryCycleVertices G r)=S
    rw [hp₂.2,hcover₂,hSmap]
  refine ⟨S,hSc,hdis,hfree,M₁',M₂',hp₁.1,hcover₁',hp₂.1,hcover₂',?_,?_⟩
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
    have hxS':x'∉S':=by
      intro h
      have hxS:(f x')∈S:=Finset.mem_subtype.mp h
      have hxT:(f x')∈T:=by simpa [hx] using hx'.2
      exact (Finset.disjoint_left.mp hdis) hxS hxT
    have hyS':y'∉S':=by
      intro h
      have hyS:(f y')∈S:=Finset.mem_subtype.mp h
      have hyT:(f y')∈T:=by simpa [hy] using hy'.2
      exact (Finset.disjoint_left.mp hdis) hyS hyT
    have hxmem:x'∈ordinaryCycleVertices J r C'∩(Finset.univ\S'):=
      Finset.mem_inter.mpr ⟨hx'C,Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hxS'⟩⟩
    have hymem:y'∈ordinaryCycleVertices J r C'∩(Finset.univ\S'):=
      Finset.mem_inter.mpr ⟨hy'C,Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hyS'⟩⟩
    have hxy: x'=y':=Finset.card_le_one.mp (hroot C' hC') x' hxmem y' hymem
    calc
      x=f x':=hx.symm
      _=f y':=congrArg f hxy
      _=y:=hy
end Oberwolfach

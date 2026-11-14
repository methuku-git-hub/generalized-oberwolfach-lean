module

public import Oberwolfach.PrescribedFamilyRestrictedEmbeddingOrderedPieces
public import Oberwolfach.PrescribedDependentRestrictedFreeLoad
public import Oberwolfach.PrescribedFamilyEmbeddingOrderedPieces
public import Oberwolfach.PrescribedDependentInitialEdges
public import Oberwolfach.PrescribedDependentFreeLoad
public import Oberwolfach.PrescribedDependentFullEdges

@[expose] public section
/-! The prescribed-image embedding theorem for a family of separately typed
source factors, each specified by vertex-disjoint ordered paths and cycles. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I V:Type} [Fintype I] [Fintype V] [DecidableEq I] [DecidableEq V]
  {X:I→Type} [∀ i,Fintype (X i)] [∀ i,DecidableEq (X i)]

theorem prescribed_dependent_family_restricted_embedding
    (pieces:∀ i,List (PrescribedSourcePiece (X i)))
    (hshape:∀ i p,p∈pieces i→p.Shape)
    (hapart:∀ i,(pieces i).Pairwise (fun p q=>Disjoint p.vertices.toFinset q.vertices.toFinset))
    (A:∀ i,Finset (X i)) (ψ:∀ i,X i→V) (J:SimpleGraph V)
    (β δ:ℝ) (hβ:0<β) (hβ1:β≤1) (hδ:0<δ) (hδbound:δ≤(β/100)^2)
    (hnβ:100/β≤(Fintype.card V:ℝ)) (hn:2/Real.sqrt δ≤(Fintype.card V:ℝ))
    (hI:(Fintype.card I:ℝ)≤Fintype.card V)
    (hsize:∀ i,((prescribedDependentVertices pieces i).card:ℝ)≤δ*Fintype.card V)
    (hold:∀ v,((Finset.univ.filter (fun i=>∃ x,x∈A i ∧ ψ i x=v)).card:ℝ)≤δ*Fintype.card V)
    (hJ:∀ v,(J.degree v:ℝ)≤δ*Fintype.card V)
    (hinj:∀ i,Set.InjOn (ψ i) (↑(A i):Set (X i))) (hA:∀ i,A i⊆prescribedDependentVertices pieces i)
    (hpair:PairwisePhysicalDisjoint (prescribedDependentInitialEdges pieces A ψ))
    (D Dstar:V→V→Prop) (hDD:∀ x y,D x y→Dstar x y)
    (hpresArc:∀ i x y,prescribedDependentDigraph pieces i x y→x∈A i→y∈A i→Dstar (ψ i x) (ψ i y))
    (L:I→Finset V) (hext:∀ i,IsExtendingList D (L i) β)
    (H:Finset I) (aScale κ θ:ℝ) (haScale:0<aScale) (hκ:0<κ) (hθ:0≤θ)
    (hH:(H.card:ℝ)≤aScale) (hθbudget:θ≤κ*(β/4))
    (hQlocal:∀i∈H,((prescribedDependentVertices pieces i).card:ℝ)≤θ*Fintype.card V)
    (hδstrong:δ≤(β/200)^2) (hnstrong:200/β≤(Fintype.card V:ℝ)):
    ∃ Φ:∀ i,X i→V,
      (∀ i,Set.InjOn (Φ i) (↑(prescribedDependentVertices pieces i):Set (X i))) ∧
      (∀ i x,x∈A i→Φ i x=ψ i x) ∧
      (∀ i x,x∈prescribedDependentVertices pieces i→x∉A i→Φ i x∈L i) ∧
      (∀ i x y,prescribedDependentDigraph pieces i x y→Dstar (Φ i x) (Φ i y) ∧
        ((x∉A i ∨ y∉A i)→D (Φ i x) (Φ i y))) ∧
      let E:I→Finset (Sym2 V):=fun i=>((prescribedDependentGraph pieces i).edgeFinset).image (Sym2.map (Φ i));
      PairwisePhysicalDisjoint E ∧
      (∀ i,Disjoint (E i\prescribedDependentInitialEdges pieces A ψ i) J.edgeFinset) ∧
      (∀ v,(((prescribedDependentFreeVertices pieces A).filter (fun z=>Φ z.1 z.2=v)).card:ℝ)≤Real.sqrt δ*Fintype.card V+1) ∧
      (prescribedPhysicalUnion E).edgeFinset=Finset.univ.biUnion E ∧
      (∀ v,((prescribedPhysicalUnion E).degree v:ℝ)≤5*Real.sqrt δ*Fintype.card V) ∧
      (∀v,((((prescribedDependentFreeVertices pieces A).filter (fun z=>z.1∈H)).filter
        (fun z=>Φ z.1 z.2=v)).card:ℝ)≤κ*aScale+1) := by
  have hnposR:0<(Fintype.card V:ℝ):=lt_of_lt_of_le (div_pos (by norm_num) hβ) hnβ
  have hnpos:0<Fintype.card V:=by exact_mod_cast hnposR
  obtain ⟨v₀⟩:=Fintype.card_pos_iff.mp hnpos
  let ps:=prescribedLiftDependentPieces Finset.univ.toList pieces
  let A':I→Finset (Σ i,X i):=prescribedLiftedSet A
  let ψ':I→(Σ i,X i)→V:=prescribedLiftedMap v₀ ψ
  let E₀:I→Finset (Sym2 V):=prescribedDependentInitialEdges pieces A ψ
  have hshape':∀ p∈ps,p.2.Shape:=prescribed_lifted_pieces_shape pieces hshape _
  have hapart':ps.Pairwise PrescribedPiecesApart:=prescribed_lifted_pieces_apart pieces hapart _ (Finset.nodup_toList (Finset.univ:Finset I))
  have hsize':∀ i,((prescribedSourceVertices ps i).card:ℝ)≤δ*Fintype.card V:=by
    intro i;rw [prescribed_lifted_source_vertex_card];exact hsize i
  have hQlocal':∀i∈H,((prescribedSourceVertices ps i).card:ℝ)≤θ*Fintype.card V:=by
    intro i hi
    rw [prescribed_lifted_source_vertex_card]
    exact hQlocal i hi
  have hold':∀ v,((Finset.univ.filter (fun i=>∃ z,z∈A' i ∧ ψ' i z=v)).card:ℝ)≤δ*Fintype.card V:=by
    intro v;rw [prescribed_lifted_occurrence_bound];exact hold v
  have hinj':FamilyPartialInjections A' ψ':=prescribed_lifted_maps_injective v₀ A ψ hinj
  have hA':∀ i,A' i⊆prescribedSourceVertices ps i:=by
    intro i z hz
    obtain ⟨x,hx,rfl⟩:=Finset.mem_image.mp hz
    exact (prescribed_lifted_source_vertex_membership pieces i x).mpr (hA i hx)
  have hE₀:∀ i,E₀ i=(prescribedInducedSourceEdges (prescribedSourceGraph ps i) (A' i)).image (Sym2.map (ψ' i)):=by
    intro i;exact (prescribed_lifted_initial_edges pieces A ψ v₀ i).symm
  have hpres':∀ i z w,prescribedSourceDigraph ps i z w→z∈A' i→w∈A' i→Dstar (ψ' i z) (ψ' i w):=by
    intro i z w harc hz hw
    obtain ⟨x,hx,rfl⟩:=Finset.mem_image.mp hz
    obtain ⟨y,hy,rfl⟩:=Finset.mem_image.mp hw
    have ha:prescribedDependentDigraph pieces i x y:=(prescribed_lifted_source_arc_membership pieces i x y).mp harc
    simpa [ψ'] using hpresArc i x y ha hx hy
  obtain ⟨st,hvalid,hassigned,hsource,hinjG,hpresG,hLG,harcsG,hEG,hpairG,hJG,hloadG,hunionG,hdegreeG,hrestrictedG⟩:=
    prescribed_family_restricted_embedding_from_ordered_pieces ps hshape' hapart' A' ψ' E₀ J β δ hβ hβ1 hδ hδbound
      hnβ hn hI hsize' hold' hJ hinj' hA' hE₀ hpair D Dstar hDD hpres' L hext H aScale κ θ haScale hκ hθ hH hθbudget hQlocal' hδstrong hnstrong
  let Φ:∀ i,X i→V:=fun i x=>st.vertexMap i (Sigma.mk i x)
  have hE:∀ i,st.physicalEdges i=((prescribedDependentGraph pieces i).edgeFinset).image (Sym2.map (Φ i)):=by
    intro i
    rw [hEG i,prescribed_lifted_full_edge_images]
  have hEfun:st.physicalEdges=(fun i=>((prescribedDependentGraph pieces i).edgeFinset).image (Sym2.map (Φ i))):=funext hE
  have hload:=prescribed_dependent_free_load_transfer pieces A st.vertexMap (Real.sqrt δ*Fintype.card V+1) hloadG
  have hRestricted:=prescribed_dependent_restricted_free_load_transfer pieces A st.vertexMap H (κ*aScale+1) hrestrictedG
  rw [hEfun] at hpairG hJG hunionG hdegreeG
  refine ⟨Φ,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro i x hx y hy he
    have hx':Sigma.mk i x∈prescribedSourceVertices ps i:=(prescribed_lifted_source_vertex_membership pieces i x).mpr hx
    have hy':Sigma.mk i y∈prescribedSourceVertices ps i:=(prescribed_lifted_source_vertex_membership pieces i y).mpr hy
    exact sigma_mk_injective (hinjG i hx' hy' he)
  · intro i x hx
    have hx':Sigma.mk i x∈A' i:=(prescribed_lifted_set_membership A i x).mpr hx
    simpa [Φ,ψ'] using hpresG i (Sigma.mk i x) hx'
  · intro i x hx hnot
    have hx':Sigma.mk i x∈prescribedSourceVertices ps i:=(prescribed_lifted_source_vertex_membership pieces i x).mpr hx
    have hnot':Sigma.mk i x∉A' i:=by intro h;exact hnot ((prescribed_lifted_set_membership A i x).mp h)
    exact hLG i (Sigma.mk i x) hx' hnot'
  · intro i x y hxy
    have hxy':prescribedSourceDigraph ps i (Sigma.mk i x) (Sigma.mk i y):=
      (prescribed_lifted_source_arc_membership pieces i x y).mpr hxy
    have hh:=harcsG i (Sigma.mk i x) (Sigma.mk i y) hxy'
    constructor
    · exact hh.1
    · intro hnot
      apply hh.2
      rcases hnot with hx|hy
      · left;intro h;exact hx ((prescribed_lifted_set_membership A i x).mp h)
      · right;intro h;exact hy ((prescribed_lifted_set_membership A i y).mp h)
  · exact hpairG
  · exact hJG
  · simpa [Φ] using hload
  · exact hunionG
  · exact hdegreeG
  · simpa [Φ] using hRestricted
end Oberwolfach

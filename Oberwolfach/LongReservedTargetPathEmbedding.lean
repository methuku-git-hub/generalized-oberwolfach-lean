module

public import Oberwolfach.LongReservedPrescribedSubwalks
public import Oberwolfach.BufferedPathFamilyTargetEmbedding

@[expose] public section
/-! Reserve the manuscript's source paths and map them to any matching
family of vertex-disjoint target paths. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_reserved_paths_to_disjoint_target_paths
    {V I J:Type*} [Fintype V] [DecidableEq V] [Fintype I] [Fintype J]
    (G:SimpleGraph V) (hG:G.IsRegularOfDegree 2)
    (components:I↪G.ConnectedComponent)
    (e:∀i:I,SimpleGraph.cycleGraph (Fintype.card (components i)) ≃g (components i).toSimpleGraph)
    (c d:ℕ) (t:J→ℕ) (ht:∀a,t a≤d)
    (hcapacity:Fintype.card J≤∑i:I,Fintype.card (components i)/(c*d+5)):
    ∃index:J↪LongReservedBlockIndex G components c d,
    ∃ext:∀a:J,Fin (c*t a+5)↪V,
    ∃inner:∀a:J,Fin (c*t a+1)↪V,
      (∀a,ext a=longReservedSigmaBlock G components c d e (index a) (t a) (ht a)) ∧
      (∀(a:J) (j:Fin (c*t a+1)),inner a j=ext a ⟨j.val+2,by omega⟩) ∧
      (∀a j,ext a j∈(components (index a).1).supp) ∧
      (∀a b:J,a≠b→Disjoint (Finset.univ.image (ext a)) (Finset.univ.image (ext b))) ∧
      (∀a:J,∃p:G.Walk (inner a ⟨0,by omega⟩) (inner a ⟨c*t a,by omega⟩),
        p.IsPath ∧ p.length=c*t a ∧ p.support=List.ofFn (inner a) ∧
        ∃q:G.Walk (ext a ⟨0,by omega⟩) (ext a ⟨c*t a+4,by omega⟩),
          q.IsPath ∧ q.length=c*t a+4 ∧ q.support=List.ofFn (ext a) ∧ p.IsSubwalk q) ∧
      ∀(W:Type) (H:SimpleGraph W) (target:∀a:J,Fin (c*t a+1)↪W),
        (∀a:J,∀k:Fin (c*t a),H.Adj (target a ⟨k.val,by omega⟩) (target a ⟨k.val+1,by omega⟩))→
        (∀a b:J,a≠b→Disjoint (Set.range (target a)) (Set.range (target b)))→
        ∃φ:{x // x∈Finset.univ.biUnion (fun a:J=>Finset.univ.image (inner a))}↪W,
          (∀a:J,∀k:Fin (c*t a+1),
            φ ⟨inner a k,Finset.mem_biUnion.mpr ⟨a,Finset.mem_univ _,Finset.mem_image.mpr ⟨k,Finset.mem_univ _,rfl⟩⟩⟩=target a k) ∧
          (∀x y,G.Adj x.val y.val→H.Adj (φ x) (φ y)):=by
  classical
  obtain ⟨index,ext,inner,hext,hinner,hcomponents,hdis,hpaths⟩:=
    long_reserved_prescribed_subwalks G hG components e c d t ht hcapacity
  refine ⟨index,ext,inner,hext,hinner,hcomponents,hdis,hpaths,?_⟩
  intro W H target htarget htargetDis
  have hwalk:∀a:J,∃q:G.Walk (ext a ⟨0,by omega⟩) (ext a ⟨c*t a+4,by omega⟩),
      q.length=c*t a+4 ∧ q.support=List.ofFn (ext a):=by
    intro a
    obtain ⟨p,hppath,hplen,hpsupp,q,hqpath,hqlen,hqsupp,hsub⟩:=hpaths a
    exact ⟨q,hqlen,hqsupp⟩
  have htargetDis':∀a∈(Finset.univ:Finset J),∀b∈(Finset.univ:Finset J),a≠b→
      Disjoint (Set.range (target a)) (Set.range (target b)):=by
    intro a ha b hb hab
    exact htargetDis a b hab
  obtain ⟨φ,hφ,hgraph⟩:=regular_two_buffered_path_family_target_embedding
    (V:=V) (W:=W) (I:=J) G hG H (fun a:J=>c*t a) ext inner hinner hwalk hdis
    (Finset.univ:Finset J) target htarget htargetDis'
  refine ⟨φ,?_,hgraph⟩
  intro a k
  exact hφ a (Finset.mem_univ _) k
end Oberwolfach

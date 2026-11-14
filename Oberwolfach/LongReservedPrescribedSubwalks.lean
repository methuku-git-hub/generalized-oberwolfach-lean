module

public import Oberwolfach.LongReservedPathSubwalk

@[expose] public section
/-! Express the reserved paths and their extensions as simple graph walks. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_reserved_prescribed_subwalks
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
          q.IsPath ∧ q.length=c*t a+4 ∧ q.support=List.ofFn (ext a) ∧ p.IsSubwalk q) := by
  obtain ⟨index,ext,inner,horient,hinner,hmem,hdis,hwalks⟩:=
    long_reserved_prescribed_walks G hG components e c d t ht hcapacity
  refine ⟨index,ext,inner,horient,hinner,hmem,hdis,?_⟩
  intro a
  obtain ⟨p,hp,hplen,hpsupp,q,hq,hqlen,hqsupp⟩:=hwalks a
  have heq:inner a=longReservedInteriorEmbedding (c*t a) (ext a):=by
    ext j
    rw [hinner a j]
    rfl
  refine ⟨p,hp,hplen,hpsupp,q,hq,hqlen,hqsupp,?_⟩
  apply long_reserved_interior_is_subwalk G (c*t a) (ext a) p q
  · simpa [heq] using hpsupp
  · exact hqsupp
end Oberwolfach

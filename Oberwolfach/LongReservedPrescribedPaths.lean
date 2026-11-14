module

public import Oberwolfach.LongReservedOrientedFactorPaths
public import Oberwolfach.LongReservedInteriorPath

@[expose] public section
/-! The reserved-path lemma: all requests have simple paths with disjoint
 two-edge extensions, in the supplied cyclic orders. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_reserved_prescribed_paths
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
      (∀(a:J) (j:Fin (c*t a+4)),G.Adj
        (ext a ⟨j.val,by omega⟩) (ext a ⟨j.val+1,by omega⟩)) ∧
      (∀(a:J) (j:Fin (c*t a+1)),inner a j=ext a ⟨j.val+2,by omega⟩) ∧
      (∀(a:J) (j:Fin (c*t a)),G.Adj
        (inner a ⟨j.val,by omega⟩) (inner a ⟨j.val+1,by omega⟩)) ∧
      (∀a j,ext a j ∈ (components (index a).1).supp) ∧
      (∀a b:J,a≠b→Disjoint (Finset.univ.image (ext a)) (Finset.univ.image (ext b))) := by
  obtain ⟨index,ext,horient,hadj,hmem,hdis⟩:=
    long_reserved_oriented_factor_paths G hG components e c d t ht hcapacity
  let inner:∀a:J,Fin (c*t a+1)↪V:=fun a=>longReservedInteriorEmbedding (c*t a) (ext a)
  refine ⟨index,ext,inner,horient,hadj,?_,?_,hmem,hdis⟩
  · intro a j
    rfl
  · intro a
    exact (long_reserved_interior_path G (c*t a) (ext a) (hadj a)).1
end Oberwolfach

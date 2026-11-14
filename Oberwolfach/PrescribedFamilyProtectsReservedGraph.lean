module

public import Oberwolfach.PrescribedFamilyAvoidPhysicalGraph

@[expose] public section
/-! Prescribed edges avoid a fixed reservoir when free arcs avoid it and
the required edges have separately been shown disjoint from it. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I V:Type} [Fintype I] [Fintype V] [DecidableEq I] [DecidableEq V]
  {X:I→Type} [∀i,Fintype (X i)] [∀i,DecidableEq (X i)]

theorem prescribed_family_protects_reserved_graph
    (pieces:∀i,List (PrescribedSourcePiece (X i))) (Φ:∀i,X i→V)
    (D:V→V→Prop) (K R:SimpleGraph V)
    (hK:∀x y,K.Adj x y→¬R.Adj x y)
    (harc:∀i x y,prescribedDependentDigraph pieces i x y→
      (D (Φ i x) (Φ i y) ∧ ¬R.Adj (Φ i x) (Φ i y)) ∨ K.Adj (Φ i x) (Φ i y)):
    let E:=fun i=>((prescribedDependentGraph pieces i).edgeFinset).image (Sym2.map (Φ i))
    ∀x y,(prescribedPhysicalUnion E).Adj x y→¬R.Adj x y:=by
  apply prescribed_family_avoids_physical_graph pieces Φ
    (fun x y=>(D x y ∧ ¬R.Adj x y) ∨ K.Adj x y) R harc
  intro x y h
  rcases h with h|h
  · exact h.2
  · exact hK x y h
end Oberwolfach

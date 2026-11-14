module

public import Oberwolfach.OrdinaryDeepRootFreeFamilies
public import Oberwolfach.OrdinaryBoundaryRootSets

@[expose] public section
/-! In a host whose deep-to-outside resources have been cleared, every
remaining edge touching the deeper roots lies inside the current pair. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_cleared_root_star_edge_inside
    (R:SimpleGraph V) (S:V→U→Prop) (X T:Finset V) (Z W:Finset U)
    (hTX:T⊆X) (hWZ:W⊆Z)
    (hR:∀v∈T,∀w∉X,¬R.Adj v w)
    (hS:∀v∈T,∀u∉Z,¬S v u)
    (hH:∀u∈W,∀v∉X,¬S v u)
    (a b:V⊕U) (hphys:(ordinaryPhysicalGraph R S).Adj a b)
    (hstar:(ordinaryDeepRootStar T W).Adj a b):
    a∈ordinaryInnerVertices X Z ∧ b∈ordinaryInnerVertices X Z :=by
  cases a with
  | inl v=>
    cases b with
    | inl w=>
      change R.Adj v w at hphys
      change (⊤:SimpleGraph V).Adj v w ∧ (v∈T ∨ w∈T) at hstar
      rcases hstar.2 with hv|hw
      · have hvX:=hTX hv
        have hwX:w∈X:=by by_contra hwX;exact hR v hv w hwX hphys
        exact ⟨(ordinaryInnerVertices_left X Z v).mpr hvX,(ordinaryInnerVertices_left X Z w).mpr hwX⟩
      · have hwX:=hTX hw
        have hvX:v∈X:=by by_contra hvX;exact hR w hw v hvX hphys.symm
        exact ⟨(ordinaryInnerVertices_left X Z v).mpr hvX,(ordinaryInnerVertices_left X Z w).mpr hwX⟩
    | inr u=>
      change S v u at hphys
      change True ∧ (v∈T ∨ u∈W) at hstar
      rcases hstar.2 with hv|hu
      · have huZ:u∈Z:=by by_contra huZ;exact hS v hv u huZ hphys
        exact ⟨(ordinaryInnerVertices_left X Z v).mpr (hTX hv),(ordinaryInnerVertices_right X Z u).mpr huZ⟩
      · have hvX:v∈X:=by by_contra hvX;exact hH u hu v hvX hphys
        exact ⟨(ordinaryInnerVertices_left X Z v).mpr hvX,(ordinaryInnerVertices_right X Z u).mpr (hWZ hu)⟩
  | inr u=>
    cases b with
    | inl v=>
      change S v u at hphys
      change True ∧ (v∈T ∨ u∈W) at hstar
      rcases hstar.2 with hv|hu
      · have huZ:u∈Z:=by by_contra huZ;exact hS v hv u huZ hphys
        exact ⟨(ordinaryInnerVertices_right X Z u).mpr huZ,(ordinaryInnerVertices_left X Z v).mpr (hTX hv)⟩
      · have hvX:v∈X:=by by_contra hvX;exact hH u hu v hvX hphys
        exact ⟨(ordinaryInnerVertices_right X Z u).mpr (hWZ hu),(ordinaryInnerVertices_left X Z v).mpr hvX⟩
    | inr w=>cases hphys
end Oberwolfach

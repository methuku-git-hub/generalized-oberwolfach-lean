module

public import Oberwolfach.CycleEdgeEnumeration

@[expose] public section
/-! An ordered cycle is contained in the host exactly when all its successive
edges are host edges. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem cycleGraph_map_le_iff {V:Type} (r:ℕ) (hr:3≤r) (f:Fin r↪V) (P:SimpleGraph V):
    (SimpleGraph.cycleGraph r).map f≤P ↔ ∀ i:Fin r,P.Adj (f i) (f (cycleNext i)):=by
  have hAdj (i j:Fin r):(SimpleGraph.cycleGraph r).Adj i j ↔ cycleNext i=j ∨ cycleNext j=i:=by
    rw [cycleGraph_modular_adj (by omega)]
    constructor
    · rintro (h|h)
      · exact Or.inl (Fin.ext h)
      · exact Or.inr (Fin.ext h)
    · rintro (h|h)
      · exact Or.inl (congrArg Fin.val h)
      · exact Or.inr (congrArg Fin.val h)
  constructor
  · intro h i
    apply h
    apply SimpleGraph.map_adj_apply.mpr
    exact (hAdj i (cycleNext i)).mpr (Or.inl rfl)
  · intro h x y hxy
    rw [SimpleGraph.map_adj] at hxy
    obtain ⟨i,j,hij,hix,hjy⟩:=hxy
    rcases (hAdj i j).mp hij with hforward|hbackward
    · rw [←hix,←hjy,←hforward]
      exact h i
    · rw [←hix,←hjy,←hbackward]
      exact (h j).symm
end Oberwolfach

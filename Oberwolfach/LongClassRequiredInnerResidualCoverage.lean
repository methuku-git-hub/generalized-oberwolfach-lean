module

public import Oberwolfach.LongClassInnerRequiredRepair
public import Oberwolfach.LongEligibleMarkedIncomingChange

@[expose] public section
/-! Once the actual packing contains the enlarged required graph, every arc
left in the first inner pair is a selected reference edge. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V]

theorem long_class_required_inner_residual_coverage
    (S Sel Used Small:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (I:Finset V)
    (D:V→V→Prop) (Pack:Finset (Sym2 V)) (M:V→V→ℕ)
    (hphysical:∀x y,M x y+M y x=if S.Adj x y then 1 else 0)
    (hPack:Pack⊆Used.edgeFinset) (hUsedSel:∀x y,Used.Adj x y→¬Sel.Adj x y):
    let K:=longRequiredPhysicalGraph S (S\Used) Sel π d I D (fun x y=>Used.Adj x y)
    let Old:=SimpleGraph.fromEdgeSet (↑Pack:Set (Sym2 V))
    let Kplus:=longClassInnerRequiredRepair S Used K I Pack
    (∀x y,s(x,y)∈Pack→x≠y→Small.Adj x y)→Kplus≤Small→
    ∀x∈I,∀y∈I,longEligibleResidualArc M Small ⊥ (x,y)→Sel.Adj x y:=by
  intro K Old Kplus hOld hK x hx y hy hp
  have hrepair:=long_class_inner_required_repair_properties S Sel Used π d I D Pack hPack hUsedSel
  have hm:M x y=1:=hp.1
  have hs:S.Adj x y:=by
    by_contra hn
    have hh:=hphysical x y
    simp only [hn,if_false] at hh
    omega
  by_contra hn
  have hnotPack:s(x,y)∉Pack:=by
    intro h
    exact hp.2.1 (hOld x y h hs.ne)
  exact hp.2.1 (hK (hrepair.2.2.1 x y hx hy hs hn hnotPack))
end Oberwolfach

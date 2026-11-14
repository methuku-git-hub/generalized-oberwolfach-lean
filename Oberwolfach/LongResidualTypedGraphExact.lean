module

public import Oberwolfach.LongReferenceResidualTypedGraphs
public import Oberwolfach.MarkedPartitionedResidualHost

@[expose] public section
/-! The residual type graphs are exactly the physical ordinary and marked
arc graphs of the corrected full residual partition. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [LinearOrder V] [Nonempty V]
local instance residualTypedExactDecEq : DecidableEq V := Classical.decEq V
local instance residualTypedExactArc (P:V×V→Prop):DecidableEq {e:V×V // P e}:=Classical.decEq _

theorem long_residual_typed_graph_exact
    (S Small:SimpleGraph V) (M:V→V→ℕ)
    (hphysical:∀x y,M x y+M y x=if S.Adj x y then 1 else 0):
    let P:=longEligibleResidualArc M Small ⊥;
    ∀(T:Finset {e:V×V // P e}) (mark:Bool) (x y:V),
      (longResidualTypedGraph S Small M T mark).Adj x y ↔
      if mark then ∃e:residualMarkedArc P T,e.val.val=(x,y)∨e.val.val=(y,x)
      else ∃e:residualOrdinaryArc P T,e.val.val=(x,y)∨e.val.val=(y,x):=by
  intro P T mark x y
  have hgraph:∀e:{a:V×V // P a},(S\Small).Adj e.val.1 e.val.2:=by
    intro e
    have hm:=e.property.1
    have hp:=hphysical e.val.1 e.val.2
    have hs:S.Adj e.val.1 e.val.2:=by
      split_ifs at hp with hh
      · exact hh
      · omega
    exact ⟨hs,e.property.2.1⟩
  cases mark with
  | false =>
    constructor
    · rintro ⟨_,e,he,ht⟩
      exact ⟨⟨e,ht⟩,he⟩
    · rintro ⟨e,he⟩
      refine ⟨?_,e.val,he,e.property⟩
      rcases he with he|he
      · simpa only [he] using hgraph e.val
      · have hh:=hgraph e.val
        simpa only [he] using hh.symm
  | true =>
    constructor
    · rintro ⟨_,e,he,ht⟩
      exact ⟨⟨e,ht⟩,he⟩
    · rintro ⟨e,he⟩
      refine ⟨?_,e.val,he,e.property⟩
      rcases he with he|he
      · simpa only [he] using hgraph e.val
      · have hh:=hgraph e.val
        simpa only [he] using hh.symm
end Oberwolfach

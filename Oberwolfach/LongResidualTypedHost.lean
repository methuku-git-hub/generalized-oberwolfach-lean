module

public import Oberwolfach.MarkedPartitionedResidualHost
public import Oberwolfach.LongMarkedResidualIncomingChange
public import Oberwolfach.LongPreparationIneligibleGraph

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [LinearOrder V]
local instance residualTypedHostDecEq : DecidableEq V := Classical.decEq V
local instance residualTypedHostArcDecEq (P:V×V→Prop):DecidableEq {e:V×V // P e}:=Classical.decEq _

theorem long_residual_typed_host_physical_properties
    (G S Small:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (Mhost:V→V→ℕ)
    (hphysical:∀x y,Mhost x y+Mhost y x=if S.Adj x y then 1 else 0)
    (hhost:∀x y,Mhost x y=1→G.Adj x y):
    let P:=longResidualHostArc Mhost Small (longPreparationIneligibleGraph G π d)
    ∀M:Finset {e:V×V // P e},
    let E:=residualOrdinaryArc P M
    let K:=residualMarkedArc P M
    let tail:=fun e:E=>e.val.val.1
    let head:=fun e:E=>e.val.val.2
    let ktail:=fun e:K=>e.val.val.1
    let khead:=fun e:K=>π.symm e.val.val.2
    Function.Injective (markedPhysicalEdge tail head ktail khead π) ∧
    (∀e:E,¬PermutationClose π (3*d) (tail e) (head e)∧G.Adj (tail e) (head e)) ∧
    (∀e:K,¬PermutationClose π (3*d) (ktail e) (khead e)∧G.Adj (ktail e) (π (khead e))):=by
  intro P M E K tail head ktail khead
  have hAnti:∀x y,P (x,y)→P (y,x)→False:=by
    intro x y hx hy
    have hh:=hphysical x y
    have h₁:Mhost x y=1:=hx.1
    have h₂:Mhost y x=1:=hy.1
    split_ifs at hh <;> omega
  refine ⟨partitioned_residual_physical_injective P M π hAnti,?_,?_⟩
  · intro e
    have he:=e.val.property
    have hg:G.Adj e.val.val.1 e.val.val.2:=hhost _ _ he.1
    refine ⟨?_,hg⟩
    intro h
    exact he.2.2 ⟨hg,Or.inl h⟩
  · intro e
    have he:=e.val.property
    have hg:G.Adj e.val.val.1 e.val.val.2:=hhost _ _ he.1
    refine ⟨?_,?_⟩
    · intro h
      exact he.2.2 ⟨hg,Or.inr (Or.inl h)⟩
    · change G.Adj e.val.val.1 (π (π.symm e.val.val.2))
      simpa only [Equiv.apply_symm_apply] using hg
end Oberwolfach

module

public import Oberwolfach.OrdinaryRequiredAvoidsForbidden
public import Oberwolfach.OrdinaryProtectedRequiredDegree
public import Oberwolfach.OrdinarySampledSurvivalTarget

@[expose] public section
/-! Required edges, surviving selected arcs and old approximate arcs all
lie in the edited target after removing the protected reservoir rim. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance (priority := 2000) ordinaryForbiddenRequiredSix:DecidableEq (Fin 6):=instDecidableEqFin 6
variable {V U Γ Color:Type} [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U]
  [Fintype Γ] [Fintype Color]

theorem ordinary_forbidden_required_directed_host
    (P Target Reference Protect Bad Host:SimpleGraph V) (hHost:Host≤P) (Inner:Finset V)
    (π:Equiv.Perm V) (d:ℕ)
    (σ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e):
    let Sample:=longPhysicalStateGraph P σ {0,1,2,3,4};
    Reference≤Sample → Protect≤Reference → Disjoint Reference Bad →
    let G:=ordinaryForbiddenRequired Target Sample Reference Bad Inner
    let Del:=ordinaryForbiddenSampleDeletion Sample Target Reference Protect Bad Inner
    let Base:=Target\Protect
    let Dfree:=fun x y=>rawSelectedPhysicalRelation P π d (fun e=>σ (Sum.inl e)) x y ∧ ¬Del.Adj x y
    let Dstar:=fun x y=>Dfree x y ∨ G.Adj x y;
    (∀x y,G.Adj x y→Dstar x y∨Dstar y x) ∧
    (∀x y,Dfree x y→Dstar x y) ∧
    (∀x y,Dstar x y→Base.Adj x y) ∧
    (∀x y,Dfree x y→ rawSelectedPhysicalRelation P π d (fun e=>σ (Sum.inl e)) x y) ∧
    (∀x y,rawMixedPhysicalArc Host π d
      (rawMarkedDeleteRims (fun e=>rawExpandedApproximateCollapse e (σ e)) Del.edgeFinset) x y→Base.Adj x y):=by
  intro Sample hRef hProtect hBad G Del Base Dfree Dstar
  have hrel:=ordinary_forbidden_required_relations Target Sample Reference Protect Bad Inner hRef hProtect hBad
  have hDel:Sample\Base≤Del:=by
    intro x y he
    by_contra hn
    exact he.2 (hrel.2.1 ⟨he.1,hn⟩)
  have hsurvive:=ordinary_sampled_survival_in_target P Base Host Del hHost π d σ hDel
  refine ⟨?_,?_,?_,?_,hsurvive.2⟩
  · intro x y h;exact Or.inl (Or.inr h)
  · intro x y h;exact Or.inl h
  · intro x y h
    rcases h with h|h
    · exact hsurvive.1 x y h.1 h.2
    · exact hrel.1 h
  · intro x y h;exact h.1


theorem ordinary_old_edges_avoid_forbidden_required
    (Target Sample Reference Protect Bad Host:SimpleGraph V) (Inner:Finset V)
    (hRef:Reference≤Sample) (hProtect:Protect≤Reference) (hBad:Disjoint Reference Bad)
    (Old:Finset (Sym2 V))
    (hSample:Old⊆Sample.edgeFinset)
    (hSurvive:Old⊆(Host\ordinaryForbiddenSampleDeletion Sample Target Reference Protect Bad Inner).edgeFinset):
    Disjoint Old (ordinaryForbiddenRequired Target Sample Reference Bad Inner).edgeFinset:=by
  apply Finset.disjoint_left.mpr
  intro e heOld heReq
  induction e using Sym2.inductionOn with
  | _ v w=>
    have hs:Sample.Adj v w:=SimpleGraph.mem_edgeFinset.mp (hSample heOld)
    have hd:(Host\ordinaryForbiddenSampleDeletion Sample Target Reference Protect Bad Inner).Adj v w:=
      SimpleGraph.mem_edgeFinset.mp (hSurvive heOld)
    have hr:(ordinaryForbiddenRequired Target Sample Reference Bad Inner).Adj v w:=SimpleGraph.mem_edgeFinset.mp heReq
    have hh:=ordinary_forbidden_required_relations Target Sample Reference Protect Bad Inner hRef hProtect hBad
    exact hh.2.2.1 v w hr ⟨hs,hd.2⟩

theorem ordinary_forbidden_required_edit_degree_bounds
    (Target Sample Reference Protect Bad:SimpleGraph V) (Inner:Finset V) (b a c:ℝ)
    (hEdit:∀v,((Finset.univ.filter (fun w=>Xor (Target.Adj v w) (Sample.Adj v w))).card:ℝ)≤b)
    (hProtect:∀v,(Protect.degree v:ℝ)≤a) (hBad:∀v,(Bad.degree v:ℝ)≤c):
    (∀v,((ordinaryForbiddenRequired Target Sample Reference Bad Inner).degree v:ℝ)≤b+Inner.card+c) ∧
    (∀v,((ordinaryForbiddenSampleDeletion Sample Target Reference Protect Bad Inner).degree v:ℝ)≤b+a+Inner.card+c):=by
  have hh:=ordinary_protected_required_degree_bounds Target Sample Reference Protect Inner b a hEdit hProtect
  constructor <;> intro v
  · have hn:= (ordinary_forbidden_required_degree_bounds Target Sample Reference Protect Bad Inner v).1
    have hr:((ordinaryForbiddenRequired Target Sample Reference Bad Inner).degree v:ℝ)≤
        (ordinaryProtectedRequired Target Sample Reference Inner).degree v+Bad.degree v:=by exact_mod_cast hn
    linarith [hh.1 v,hBad v]
  · have hn:= (ordinary_forbidden_required_degree_bounds Target Sample Reference Protect Bad Inner v).2
    have hr:((ordinaryForbiddenSampleDeletion Sample Target Reference Protect Bad Inner).degree v:ℝ)≤
        (ordinaryProtectedSampleDeletion Sample Target Reference Protect Inner).degree v+Bad.degree v:=by exact_mod_cast hn
    linarith [hh.2 v,hBad v]
end Oberwolfach

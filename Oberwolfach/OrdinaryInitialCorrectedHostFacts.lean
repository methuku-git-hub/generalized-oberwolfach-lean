module

public import Oberwolfach.OrdinaryRawIntervalGeometry
public import Oberwolfach.OrdinaryResourceSubgraphs

@[expose] public section
/-! Removing forbidden rim edges, a correction and reservoir keeps the
initial host inside the original graph and disjoint from the forbidden graph. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]

theorem ordinary_initial_corrected_host_facts
    (P F JQ:SimpleGraph V) (JH:V→U→Prop) (π:Equiv.Perm V) (d:ℕ) (j:Color)
    (σ:RawWheelOutcome V U Γ Color) (K:Finset (Sym2 V⊕(V×U))):
    let R:=rawWheelGraph P σ;let J:=rawWheelSpokes π d σ j;
    let Qcorr:=(R\F)\JQ;let Hcorr:=fun v u=>J v u∧¬JH v u;
    let G:=Qcorr\ordinaryResourceRim Qcorr K;let Hs:=fun v u=>Hcorr v u∧¬(Sum.inr (v,u)∈K);
    G≤P ∧ Disjoint G F ∧ (∀v u,Hs v u→J v u):=by
  intro R J Qcorr Hcorr G Hs
  have hGR:G≤R:=(show G≤Qcorr from sdiff_le).trans ((show Qcorr≤R from sdiff_le.trans sdiff_le))
  refine ⟨hGR.trans (retainedGraph_le P _),?_,?_⟩
  · apply disjoint_iff_inf_le.mpr
    intro v w hvw
    have hg:Qcorr.Adj v w:=(show G≤Qcorr from sdiff_le) hvw.1
    exact hg.1.2 hvw.2
  · intro v u h
    exact h.1.1
end Oberwolfach

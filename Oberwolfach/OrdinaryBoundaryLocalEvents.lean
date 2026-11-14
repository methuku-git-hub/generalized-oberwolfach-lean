module

public import Oberwolfach.OrdinaryBoundaryExtensionRetention
public import Oberwolfach.OrdinaryBoundaryHubPairRetention
public import Oberwolfach.GoodPlacementEvents

@[expose] public section
/-! Named same-sample extension and two-spoke events for sparse cleanup. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

def OrdinaryBoundaryExtensionGood (Q:SimpleGraph V) (H:V→U→Prop) (X:Finset V)
    (β p:ℝ) (σ:Sym2 (V⊕U)→Bool):Prop:=
  ∀a c u,p^3*β*Fintype.card (V⊕U)/2≤
    ((retainedPatternSet (X.filter (fun v=>Q.Adj a v∧Q.Adj v c∧H v u))
      (markedBoundaryJoinCoins a c u) σ).card:ℝ)

def OrdinaryBoundaryHubPairGood (H:V→U→Prop) (Z:Finset U) (β p:ℝ) (σ:Sym2 (V⊕U)→Bool):Prop:=
  ∀a c,β*Fintype.card (V⊕U)≤((Z.filter (fun u=>H a u∧H c u)).card:ℝ)→
    p^2*β*Fintype.card (V⊕U)/2≤
      ((retainedPatternSet (Z.filter (fun u=>H a u∧H c u)) (ordinaryBoundaryHubPairCoins a c) σ).card:ℝ)

theorem ordinary_boundary_local_events_high_probability (βe βh p:ℝ)
    (hβe:0<βe) (hβh:0<βh) (hp:0<p) (hp1:p≤1) (q:ℕ):
    ∃N:ℕ,∀(V U:Type) [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U],
      N≤Fintype.card (V⊕U)→∀(Q:SimpleGraph V) (H:V→U→Prop) (X:Finset V) (Z:Finset U),
      (∀a c u,βe*Fintype.card (V⊕U)≤
        ((X.filter (fun v=>Q.Adj a v∧Q.Adj v c∧H v u)).card:ℝ))→
      1-2/(Fintype.card (V⊕U):ℝ)^q≤
        (FiniteLaw.pi (fun _:Sym2 (V⊕U)=>FiniteLaw.retentionCoin p hp.le hp1)).probability
          (fun σ=>OrdinaryBoundaryExtensionGood Q H X βe p σ ∧ OrdinaryBoundaryHubPairGood H Z βh p σ):=by
  obtain ⟨N,hN⟩:=ordinary_boundary_extension_retention_event βe p hβe hp hp1 q
  obtain ⟨M,hM⟩:=ordinary_boundary_hub_pair_retention_event βh p hβh hp hp1 q
  refine ⟨max N M,?_⟩
  intro V U _ _ _ _ hn Q H X Z hparent
  let ν:=FiniteLaw.pi (fun _:Sym2 (V⊕U)=>FiniteLaw.retentionCoin p hp.le hp1)
  let δ:ℝ:=1/(Fintype.card (V⊕U):ℝ)^q
  have he:1-δ≤ν.probability (OrdinaryBoundaryExtensionGood Q H X βe p):=hN V U (by omega) Q H X hparent
  have hh:1-δ≤ν.probability (OrdinaryBoundaryHubPairGood H Z βh p):=hM V U (by omega) H Z
  have hi:=finiteLaw_good_intersection ν (OrdinaryBoundaryExtensionGood Q H X βe p)
    (OrdinaryBoundaryHubPairGood H Z βh p) δ hh
  change 1-2/(Fintype.card (V⊕U):ℝ)^q≤_
  dsimp [δ] at he hi
  have htwo:2/(Fintype.card (V⊕U):ℝ)^q=
      1/(Fintype.card (V⊕U):ℝ)^q+1/(Fintype.card (V⊕U):ℝ)^q:=by ring
  rw [htwo]
  linarith only [he,hi]
end Oberwolfach

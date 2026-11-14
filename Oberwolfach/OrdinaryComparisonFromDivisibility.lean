module

public import Oberwolfach.OrdinaryDisjointWheelComparison
public import Oberwolfach.OrdinaryExpansionCentralGraph
public import Oberwolfach.OrdinaryTransferCycles

@[expose] public section

/-! Construct the decomposable comparison graph directly from local
wheel-divisibility. No decomposition of the original graph is assumed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

abbrev OrdinaryComparisonRows (r k : ℕ) := Fin k⊕(Fin k×Fin r)
abbrev OrdinaryComparisonHubs (k : ℕ) := Empty⊕Fin k

def ordinaryComparisonRim (r k : ℕ) (hr : 0<r) : SimpleGraph (OrdinaryComparisonRows r k) :=
  ordinaryAttachmentRim ⊥ (SimpleGraph.cycleGraph r) ⟨0,hr⟩ id

def ordinaryComparisonSpokes (r k : ℕ) (hr : 0<r) : OrdinaryComparisonRows r k → OrdinaryComparisonHubs k → Prop :=
  disjointWheelSpokes ⟨0,hr⟩

theorem ordinaryComparison_order (r k : ℕ) :
    Fintype.card (OrdinaryComparisonRows r k)+Fintype.card (OrdinaryComparisonHubs k)=k*(r+2) := by
  simp only [OrdinaryComparisonRows,OrdinaryComparisonHubs,Fintype.card_sum,Fintype.card_prod,
    Fintype.card_fin,Fintype.card_empty,zero_add]
  ring

theorem ordinary_comparison_from_divisibility {V U : Type}
    [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
    (G : SimpleGraph V) (H : V → U → Prop) (r : ℕ) (hr : 3≤r)
    (hbal : ∀ v,G.degree v=2*(Finset.univ.filter (H v)).card)
    (hdiv : ∀ u,r∣(Finset.univ.filter (fun v => H v u)).card) :
    let k := G.edgeFinset.card/r
    let Q := ordinaryComparisonRim r k (by omega)
    let K := ordinaryComparisonSpokes r k (by omega)
    HasOrdinaryWheelDecomposition Q K r ∧
    (∀ a,Q.degree a=2*(Finset.univ.filter (K a)).card) ∧
    (∀ b,r∣(Finset.univ.filter (fun a => K a b)).card) ∧
    Q.edgeFinset.card=G.edgeFinset.card ∧
    Fintype.card {e:OrdinaryComparisonRows r k×OrdinaryComparisonHubs k // K e.1 e.2}=
      Fintype.card {e:V×U // H e.1 e.2} := by
  dsimp only
  let k := G.edgeFinset.card/r
  have hkr : k*r=G.edgeFinset.card := Nat.div_mul_cancel (ordinary_balanced_rim_total_divisible G H r hbal hdiv)
  have hcycle : IsEmbeddedCycle (SimpleGraph.cycleGraph r) r := by
    refine ⟨hr,Function.Embedding.refl _,?_⟩
    change SimpleGraph.cycleGraph r=(SimpleGraph.cycleGraph r).map id
    rw [SimpleGraph.map_id]
  have hfull : ∀ w:Fin r,w∈(SimpleGraph.cycleGraph r).support := by
    intro w
    rw [cycleGraph_support_eq_univ hr]
    exact Set.mem_univ _
  obtain ⟨hdec,hb,hd,he,hs⟩ := disjoint_wheel_comparison (I:=Fin k) (SimpleGraph.cycleGraph r) r hcycle
    ⟨0,by omega⟩ hfull (Fintype.card_fin r)
  have he' : (ordinaryComparisonRim r k (by omega)).edgeFinset.card=G.edgeFinset.card := by
    simpa only [ordinaryComparisonRim,OrdinaryComparisonRows,Fintype.card_fin,hkr] using he
  have hs' : Fintype.card {e:OrdinaryComparisonRows r k×OrdinaryComparisonHubs k //
      ordinaryComparisonSpokes r k (by omega) e.1 e.2}=Fintype.card {e:V×U // H e.1 e.2} := by
    calc
      _ = k*r := by simpa only [ordinaryComparisonSpokes,OrdinaryComparisonRows,OrdinaryComparisonHubs,Fintype.card_fin] using hs
      _ = G.edgeFinset.card := hkr
      _ = _ := ordinary_balanced_total_edges G H hbal
  exact ⟨hdec,hb,hd,he',hs'⟩

end Oberwolfach

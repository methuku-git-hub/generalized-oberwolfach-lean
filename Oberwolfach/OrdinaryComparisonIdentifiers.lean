module

public import Oberwolfach.OrdinaryComparisonFromDivisibility

@[expose] public section

/-! Equal physical edge counts supply the actual private-index
bijections, and the shared central expansion is wheel-divisible. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U : Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_comparison_identifier_equivalences (G : SimpleGraph V) (H : V → U → Prop)
    (r : ℕ) (hr : 3≤r)
    (hbal : ∀ v,G.degree v=2*(Finset.univ.filter (H v)).card)
    (hdiv : ∀ u,r∣(Finset.univ.filter (fun v => H v u)).card) :
    let k := G.edgeFinset.card/r
    let Q := ordinaryComparisonRim r k (by omega)
    let K := ordinaryComparisonSpokes r k (by omega)
    Nonempty (Q.edgeFinset≃G.edgeFinset) ∧
      Nonempty ({e:OrdinaryComparisonRows r k×OrdinaryComparisonHubs k // K e.1 e.2}≃
        {e:V×U // H e.1 e.2}) := by
  dsimp only
  have h := ordinary_comparison_from_divisibility G H r hr hbal hdiv
  constructor
  · apply Nonempty.intro
    apply Fintype.equivOfCardEq
    simpa only [Fintype.card_coe] using h.2.2.2.1
  · exact ⟨Fintype.equivOfCardEq h.2.2.2.2⟩

theorem cycleGraph_zero_last_adj (r : ℕ) (hr : 3≤r) :
    (SimpleGraph.cycleGraph r).Adj (⟨0,by omega⟩:Fin r) ⟨r-1,by omega⟩ := by
  rw [cycleGraph_modular_adj (by omega)]
  right
  change ((r-1)+1)%r=0
  rw [Nat.sub_add_cancel (by omega : 1≤r),Nat.mod_self]

theorem original_central_cycle_divisible (G : SimpleGraph V) (H : V → U → Prop)
    (r : ℕ) (hr : 3≤r)
    (hbal : ∀ v,G.degree v=2*(Finset.univ.filter (H v)).card)
    (hdiv : ∀ u,r∣(Finset.univ.filter (fun v => H v u)).card) :
    let z : Fin r := ⟨0,by omega⟩
    let o : Fin r := ⟨r-1,by omega⟩
    let Q := ordinaryExpansionRim (J:={e:V×U // H e.1 e.2}) (SimpleGraph.cycleGraph r) z o
      (fun _ : G.edgeFinset => ()) (fun _ => ())
    let K := ordinaryExpansionSpokes (E:=G.edgeFinset) z
      (fun _ : {e:V×U // H e.1 e.2} => ()) (fun _ => ())
    (∀ a,Q.degree a=2*(Finset.univ.filter (K a)).card) ∧
      (∀ b,r∣(Finset.univ.filter (fun a => K a b)).card) := by
  dsimp only
  have hcard : Fintype.card G.edgeFinset=Fintype.card {e:V×U // H e.1 e.2} := by
    simpa only [Fintype.card_coe] using ordinary_balanced_total_edges G H hbal
  exact ⟨ordinaryExpansion_central_balance _ _ _ (cycleGraph_zero_last_adj r hr)
    (by intro a;simpa only [←SimpleGraph.ncard_neighborSet] using (cycleGraph_regular hr a)) hcard,
    ordinaryExpansion_central_hub_divisibility r (Fintype.card_fin r) _ (ordinary_spoke_total_divisible H r hdiv)⟩

end Oberwolfach

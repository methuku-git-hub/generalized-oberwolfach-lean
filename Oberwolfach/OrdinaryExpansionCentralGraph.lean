module

public import Oberwolfach.OrdinaryExpansionDegrees
public import Oberwolfach.OrdinaryExpansionResourceMaps

@[expose] public section

/-! The central graph is an actual simple expansion of repeated formal
loops at one row root and repeated formal spokes to one hub root. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {E J W : Type} [Fintype E] [Fintype J] [Fintype W]
    [DecidableEq E] [DecidableEq J] [DecidableEq W]

theorem ordinaryExpansion_central_balance (C : SimpleGraph W) (z o : W)
    (hzo : C.Adj z o) (hC : C.IsRegularOfDegree 2) (hEJ : Fintype.card E=Fintype.card J) :
    ∀ a,(ordinaryExpansionRim (J:=J) C z o (fun _ : E => ()) (fun _ => ())).degree a=
      2*(Finset.univ.filter (ordinaryExpansionSpokes z (fun _ : J => ()) (fun _ => ()) a)).card := by
  apply ordinaryExpansion_row_balance C z o hzo hC
  intro a
  cases a
  simp [hEJ,two_mul]

theorem ordinaryExpansion_central_hub_divisibility (r : ℕ) (hW : Fintype.card W=r)
    (z : W) (hJ : r ∣ Fintype.card J) :
    ∀ b,r ∣ (Finset.univ.filter (fun a => ordinaryExpansionSpokes (E:=E) z
      (fun _ : J => ()) (fun _ => ()) a b)).card := by
  apply ordinaryExpansion_hub_divisibility r hW
  intro b
  cases b
  simpa using hJ

theorem ordinaryExpansion_central_order :
    Fintype.card (ExpansionRow Unit E J W)+Fintype.card (ExpansionHub Unit E J)=
      2+(Fintype.card E+Fintype.card J)*(Fintype.card W+1) := by
  simpa using (ordinaryExpansion_order (V:=Unit) (U:=Unit) (E:=E) (J:=J) (W:=W))

theorem cycleGraph_zero_one_adj (r : ℕ) (hr : 3≤r) :
    (SimpleGraph.cycleGraph r).Adj (⟨0,by omega⟩ : Fin r) (⟨1,by omega⟩ : Fin r) := by
  rw [cycleGraph_modular_adj (by omega)]
  exact Or.inl (by simp [Nat.mod_eq_of_lt (by omega : 1<r)])

theorem ordinaryExpansion_central_cycle_divisible (r : ℕ) (hr : 3≤r)
    (hEJ : Fintype.card E=Fintype.card J) (hJ : r ∣ Fintype.card J) :
    let z : Fin r := ⟨0,by omega⟩
    let o : Fin r := ⟨1,by omega⟩
    let G := ordinaryExpansionRim (J:=J) (SimpleGraph.cycleGraph r) z o (fun _ : E => ()) (fun _ => ())
    let H := ordinaryExpansionSpokes (E:=E) z (fun _ : J => ()) (fun _ => ())
    (∀ a,G.degree a=2*(Finset.univ.filter (H a)).card) ∧
      (∀ b,r ∣ (Finset.univ.filter (fun a => H a b)).card) := by
  dsimp only
  exact ⟨ordinaryExpansion_central_balance _ _ _ (cycleGraph_zero_one_adj r hr)
    (by intro a;simpa only [←SimpleGraph.ncard_neighborSet] using (cycleGraph_regular hr a)) hEJ,
    ordinaryExpansion_central_hub_divisibility r (Fintype.card_fin r) _ hJ⟩

theorem ordinaryExpansion_collapse_resources
    {V U : Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
    (C : SimpleGraph W) (z o : W) (hzo : z≠o)
    (x y : E → V) (v : J → V) (u : J → U) :
    let S := ordinaryHostResources (ordinaryExpansionRim C z o x y) (ordinaryExpansionSpokes z v u)
    let T := ordinaryHostResources (ordinaryExpansionRim (J:=J) C z o (fun _ : E => ()) (fun _ => ()))
      (ordinaryExpansionSpokes z (fun _ : J => ()) (fun _ => ()))
    let f := expansionResourceMap (E:=E) (J:=J) (W:=W) (fun _ : V => ()) (fun _ : U => ())
    Set.InjOn f S ∧ S.image f=T := by
  dsimp only
  exact ⟨ordinaryExpansion_resources_injective C z o hzo x y v u _ _,
    ordinaryExpansion_resources_image C z o x y v u _ _⟩

end Oberwolfach

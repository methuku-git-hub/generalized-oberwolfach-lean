module

public import Oberwolfach.OrdinaryBoundaryPrescribedLoadBudget

@[expose] public section
/-! Boundary starts and unmatched physical rows control the prescribed load;
forced inner targets use only the protected-hub budget. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_reserved_forced_load_from_boundary
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (d:ℕ) (δ a γ:ℝ) (hd:0<d) (hδ:0≤δ) (hU:Fintype.card U≤n)
    (hD:4/(d:ℝ)≤δ/16)
    (hN:4*(n:ℝ)^(3/4:ℝ)≤δ*n/16)
    (hMatching:2*((max a γ)*n)≤δ*n/8)
    (Prescribed T:U→Finset (Fin n)) (Protected:Finset U) (G:SimpleGraph (Fin n))
    (hpres:∀v,((Finset.univ.filter (fun u=>v∈Prescribed u)).card:ℝ)≤
      4*(Fintype.card U:ℝ)/d+4*(n:ℝ)^(3/4:ℝ)+2*((max a γ)*n))
    (hbad:∀v,(G.degree v:ℝ)≤δ*n/8)
    (hT:∀u,T u≠∅→u∈Protected) (hProtected:(Protected.card:ℝ)≤δ*n/2):
    ∀v,((Finset.univ.filter (fun u=>v∈Prescribed u)).card:ℝ)+G.degree v+
      ((Finset.univ.filter (fun u=>v∈T u)).card:ℝ)≤δ*n :=by
  let pres:=fun v:Fin n=>((Finset.univ.filter (fun u=>v∈Prescribed u)).card:ℝ)
  let bad:=fun v:Fin n=>(G.degree v:ℝ)
  have hb:=ordinary_boundary_prescribed_load_budget n (Fintype.card U) d δ a γ hd hδ hU hD hN hMatching pres bad hpres hbad
  intro v
  have ht:((Finset.univ.filter (fun u=>v∈T u)).card:ℝ)≤Protected.card:=by
    apply Nat.cast_le.mpr
    apply Finset.card_le_card
    intro u hu
    simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hu
    apply hT u
    intro hEmpty
    simpa [hEmpty] using hu
  have hbase:=hb v
  dsimp [pres,bad] at hbase
  linarith
end Oberwolfach

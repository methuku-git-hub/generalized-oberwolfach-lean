module

public import Oberwolfach.OrdinaryWheelRemainders

@[expose] public section
/-! Temporarily reserve the star of a balanced corrected inner host.  At
    the protected roots the outside host remains balanced and divisible. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 3000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

def ordinaryRimRootStar (G:SimpleGraph V) (T:Finset V):SimpleGraph V where
  Adj v w := G.Adj v w ∧ (v∈T ∨ w∈T)
  symm := ⟨by intro v w h; exact ⟨h.1.symm,h.2.symm⟩⟩
  loopless := ⟨by intro v h; exact G.ne_of_adj h.1 rfl⟩

def ordinarySpokeRootStar (K:V→U→Prop) (T:Finset V) (W:Finset U):V→U→Prop :=
  fun v u=>K v u ∧ (v∈T ∨ u∈W)

theorem ordinary_corrected_inner_star_root_balance
    (Q C:SimpleGraph V) (H K:V→U→Prop) (T:Finset V) (W:Finset U) (r:ℕ)
    (hCQ:C≤Q) (hKH:∀v u,K v u→H v u)
    (hQ:∀v∈T,Q.degree v=2*(Finset.univ.filter (H v)).card)
    (hC:∀v∈T,C.degree v=2*(Finset.univ.filter (K v)).card)
    (hH:∀u∈W,r∣(Finset.univ.filter (fun v=>H v u)).card)
    (hK:∀u∈W,r∣(Finset.univ.filter (fun v=>K v u)).card):
    let R:=ordinaryRimRootStar C T;
    let S:=ordinarySpokeRootStar K T W;
    R≤Q ∧ (∀v u,S v u→H v u) ∧
    (∀v∈T,(Q\R).degree v=2*(Finset.univ.filter (fun u=>H v u∧¬S v u)).card) ∧
    (∀u∈W,r∣(Finset.univ.filter (fun v=>H v u∧¬S v u)).card) :=by
  intro R S
  have hR:R≤Q:=by intro v w h;exact hCQ h.1
  have hS:∀v u,S v u→H v u:=by intro v u h;exact hKH v u h.1
  have hr (v:V) (hv:v∈T):R.degree v=C.degree v:=by
    rw [←SimpleGraph.card_neighborFinset_eq_degree,←SimpleGraph.card_neighborFinset_eq_degree]
    congr 1
    ext w
    simp only [SimpleGraph.mem_neighborFinset]
    change (C.Adj v w ∧ (v∈T ∨ w∈T)) ↔ C.Adj v w
    simp [hv]
  have hs (v:V) (hv:v∈T):(Finset.univ.filter (S v)).card=(Finset.univ.filter (K v)).card:=by
    congr 1
    ext u
    simp [S,ordinarySpokeRootStar,hv]
  have hc (u:U) (hu:u∈W):(Finset.univ.filter (fun v=>S v u)).card=(Finset.univ.filter (fun v=>K v u)).card:=by
    congr 1
    ext v
    simp [S,ordinarySpokeRootStar,hu]
  refine ⟨hR,hS,?_,?_⟩
  · intro v hv
    rw [graph_degree_sdiff Q R hR v,spoke_row_sdiff_card H S hS v,hr v hv,hs v hv,hQ v hv,hC v hv,Nat.mul_sub_left_distrib]
  · intro u hu
    rw [spoke_col_sdiff_card H S hS u,hc u hu]
    exact Nat.dvd_sub (hH u hu) (hK u hu)
end Oberwolfach

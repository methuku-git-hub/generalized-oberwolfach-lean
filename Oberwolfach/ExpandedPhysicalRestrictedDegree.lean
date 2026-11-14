module

public import Oberwolfach.ColourDegreeEvent
public import Oberwolfach.MarkedExpandedRawLaw
public import Oberwolfach.FiniteProductProjection
public import Oberwolfach.FiniteLawSigmaProjection

@[expose] public section
/-! The degree into a fixed vertex set, with all roots in the ambient graph. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

def physicalRootRestrictedGraph (G:SimpleGraph V) (x:V) (A:Finset V):SimpleGraph V where
  Adj v w:=G.Adj v w ∧ ((v=x ∧ w∈A) ∨ (w=x ∧ v∈A))
  symm:=⟨by intro v w h;exact ⟨h.1.symm,h.2.elim Or.inr Or.inl⟩⟩
  loopless:=⟨by intro v h;exact (G.ne_of_adj h.1) rfl⟩

theorem physicalRootRestrictedGraph_neighbours (G:SimpleGraph V) (x:V) (A:Finset V):
    (physicalRootRestrictedGraph G x A).neighborFinset x=G.neighborFinset x∩A:=by
  ext y
  simp only [SimpleGraph.mem_neighborFinset,Finset.mem_inter]
  change G.Adj x y ∧ ((x=x ∧ y∈A) ∨ (y=x ∧ x∈A)) ↔ G.Adj x y ∧ y∈A
  constructor
  · rintro ⟨h,ha|⟨rfl,_⟩⟩
    · exact ⟨h,ha.2⟩
    · exact ((G.ne_of_adj h) rfl).elim
  · rintro ⟨h,hy⟩;exact ⟨h,Or.inl ⟨rfl,hy⟩⟩

theorem physicalRootRestrictedGraph_colour_degree (G:SimpleGraph V) (x:V) (A:Finset V)
    (c:Sym2 V→Fin 6) (a:Fin 6):
    sampledColourDegree (physicalRootRestrictedGraph G x A) c a x =
      ((G.neighborFinset x∩A).filter (fun y=>c s(x,y)=a)).card := by
  simp only [sampledColourDegree,physicalRootRestrictedGraph_neighbours]

theorem physicalRestrictedColourDegree_all_event
    (G:SimpleGraph V) (A:Finset V) (ρ:Fin 6→ℝ) (hρ:∀ a,0≤ρ a) (hsum:∑ a,ρ a=1)
    (a:Fin 6) (t:ℝ) (ht:0<t):
    1-2*Fintype.card V*Real.exp (-2*t^2/Fintype.card V)≤
      (FiniteLaw.pi (fun _:Sym2 V=>FiniteLaw.categoricalDirection ρ hρ hsum)).probability (fun σ=>∀ x,
        |(((G.neighborFinset x∩A).filter (fun y=>(σ s(x,y)).1=a)).card:ℝ)-
          ρ a*(G.neighborFinset x∩A).card|<t):=by
  let μ:=FiniteLaw.pi (fun _:Sym2 V=>FiniteLaw.categoricalDirection ρ hρ hsum)
  have hh:=finiteLaw_common_event_lower μ (Finset.univ:Finset V)
    (fun x σ=>t≤|(((G.neighborFinset x∩A).filter (fun y=>(σ s(x,y)).1=a)).card:ℝ)-ρ a*(G.neighborFinset x∩A).card|)
    (fun _=>2*Real.exp (-2*t^2/Fintype.card V))
    (fun x _=>by
      have hx:=sampledColourDegree_joint_tail (physicalRootRestrictedGraph G x A) ρ hρ hsum a x ht.le
      simp_rw [physicalRootRestrictedGraph_colour_degree, ← SimpleGraph.card_neighborFinset_eq_degree,
        physicalRootRestrictedGraph_neighbours] at hx
      exact hx)
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Finset.mem_univ,true_implies,not_le] at hh
  convert hh using 1 <;> ring
end Oberwolfach

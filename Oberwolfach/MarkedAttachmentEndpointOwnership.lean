module

public import Oberwolfach.DirectedIncidenceHubAssignments
public import Oberwolfach.MarkedSpokeLoadGrouping

@[expose] public section

/-! A fixed attachment can lie on a rim path only when that path belongs
to its original incidence. This identifies the precise forbidden hub for
the later vertex wheel. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 11000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U A S:Type} [Fintype A] [Fintype S] [DecidableEq V]

 theorem marked_attachment_endpoint_ownership (n:ℕ)
    (src dst:A→V) (row:S→V)
    (a:∀ v,{e:A // dst e=v}≃{s:S // row s=v})
    (d:∀ v,{e:A // src e=v}≃{s:S // row s=v})
    (pr:A→(Fin (n+1)↪V)) (ps:S→(Fin (n+2)↪V))
    (pv:(Σ v,DirectedIncidence src dst v)→Fin (n+2)→V)
    (hr:∀ e f,e≠f→Disjoint (Finset.univ.image (pr e)) (Finset.univ.image (pr f)))
    (hrs:∀ e s,Disjoint (Finset.univ.image (pr e)) (Finset.univ.image (ps s)))
    (hvin:∀ v e,pv ⟨v,Sum.inl e⟩ 0=pr e.val 0∧
      pv ⟨v,Sum.inl e⟩ (Fin.last (n+1))=ps (a v e).val (Fin.last (n+1)))
    (hvout:∀ v e,pv ⟨v,Sum.inr e⟩ 0=ps (d v e).val 0∧
      pv ⟨v,Sum.inr e⟩ (Fin.last (n+1))=pr e.val (Fin.last n)):
    ∀ z:Σ v,DirectedIncidence src dst v,∀ e:A,
      pv z 0∈Finset.univ.image (pr e)∨pv z (Fin.last (n+1))∈Finset.univ.image (pr e)→
      e=directedIncidenceEdge z.2:=by
  have hinj (e f:A) (k:Fin (n+1)) (h:pr f k∈Finset.univ.image (pr e)):e=f:=by
    by_contra hn
    exact Finset.disjoint_left.mp (hr e f hn) h (Finset.mem_image.mpr ⟨k,Finset.mem_univ _,rfl⟩)
  rintro ⟨v,z⟩ e hz
  cases z with
  | inl z=>
    rcases hz with hz|hz
    · rw [(hvin v z).1] at hz
      exact hinj e z.val 0 hz
    · rw [(hvin v z).2] at hz
      exact False.elim (Finset.disjoint_left.mp (hrs e (a v z).val) hz
        (Finset.mem_image.mpr ⟨Fin.last _,Finset.mem_univ _,rfl⟩))
  | inr z=>
    rcases hz with hz|hz
    · rw [(hvout v z).1] at hz
      exact False.elim (Finset.disjoint_left.mp (hrs e (d v z).val) hz
        (Finset.mem_image.mpr ⟨0,Finset.mem_univ _,rfl⟩))
    · rw [(hvout v z).2] at hz
      exact hinj e z.val (Fin.last n) hz

 theorem marked_attachment_rim_hub_avoidance (n:ℕ)
    (src dst:A→V) (hloop:∀ e,dst e≠src e)
    (σ:∀ v,Equiv.Perm (DirectedIncidence src dst v)) (hσ:∀ v i,σ v i≠i)
    (hub:A→U) (hhub:Function.Injective hub)
    (pr:A→(Fin (n+1)↪V)) (pv:(Σ v,DirectedIncidence src dst v)→Fin (n+2)→V)
    (hown:∀ z:Σ v,DirectedIncidence src dst v,∀ e:A,
      pv z 0∈Finset.univ.image (pr e)∨pv z (Fin.last (n+1))∈Finset.univ.image (pr e)→
      e=directedIncidenceEdge z.2):
    ∀ z:Σ v,DirectedIncidence src dst v,∀ e:A,
      pv z 0∈Finset.univ.image (pr e)∨pv z (Fin.last (n+1))∈Finset.univ.image (pr e)→
      hub e≠hub (directedIncidenceEdge (σ z.1 z.2)):=by
  intro z e he hh
  have hh':e=directedIncidenceEdge (σ z.1 z.2):=hhub hh
  exact directed_incidence_assignment_avoids_own_edge hloop z.1 (σ z.1) (hσ z.1) z.2
    (hh'.symm.trans (hown z e he))

end Oberwolfach

module

public import Oberwolfach.PrescribedFamilyStateInitial

@[expose] public section
/-! Relabelling an induced prescribed source graph preserves its physical
edge set. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {X Y:Type} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

theorem prescribed_induced_edge_mk (Q:SimpleGraph X) (A:Finset X) (x y:X):
    s(x,y)∈prescribedInducedSourceEdges Q A ↔ Q.Adj x y ∧ x∈A ∧ y∈A := by
  rw [prescribedInducedSourceEdges,Finset.mem_filter]
  constructor
  · rintro ⟨he,ha⟩
    have hxy:Q.Adj x y:=SimpleGraph.mem_edgeFinset.mp he
    have hx:x∈s(x,y).toFinset:=by simp [Sym2.toFinset_mk_eq]
    have hy:y∈s(x,y).toFinset:=by simp [Sym2.toFinset_mk_eq]
    exact ⟨hxy,ha x hx,ha y hy⟩
  · rintro ⟨hxy,hx,hy⟩
    refine ⟨SimpleGraph.mem_edgeFinset.mpr hxy,?_⟩
    intro z hz
    simp only [Sym2.toFinset_mk_eq,Finset.mem_insert,Finset.mem_singleton] at hz
    rcases hz with rfl|rfl <;> assumption

theorem prescribed_induced_source_edges_relabel (Q:SimpleGraph X) (G:SimpleGraph Y) (f:X↪Y)
    (hAdj:∀ x y,G.Adj (f x) (f y) ↔ Q.Adj x y) (A:Finset X):
    prescribedInducedSourceEdges G (A.image f)=
      (prescribedInducedSourceEdges Q A).image (Sym2.map f) := by
  ext e
  induction e using Sym2.ind with
  | _ u v =>
    rw [prescribed_induced_edge_mk]
    constructor
    · rintro ⟨huv,hu,hv⟩
      obtain ⟨x,hx,rfl⟩:=Finset.mem_image.mp hu
      obtain ⟨y,hy,rfl⟩:=Finset.mem_image.mp hv
      apply Finset.mem_image.mpr
      refine ⟨s(x,y),?_,rfl⟩
      exact (prescribed_induced_edge_mk Q A x y).mpr ⟨(hAdj x y).mp huv,hx,hy⟩
    · intro he
      obtain ⟨e,he,heq⟩:=Finset.mem_image.mp he
      induction e using Sym2.ind with
      | _ x y =>
        have hh:Q.Adj x y ∧ x∈A ∧ y∈A:=(prescribed_induced_edge_mk Q A x y).mp he
        change s(f x,f y)=s(u,v) at heq
        rcases Sym2.eq_iff.mp heq with ⟨hx,hy⟩|⟨hx,hy⟩
        · subst u;subst v
          exact ⟨(hAdj x y).mpr hh.1,Finset.mem_image.mpr ⟨x,hh.2.1,rfl⟩,Finset.mem_image.mpr ⟨y,hh.2.2,rfl⟩⟩
        · subst u;subst v
          exact ⟨((hAdj x y).mpr hh.1).symm,Finset.mem_image.mpr ⟨y,hh.2.2,rfl⟩,Finset.mem_image.mpr ⟨x,hh.2.1,rfl⟩⟩
end Oberwolfach

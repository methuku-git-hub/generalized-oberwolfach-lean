module

public import Mathlib.Combinatorics.SimpleGraph.Finite

@[expose] public section
/-! Two-vertex buffers separate the interior vertices of disjoint paths in a
2-regular graph. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem regular_two_buffered_path_interiors_nonadjacent
    {V I:Type*} [Fintype V] [DecidableEq V]
    (G:SimpleGraph V) (hG:G.IsRegularOfDegree 2)
    (n:I→ℕ) (ext:∀i,Fin (n i+5)↪V) (inner:∀i,Fin (n i+1)↪V)
    (hinner:∀i k,inner i k=ext i ⟨k.val+2,by omega⟩)
    (hstep:∀i (k:Fin (n i+4)),
      G.Adj (ext i ⟨k.val,by omega⟩) (ext i ⟨k.val+1,by omega⟩))
    (hdis:∀i j,i≠j→Disjoint (Finset.univ.image (ext i)) (Finset.univ.image (ext j))):
    ∀i j,i≠j→∀(p:Fin (n i+1)) (q:Fin (n j+1)),¬G.Adj (inner i p) (inner j q) := by
  classical
  intro i j hij p q hadj
  let x:=inner i p
  let y:=inner j q
  let u:=ext i ⟨p.val+1,by omega⟩
  let v:=ext i ⟨p.val+3,by omega⟩
  have hx:x=ext i ⟨p.val+2,by omega⟩:=hinner i p
  have hxu:G.Adj x u:=by
    rw [hx]
    exact (hstep i ⟨p.val+1,by omega⟩).symm
  have hxv:G.Adj x v:=by
    rw [hx]
    exact hstep i ⟨p.val+2,by omega⟩
  have huv:u≠v:=by
    intro h
    have hh: (⟨p.val+1,by omega⟩:Fin (n i+5))=⟨p.val+3,by omega⟩:=(ext i).injective h
    have hh':p.val+1=p.val+3:=congrArg Fin.val hh
    omega
  have hsub:({u,v}:Finset V)⊆G.neighborFinset x:=by
    intro z hz
    simp only [Finset.mem_insert,Finset.mem_singleton] at hz
    rcases hz with rfl|rfl <;> simpa using (show G.Adj x _ from by first | exact hxu | exact hxv)
  have hcard:(G.neighborFinset x).card=2:=by simpa using hG x
  have heq:G.neighborFinset x={u,v}:=by
    apply (Finset.eq_of_subset_of_card_le hsub ?_).symm
    simp [hcard,huv]
  have hy:G.Adj x y:=hadj
  have hyn:y∈G.neighborFinset x:=by simpa using hy
  rw [heq] at hyn
  have hyext:y∈Finset.univ.image (ext i):=by
    simp only [Finset.mem_insert,Finset.mem_singleton] at hyn
    rcases hyn with hu|hv
    · rw [hu]; exact Finset.mem_image.mpr ⟨⟨p.val+1,by omega⟩,Finset.mem_univ _,rfl⟩
    · rw [hv]; exact Finset.mem_image.mpr ⟨⟨p.val+3,by omega⟩,Finset.mem_univ _,rfl⟩
  have hyj:y∈Finset.univ.image (ext j):=by
    change inner j q∈Finset.univ.image (ext j)
    rw [hinner j q]
    exact Finset.mem_image.mpr ⟨⟨q.val+2,by omega⟩,Finset.mem_univ _,rfl⟩
  exact Finset.disjoint_left.mp (hdis i j hij) hyext hyj
theorem regular_two_buffered_path_edge_cover
    {V I:Type*} [Fintype V] [DecidableEq V] [DecidableEq I]
    (G:SimpleGraph V) (hG:G.IsRegularOfDegree 2)
    (n:I→ℕ) (ext:∀i,Fin (n i+5)↪V) (inner:∀i,Fin (n i+1)↪V)
    (hinner:∀i k,inner i k=ext i ⟨k.val+2,by omega⟩)
    (hstep:∀i (k:Fin (n i+4)),
      G.Adj (ext i ⟨k.val,by omega⟩) (ext i ⟨k.val+1,by omega⟩))
    (hdis:∀i j,i≠j→Disjoint (Finset.univ.image (ext i)) (Finset.univ.image (ext j)))
    (A:Finset I):
    ∀x y,x∈A.biUnion (fun i=>Finset.univ.image (inner i))→
      y∈A.biUnion (fun i=>Finset.univ.image (inner i))→G.Adj x y→
      ∃i∈A,x∈Finset.univ.image (inner i) ∧ y∈Finset.univ.image (inner i):=by
  classical
  intro x y hx hy hxy
  obtain ⟨i,hi,hxi⟩:=Finset.mem_biUnion.mp hx
  obtain ⟨j,hj,hyj⟩:=Finset.mem_biUnion.mp hy
  obtain ⟨p,_,hp⟩:=Finset.mem_image.mp hxi
  obtain ⟨q,_,hq⟩:=Finset.mem_image.mp hyj
  by_cases hij:i=j
  · subst j
    exact ⟨i,hi,hxi,hyj⟩
  · have hn:=regular_two_buffered_path_interiors_nonadjacent G hG n ext inner hinner hstep hdis i j hij p q
    apply False.elim
    apply hn
    simpa only [hp,hq] using hxy
end Oberwolfach

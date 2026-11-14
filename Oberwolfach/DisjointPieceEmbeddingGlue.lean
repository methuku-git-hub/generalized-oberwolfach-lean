module

public import Mathlib.Combinatorics.SimpleGraph.Finite

@[expose] public section
/-! Glue embeddings on disjoint finite pieces, preserving their values and
all graph edges lying within one of the pieces. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
open scoped BigOperators

theorem disjoint_piece_embeddings_glue
    {X V J:Type*} [DecidableEq X] [DecidableEq J]
    (I:Finset J) (S:J→Finset X)
    (hS:∀i∈I,∀j∈I,i≠j→Disjoint (S i) (S j))
    (f:∀i,{x // x∈S i}↪V)
    (hf:∀i∈I,∀j∈I,i≠j→Disjoint (Set.range (f i)) (Set.range (f j))):
    ∃φ:{x // x∈I.biUnion S}↪V,
      ∀i (hi:i∈I) (x:X) (hx:x∈S i),
        φ ⟨x,Finset.mem_biUnion.mpr ⟨i,hi,hx⟩⟩=f i ⟨x,hx⟩ := by
  classical
  let idx (x:{x // x∈I.biUnion S}):J:=Classical.choose (Finset.mem_biUnion.mp x.property)
  have hidx (x:{x // x∈I.biUnion S}):idx x∈I ∧ x.val∈S (idx x):=
    Classical.choose_spec (Finset.mem_biUnion.mp x.property)
  have map_eq (i j:J) (hij:i=j) (x:X) (hxi:x∈S i) (hxj:x∈S j):
      f i ⟨x,hxi⟩=f j ⟨x,hxj⟩:=by
    subst j
    rfl
  let φ (x:{x // x∈I.biUnion S}):V:=f (idx x) ⟨x.val,(hidx x).2⟩
  have hinj:Function.Injective φ:=by
    intro x y hxy
    have hij:idx x=idx y:=by
      by_contra hne
      have hx:φ x∈Set.range (f (idx x)):=⟨⟨x.val,(hidx x).2⟩,rfl⟩
      have hy:φ y∈Set.range (f (idx y)):=⟨⟨y.val,(hidx y).2⟩,rfl⟩
      have hy':φ x∈Set.range (f (idx y)):=by rw [hxy];exact hy
      exact Set.disjoint_left.mp (hf (idx x) (hidx x).1 (idx y) (hidx y).1 hne) hx hy'
    apply Subtype.ext
    have hyx:y.val∈S (idx x):=by simpa only [hij] using (hidx y).2
    have hy':f (idx x) ⟨y.val,hyx⟩=f (idx y) ⟨y.val,(hidx y).2⟩:=
      map_eq (idx x) (idx y) hij y.val hyx (hidx y).2
    change f (idx x) ⟨x.val,(hidx x).2⟩=f (idx y) ⟨y.val,(hidx y).2⟩ at hxy
    have hsub: (⟨x.val,(hidx x).2⟩:{w:X // w∈S (idx x)})=⟨y.val,hyx⟩:=
      (f (idx x)).injective (hxy.trans hy'.symm)
    exact congrArg (fun (z:{w:X // w∈S (idx x)})=>z.val) hsub
  refine ⟨⟨φ,hinj⟩,?_⟩
  intro i hi x hx
  let z:{x // x∈I.biUnion S}:=⟨x,Finset.mem_biUnion.mpr ⟨i,hi,hx⟩⟩
  have heq:idx z=i:=by
    by_contra hne
    exact Finset.disjoint_left.mp (hS (idx z) (hidx z).1 i hi hne) (hidx z).2 hx
  change φ z=f i ⟨x,hx⟩
  exact map_eq (idx z) i heq x (hidx z).2 hx

theorem disjoint_piece_graph_embeddings_glue
    {X V J:Type*} [DecidableEq X] [DecidableEq J]
    (I:Finset J) (S:J→Finset X)
    (hS:∀i∈I,∀j∈I,i≠j→Disjoint (S i) (S j))
    (f:∀i,{x // x∈S i}↪V)
    (hf:∀i∈I,∀j∈I,i≠j→Disjoint (Set.range (f i)) (Set.range (f j)))
    (G:SimpleGraph X) (H:SimpleGraph V)
    (hcover:∀x y,x∈I.biUnion S→y∈I.biUnion S→G.Adj x y→
      ∃i∈I,x∈S i ∧ y∈S i)
    (hlocal:∀i∈I,∀x y (hx:x∈S i) (hy:y∈S i),G.Adj x y→H.Adj (f i ⟨x,hx⟩) (f i ⟨y,hy⟩)):
    ∃φ:{x // x∈I.biUnion S}↪V,
      (∀i (hi:i∈I) (x:X) (hx:x∈S i),
        φ ⟨x,Finset.mem_biUnion.mpr ⟨i,hi,hx⟩⟩=f i ⟨x,hx⟩) ∧
      (∀x y,G.Adj x.val y.val→H.Adj (φ x) (φ y)) := by
  obtain ⟨φ,hφ⟩:=disjoint_piece_embeddings_glue I S hS f hf
  refine ⟨φ,hφ,?_⟩
  intro x y hxy
  obtain ⟨i,hi,hx,hy⟩:=hcover x.val y.val x.property y.property hxy
  have hx':φ x=f i ⟨x.val,hx⟩:=by simpa using hφ i hi x.val hx
  have hy':φ y=f i ⟨y.val,hy⟩:=by simpa using hφ i hi y.val hy
  rw [hx',hy']
  exact hlocal i hi x.val y.val hx hy hxy
end Oberwolfach

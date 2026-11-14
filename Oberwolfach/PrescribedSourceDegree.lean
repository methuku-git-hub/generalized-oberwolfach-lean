module

public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Basic.Real.Basic

@[expose] public section
/-! A simple underlying graph has degree at most two when the directed
source has at most one predecessor and one successor at each vertex. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {X:Type} [Fintype X] [DecidableEq X]

theorem prescribed_source_degree_from_directions (Q:SimpleGraph X) (D:X→X→Prop)
    (hrep:∀ x y,Q.Adj x y↔D x y ∨ D y x)
    (hout:∀ x y z,D x y→D x z→y=z)
    (hin:∀ x y z,D y x→D z x→y=z):
    ∀ x,Q.degree x≤2 := by
  intro x
  let out:X:=if h:∃ y,D x y then Classical.choose h else x
  let inn:X:=if h:∃ y,D y x then Classical.choose h else x
  have hsubset:Q.neighborFinset x⊆{out,inn}:=by
    intro y hy
    have hy':Q.Adj x y:=(SimpleGraph.mem_neighborFinset Q x y).mp hy
    rcases (hrep x y).mp hy' with hy'|hy'
    · have he:∃ z,D x z:=⟨y,hy'⟩
      have ho:D x out:=by simp only [out,dif_pos he];exact Classical.choose_spec he
      have hyout:y=out:=hout x y out hy' ho
      simp [hyout]
    · have he:∃ z,D z x:=⟨y,hy'⟩
      have hi:D inn x:=by simp only [inn,dif_pos he];exact Classical.choose_spec he
      have hyin:y=inn:=hin x y inn hy' hi
      simp [hyin]
  calc
    Q.degree x=(Q.neighborFinset x).card:=rfl
    _≤({out,inn}:Finset X).card:=Finset.card_le_card hsubset
    _≤({inn}:Finset X).card+1:=Finset.card_insert_le out {inn}
    _=2:=by simp
end Oberwolfach

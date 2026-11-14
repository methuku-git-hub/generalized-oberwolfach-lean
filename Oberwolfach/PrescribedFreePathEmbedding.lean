module

public import Oberwolfach.PrescribedZipPositions
public import Oberwolfach.PrescribedPathConsecutive

@[expose] public section
/-! Ordered source vertices and a selected host path give an injective
extension preserving the path's consecutive directed edges. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {X V:Type} [Fintype V] [DecidableEq X] [DecidableEq V]

theorem prescribed_free_path_from_ordered_vertices
    (as:List X) (x:V) (xs:List V) (hlen:as.length=(x::xs).length)
    (ha:as.Nodup) (hb:(x::xs).Nodup) (A:Finset X) (f:X→V)
    (hinj:Set.InjOn f A) (hsource:∀ a∈as,a∉A)
    (htarget:∀ z∈x::xs,z∉A.image f)
    (D:V→V→Prop) (F:SimpleGraph V) (hpath:DirectedPathFrom D F true x xs):
    let g:=updatePairedImages f (as.zip (x::xs));
    Set.InjOn g (↑(A∪as.toFinset):Set X) ∧ (∀ a∈A,g a=f a) ∧
    (∀ i:ℕ,∀ hi:i+1<as.length,
      D (g (as[i]'(by omega))) (g (as[i+1]'(by omega))) ∧
      ¬F.Adj (g (as[i]'(by omega))) (g (as[i+1]'(by omega)))) := by
  let g:=updatePairedImages f (as.zip (x::xs))
  have hbase:=prescribed_embedding_zip_update as (x::xs) hlen ha hb A f hinj hsource htarget
  refine ⟨hbase.1,hbase.2.1,?_⟩
  intro i hi
  have hi0:i<as.length:=by omega
  have hi1:i+1<as.length:=hi
  have hh0:=prescribed_embedding_zip_update_at_position as (x::xs) hlen ha hb A f hinj hsource htarget ⟨i,hi0⟩
  have hh1:=prescribed_embedding_zip_update_at_position as (x::xs) hlen ha hb A f hinj hsource htarget ⟨i+1,hi1⟩
  have htargetlen:i+1<(x::xs).length:=by omega
  have hedges:=prescribed_path_consecutive D F true xs x hpath i htargetlen
  simp only [Bool.true_eq,if_true] at hedges
  change D (g (as[i])) (g (as[i+1])) ∧ ¬F.Adj (g (as[i])) (g (as[i+1]))
  change g (as[i])=(x::xs)[i] at hh0
  change g (as[i+1])=(x::xs)[i+1] at hh1
  rw [hh0,hh1]
  exact hedges
end Oberwolfach

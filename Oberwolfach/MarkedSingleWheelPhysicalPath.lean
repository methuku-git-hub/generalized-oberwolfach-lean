module

public import Oberwolfach.FiniteSequenceSimpleWalk
public import Oberwolfach.MarkedWheels

@[expose] public section
/-! A marked wheel's rim is a simple physical path from its marked root
 to the successor of that root, before concatenation along intervals. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_single_wheel_physical_path
    {V E K:Type*} (G:SimpleGraph V) (tail head:E→V) (ktail khead:K→V)
    (m b:ℕ) (π:Equiv.Perm V) (hb:1≤b)
    (C:MarkedCycleTuple tail head ktail khead m π b)
    (hroot:π (C.val 0)≠C.val 0)
    (hE:∀e:E,G.Adj (tail e) (head e))
    (hK:∀e:K,G.Adj (ktail e) (π (khead e))):
    ∃f:Fin ((m+1)+1)↪V,
      (∀i:Fin (m+1),f i.castSucc=C.val i) ∧ f (Fin.last (m+1))=π (C.val 0) ∧
      (∀j:Fin (m+1),G.Adj (f ⟨j.val,by omega⟩) (f ⟨j.val+1,by omega⟩)) := by
  have havoid:π (C.val 0)∉Set.range C.val:=by
    rintro ⟨i,hi⟩
    by_cases h:i=0
    · subst i
      exact hroot hi.symm
    · have hne:(0:Fin (m+1))≠i:=Ne.symm h
      exact (permutationSeparated_successor_avoid π b hb C.val C.property.1 0 i hne) hi.symm
  let f:Fin ((m+1)+1)↪V:=⟨Fin.snoc C.val (π (C.val 0)),
    Fin.snoc_injective_of_injective (permutationSeparated_injective π b C.val C.property.1) havoid⟩
  have hadj:∀j:Fin (m+1),G.Adj (f ⟨j.val,by omega⟩) (f ⟨j.val+1,by omega⟩):=by
    intro j
    change G.Adj (f j.castSucc) (f j.succ)
    refine Fin.lastCases ?_ (fun i=>?_) j
    · obtain ⟨e,he₁,he₂⟩:=C.property.2.2
      have h:=hK e
      rw [he₁,he₂] at h
      simpa [f] using h
    · obtain ⟨e,he₁,he₂⟩:=C.property.2.1 i
      have h:=hE e
      rw [he₁,he₂] at h
      have hi:i.castSucc.succ=i.succ.castSucc:=by apply Fin.ext; rfl
      simpa only [f, Function.Embedding.coeFn_mk, hi, Fin.snoc_castSucc] using h
  refine ⟨f,?_,?_,hadj⟩
  · intro i; simp only [f, Function.Embedding.coeFn_mk, Fin.snoc_castSucc]
  · simp only [f, Function.Embedding.coeFn_mk, Fin.snoc_last]
end Oberwolfach

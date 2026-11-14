module

public import Oberwolfach.LongReservedPrescribedPaths

@[expose] public section
/-! A finite injective adjacent sequence is a graph-theoretic simple path. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem finite_sequence_simple_walk
    {V:Type*} (G:SimpleGraph V) (n:ℕ) (f:Fin (n+1)↪V)
    (hadj:∀j:Fin n,G.Adj (f ⟨j.val,by omega⟩) (f ⟨j.val+1,by omega⟩)):
    ∃p:G.Walk (f ⟨0,by omega⟩) (f ⟨n,by omega⟩),
      p.IsPath ∧ p.length=n ∧ p.support=List.ofFn f := by
  induction n with
  | zero =>
    refine ⟨SimpleGraph.Walk.nil,SimpleGraph.Walk.IsPath.nil, rfl, ?_⟩
    simp [List.ofFn_succ]
  | succ n ih =>
    let tail:Fin (n+1)↪V := (Fin.succEmb (n+1)).trans f
    have ht:∀j:Fin n,G.Adj (tail ⟨j.val,by omega⟩) (tail ⟨j.val+1,by omega⟩):=by
      intro j
      have hh:=hadj ⟨j.val+1,by omega⟩
      simpa [tail,Fin.succEmb,Fin.succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh
    obtain ⟨p,hp,hlen,hsupp⟩:=ih tail ht
    have h0:G.Adj (f ⟨0,by omega⟩) (tail ⟨0,by omega⟩):=by
      simpa [tail,Fin.succEmb,Fin.succ] using hadj ⟨0,by omega⟩
    have hnot:f ⟨0,by omega⟩∉p.support:=by
      rw [hsupp]
      have hnod: (List.ofFn f).Nodup:=List.nodup_ofFn_ofInjective f.injective
      have ht':List.ofFn f=f ⟨0,by omega⟩::List.ofFn tail:=by
        simp [List.ofFn_succ,tail,Fin.succEmb]
      rw [ht'] at hnod
      exact (List.nodup_cons.mp hnod).1
    refine ⟨p.cons h0, hp.cons hnot, ?_, ?_⟩
    · simpa [hlen]
    · rw [SimpleGraph.Walk.support_cons,hsupp]
      simp [List.ofFn_succ,tail,Fin.succEmb]
end Oberwolfach

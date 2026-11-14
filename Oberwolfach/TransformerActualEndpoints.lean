module

public import Oberwolfach.CanonicalEdgeDarts
public import Oberwolfach.TransformerPathEndpoints

@[expose] public section

/-! Root adjacencies of the actual endpoints, with one fixed orientation
of each undirected edge. No independent endpoint choices are assumed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V]

 def rimIncidenceEquiv (G:SimpleGraph V):
    (Σ v,G.neighborSet v)≃(G.edgeFinset×Fin 2):=
  (neighborSigmaDartEquiv G).trans (canonicalEdgeDartEquiv G).symm

 theorem rimIncidenceEquiv_edge (G:SimpleGraph V) (d:Σ v,G.neighborSet v):
    (rimIncidenceEquiv G d).1.val=s(d.1,d.2.val):=
  canonicalEdgeDartEquiv_inverse_edge G (neighborSigmaDartEquiv G d)

 theorem rimIncidenceEquiv_root (G:SimpleGraph V) (d:Σ v,G.neighborSet v):
    d.1=if (rimIncidenceEquiv G d).2=0 then (rimIncidenceEquiv G d).1.val.out.1
      else (rimIncidenceEquiv G d).1.val.out.2:=by
  have hh:(canonicalEdgeDartEquiv G) (rimIncidenceEquiv G d)=neighborSigmaDartEquiv G d:=
    (canonicalEdgeDartEquiv G).apply_symm_apply _
  have hfst:=congrArg (fun x:G.Dart=>x.fst) hh
  change (canonicalEdgeDart G (rimIncidenceEquiv G d)).fst=d.1 at hfst
  unfold canonicalEdgeDart at hfst
  split_ifs at hfst ⊢ <;> exact hfst.symm

 theorem actual_rim_endpoint_adjacency (G Q:SimpleGraph V) (φ:V→V)
    (p:G.edgeFinset→(Σ a:V,Σ c:V,Q.Walk a c))
    (hends:∀ e,Q.Adj e.val.out.1 (p e).1 ∧ Q.Adj (φ e.val.out.1) (p e).1 ∧
      Q.Adj e.val.out.2 (p e).2.1 ∧ Q.Adj (φ e.val.out.2) (p e).2.1):
    ∀ d:Σ v,G.neighborSet v,
      Q.Adj d.1 (graphPathEndpoint (p (rimIncidenceEquiv G d).1) (rimIncidenceEquiv G d).2) ∧
      Q.Adj (φ d.1) (graphPathEndpoint (p (rimIncidenceEquiv G d).1) (rimIncidenceEquiv G d).2):=by
  intro d
  have hroot:=rimIncidenceEquiv_root G d
  have hend:=hends (rimIncidenceEquiv G d).1
  unfold graphPathEndpoint
  split_ifs with he
  · simp only [he,ite_true] at hroot
    rw [hroot]
    exact ⟨hend.1,hend.2.1⟩
  · simp only [he,ite_false] at hroot
    rw [hroot]
    exact ⟨hend.2.2.1,hend.2.2.2⟩

 def incidenceShiftEquiv (G:SimpleGraph V) (σ:∀ v,Equiv.Perm (G.neighborSet v)):
    Equiv.Perm (Σ v,G.neighborSet v) where
  toFun d:=⟨d.1,σ d.1 d.2⟩
  invFun d:=⟨d.1,(σ d.1).symm d.2⟩
  left_inv:=by rintro ⟨v,w⟩;simp
  right_inv:=by rintro ⟨v,w⟩;simp

 def shiftedIncidenceEquiv (G:SimpleGraph V) (σ:∀ v,Equiv.Perm (G.neighborSet v)):
    (Σ v,G.neighborSet v)≃(G.edgeFinset×Fin 2):=
  (incidenceShiftEquiv G σ).trans (rimIncidenceEquiv G)

 theorem shiftedIncidenceEquiv_edge (G:SimpleGraph V) (σ:∀ v,Equiv.Perm (G.neighborSet v))
    (d:Σ v,G.neighborSet v):
    (shiftedIncidenceEquiv G σ d).1.val=s(d.1,(σ d.1 d.2).val):=
  rimIncidenceEquiv_edge G (incidenceShiftEquiv G σ d)

 def transformerHubAttachments (G:SimpleGraph V) (σ:∀ v,Equiv.Perm (G.neighborSet v))
    (a z:(Σ v,G.neighborSet v)→V) (e:G.edgeFinset):Finset V:=
  Finset.univ.biUnion (fun i:Fin 2=>
    {a ((shiftedIncidenceEquiv G σ).symm (e,i)),z ((shiftedIncidenceEquiv G σ).symm (e,i))})

 theorem transformerHubAttachments_card (G:SimpleGraph V) (σ:∀ v,Equiv.Perm (G.neighborSet v))
    (a z:(Σ v,G.neighborSet v)→V) (e:G.edgeFinset):
    (transformerHubAttachments G σ a z e).card≤4:=by
  apply (Finset.card_biUnion_le).trans
  calc
    _ ≤ ∑ _i:Fin 2,(2:ℕ):=Finset.sum_le_sum (fun i _=>by
      simpa using Finset.card_insert_le (a ((shiftedIncidenceEquiv G σ).symm (e,i)))
        ({z ((shiftedIncidenceEquiv G σ).symm (e,i))}:Finset V))
    _ = 4:=by simp

 theorem transformerHubAttachments_contains (G:SimpleGraph V) (σ:∀ v,Equiv.Perm (G.neighborSet v))
    (a z:(Σ v,G.neighborSet v)→V) (d:Σ v,G.neighborSet v):
    a d∈transformerHubAttachments G σ a z (shiftedIncidenceEquiv G σ d).1 ∧
    z d∈transformerHubAttachments G σ a z (shiftedIncidenceEquiv G σ d).1:=by
  have he:(shiftedIncidenceEquiv G σ).symm
      ((shiftedIncidenceEquiv G σ d).1,(shiftedIncidenceEquiv G σ d).2)=d:=
    (shiftedIncidenceEquiv G σ).symm_apply_apply d
  constructor <;> apply Finset.mem_biUnion.mpr
  · exact ⟨(shiftedIncidenceEquiv G σ d).2,Finset.mem_univ _,by rw [he];simp⟩
  · exact ⟨(shiftedIncidenceEquiv G σ d).2,Finset.mem_univ _,by rw [he];simp⟩

end Oberwolfach

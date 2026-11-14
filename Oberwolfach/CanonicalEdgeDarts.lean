module

public import Oberwolfach.CanonicalGraphPairs
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum

@[expose] public section

/-! A fixed, shared orientation identifies the two ends of every actual
undirected edge with its two directed incidences. This is used to attach
the selected path endpoints to the correct old vertices. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V]

 theorem edge_out_adj (G:SimpleGraph V) (e:G.edgeFinset):G.Adj e.val.out.1 e.val.out.2:=by
  have he:s(e.val.out.1,e.val.out.2)=e.val:=by rw [Sym2.mk];exact e.val.out_eq
  exact SimpleGraph.mem_edgeFinset.mp (he.symm ▸ e.property)

 def canonicalEdgeDart (G:SimpleGraph V) (e:G.edgeFinset×Fin 2):G.Dart:=
  if e.2=0 then ⟨(e.1.val.out.1,e.1.val.out.2),edge_out_adj G e.1⟩
  else ⟨(e.1.val.out.2,e.1.val.out.1),(edge_out_adj G e.1).symm⟩

 theorem canonicalEdgeDart_edge (G:SimpleGraph V) (e:G.edgeFinset×Fin 2):
    (canonicalEdgeDart G e).edge=e.1.val:=by
  have he:s(e.1.val.out.1,e.1.val.out.2)=e.1.val:=by rw [Sym2.mk];exact e.1.val.out_eq
  unfold canonicalEdgeDart
  split_ifs
  · exact he
  · change s(e.1.val.out.2,e.1.val.out.1)=e.1.val
    rw [Sym2.eq_swap];exact he

 theorem canonicalEdgeDart_bijective (G:SimpleGraph V):Function.Bijective (canonicalEdgeDart G):=by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  constructor
  · rintro ⟨e,i⟩ ⟨f,j⟩ he
    have hef:e=f:=by
      apply Subtype.ext
      have hh:=congrArg SimpleGraph.Dart.edge he
      simpa only [canonicalEdgeDart_edge] using hh
    subst f
    have hn:= (edge_out_adj G e).ne
    have hh:=congrArg (fun d:G.Dart=>d.fst) he
    fin_cases i <;> fin_cases j <;> simp [canonicalEdgeDart] at hh ⊢
    · exact (hn hh).elim
    · exact (hn hh.symm).elim
  · rw [Fintype.card_prod,Fintype.card_fin,Fintype.card_coe,G.dart_card_eq_twice_card_edges,Nat.mul_comm]

 def canonicalEdgeDartEquiv (G:SimpleGraph V):(G.edgeFinset×Fin 2)≃G.Dart:=
  Equiv.ofBijective (canonicalEdgeDart G) (canonicalEdgeDart_bijective G)

 def neighborSigmaDartEquiv (G:SimpleGraph V):(Σ v,G.neighborSet v)≃G.Dart where
  toFun p:=⟨(p.1,p.2.val),p.2.property⟩
  invFun d:=⟨d.fst,⟨d.snd,d.adj⟩⟩
  left_inv:=by intro p;cases p;rfl
  right_inv:=by intro d;cases d;rfl

 theorem canonicalEdgeDartEquiv_inverse_edge (G:SimpleGraph V) (d:G.Dart):
    ((canonicalEdgeDartEquiv G).symm d).1.val=d.edge:=by
  have hh:=canonicalEdgeDart_edge G ((canonicalEdgeDartEquiv G).symm d)
  have hh':canonicalEdgeDart G ((canonicalEdgeDartEquiv G).symm d)=d:=
    (canonicalEdgeDartEquiv G).apply_symm_apply d
  rw [hh'] at hh
  exact hh.symm

end Oberwolfach

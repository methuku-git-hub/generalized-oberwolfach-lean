module

public import Oberwolfach.SeparatedCycleRepresentations
public import Oberwolfach.OrderedCycleHostMembership

@[expose] public section
/-! Partition separated host tuples by their underlying physical cycle. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V]

abbrev SeparatedHostCycle (P:SimpleGraph V) (π:Equiv.Perm V) (b r:ℕ):=
  {H:SimpleGraph V // IsEmbeddedCycle H r ∧ H≤P ∧
    ∀ x∈H.support,∀ y∈H.support,x≠y→¬PermutationClose π b x y}

abbrev SeparatedHostCycleTuple (P:SimpleGraph V) (π:Equiv.Perm V) (b r:ℕ):=
  {C:Fin r→V // PermutationSeparated π b C ∧ ∀ i,P.Adj (C i) (C (cycleNext i))}

def separatedTupleCycle {P:SimpleGraph V} {π:Equiv.Perm V} {b n:ℕ} (hn:1≤n)
    (C:SeparatedHostCycleTuple P π b (n+2)):SeparatedHostCycle P π b (n+2):=by
  let f:Fin (n+2)↪V:=⟨C.val,permutationSeparated_injective π b C.val C.property.1⟩
  refine ⟨(SimpleGraph.cycleGraph (n+2)).map f,⟨by omega,f,rfl⟩,?_,?_⟩
  · exact (cycleGraph_map_le_iff (n+2) (by omega) f P).mpr C.property.2
  · rw [cycle_map_support (by omega) f]
    exact (permutationSeparated_iff_range π b f f.injective).mp C.property.1

def separatedTupleToSigma {P:SimpleGraph V} {π:Equiv.Perm V} {b n:ℕ} (hn:1≤n)
    (C:SeparatedHostCycleTuple P π b (n+2)):
    Σ H:SeparatedHostCycle P π b (n+2),OrderedCycleRepresentations H.val (n+2):=by
  let f:Fin (n+2)↪V:=⟨C.val,permutationSeparated_injective π b C.val C.property.1⟩
  exact ⟨separatedTupleCycle hn C,⟨f,rfl⟩⟩

def separatedSigmaToTuple {P:SimpleGraph V} {π:Equiv.Perm V} {b n:ℕ} (hn:1≤n)
    (p:Σ H:SeparatedHostCycle P π b (n+2),OrderedCycleRepresentations H.val (n+2)):
    SeparatedHostCycleTuple P π b (n+2):=by
  let H:=p.1
  let f:=p.2
  refine ⟨f.val,?_,?_⟩
  · exact (orderedCycle_separation_iff_support H.val n hn π b f).mpr H.property.2.2
  · have hf:(SimpleGraph.cycleGraph (n+2)).map f.val≤P:=by rw [←f.property];exact H.property.2.1
    exact (cycleGraph_map_le_iff (n+2) (by omega) f.val P).mp hf

def separatedHostCycleTupleEquiv {P:SimpleGraph V} {π:Equiv.Perm V} {b n:ℕ} (hn:1≤n):
    SeparatedHostCycleTuple P π b (n+2)≃
      (Σ H:SeparatedHostCycle P π b (n+2),OrderedCycleRepresentations H.val (n+2)) where
  toFun:=separatedTupleToSigma hn
  invFun:=separatedSigmaToTuple hn
  left_inv C:=by apply Subtype.ext;rfl
  right_inv p:=by
    obtain ⟨H,f⟩:=p
    have he:(separatedTupleCycle hn (separatedSigmaToTuple hn ⟨H,f⟩))=H:=by
      apply Subtype.ext
      exact f.property.symm
    change (separatedTupleToSigma hn (separatedSigmaToTuple hn ⟨H,f⟩)).1=H at he
    apply Sigma.ext he
    apply (Subtype.heq_iff_coe_eq (fun z=>by rw [he])).mpr
    rfl
end Oberwolfach

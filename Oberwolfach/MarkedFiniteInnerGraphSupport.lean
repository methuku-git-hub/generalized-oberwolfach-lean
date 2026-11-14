module

public import Oberwolfach.MarkedFinitePhysicalDeletion

@[expose] public section

/-! Physical support of an inner typed arc set, including the permutation
on marked heads. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_finite_inner_graph_support
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (σ:RawMarkedOutcome V U Γ Color)
    (I:Finset V) (J:Finset U) (hI:∀ x,π x∈I↔x∈I):
    let E:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let K:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true;
    ∀ (A:Finset (E⊕K)) (S:Finset (V×U)),
    (∀ a∈A,Sum.elim (fun e=>e.val.1) (fun e=>e.val.1) a∈I∧
      Sum.elim (fun e=>e.val.2) (fun e=>e.val.2) a∈I)→
    (∀ z∈S,z.1∈I∧z.2∈J)→
    (∀ x y,(markedSampleArcSetGraph P π d σ A).Adj x y→x∈I∧y∈I)∧
    (∀ x u,(markedFiniteSpokeGraph S).Adj (Sum.inl x) (Sum.inr u)→x∈I∧u∈J):=by
  intro E K A S hA hS
  constructor
  · intro x y hxy
    obtain ⟨a,ha,he⟩:=Finset.mem_image.mp hxy.2
    have heI:∀ z∈markedPhysicalEdge (fun e:E=>e.val.1) (fun e=>e.val.2)
        (fun e:K=>e.val.1) (fun e=>e.val.2) π a,z∈I:=by
      have hh:=hA a ha
      cases a with
      | inl a=>
        intro z hz
        have hz':z=a.val.1∨z=a.val.2:=by simpa only [markedPhysicalEdge,Sum.elim_inl,Finset.mem_insert,Finset.mem_singleton] using hz
        rcases hz' with rfl|rfl
        · exact hh.1
        · exact hh.2
      | inr a=>
        intro z hz
        have hz':z=a.val.1∨z=π a.val.2:=by simpa only [markedPhysicalEdge,Sum.elim_inr,Finset.mem_insert,Finset.mem_singleton] using hz
        rcases hz' with rfl|rfl
        · exact hh.1
        · exact (hI _).mpr hh.2
    rw [he] at heI
    exact ⟨heI x (by simp),heI y (by simp)⟩
  · intro x u h
    exact hS (x,u) ((markedFiniteSpokeGraph_adj S x u).mp h)

end Oberwolfach

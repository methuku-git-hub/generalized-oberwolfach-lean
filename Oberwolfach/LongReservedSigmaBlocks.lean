module

public import Oberwolfach.LongReservedComponentBlocks

@[expose] public section
/-! Blocks in distinct specified components have disjoint vertex images. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V I:Type*} [Fintype V] [DecidableEq V] [Fintype I]
    (G:SimpleGraph V) (components:I↪G.ConnectedComponent) (c d:ℕ)

abbrev LongReservedBlockIndex := Σi:I,Fin (Fintype.card (components i)/(c*d+5))

theorem long_reserved_sigma_block_fit (q:LongReservedBlockIndex G components c d):
    (c*d+5)*(q.2.val+1)≤Fintype.card (components q.1) := by
  have hpos:0<c*d+5:=by omega
  have hh:q.2.val+1≤Fintype.card (components q.1)/(c*d+5):=by have hq:=q.2.isLt;omega
  simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le hpos).mp hh

def longReservedSigmaBlock
    (e:∀i:I,SimpleGraph.cycleGraph (Fintype.card (components i)) ≃g (components i).toSimpleGraph)
    (q:LongReservedBlockIndex G components c d) (t:ℕ) (ht:t≤d):Fin (c*t+5)↪V :=
  (longReservedComponentBlock G (components q.1) (e q.1) c d t q.2.val ht
    (long_reserved_sigma_block_fit G components c d q)).trans (Function.Embedding.subtype _)

theorem long_reserved_sigma_block_edges
    (e:∀i:I,SimpleGraph.cycleGraph (Fintype.card (components i)) ≃g (components i).toSimpleGraph)
    (hthree:∀i,3≤Fintype.card (components i))
    (q:LongReservedBlockIndex G components c d) (t:ℕ) (ht:t≤d):
    ∀j:Fin (c*t+4),G.Adj
      (longReservedSigmaBlock G components c d e q t ht ⟨j.val,by omega⟩)
      (longReservedSigmaBlock G components c d e q t ht ⟨j.val+1,by omega⟩) := by
  intro j
  exact long_reserved_component_block_edges G (components q.1) (e q.1) (hthree q.1)
    c d t q.2.val ht (long_reserved_sigma_block_fit G components c d q) j

theorem long_reserved_sigma_blocks_disjoint
    (e:∀i:I,SimpleGraph.cycleGraph (Fintype.card (components i)) ≃g (components i).toSimpleGraph)
    (q q':LongReservedBlockIndex G components c d) (t t':ℕ) (ht:t≤d) (ht':t'≤d) (hne:q≠q'):
    Disjoint (Finset.univ.image (longReservedSigmaBlock G components c d e q t ht))
      (Finset.univ.image (longReservedSigmaBlock G components c d e q' t' ht')) := by
  cases q with
  | mk i bi =>
    cases q' with
    | mk j bj =>
      by_cases hij:i=j
      · subst j
        have hblock:bi.val≠bj.val:=by
          intro hv
          have hh:bi=bj:=Fin.ext hv
          apply hne
          cases hh
          rfl
        have hdis:=long_reserved_component_blocks_disjoint G (components i) (e i) c d t t' bi.val bj.val ht ht'
          (long_reserved_sigma_block_fit G components c d ⟨i,bi⟩) (long_reserved_sigma_block_fit G components c d ⟨i,bj⟩) hblock
        apply Finset.disjoint_left.mpr
        intro v hva hvb
        obtain ⟨x,_,hx⟩:=Finset.mem_image.mp hva
        obtain ⟨y,_,hy⟩:=Finset.mem_image.mp hvb
        let A:=longReservedComponentBlock G (components i) (e i) c d t bi.val ht (long_reserved_sigma_block_fit G components c d ⟨i,bi⟩)
        let B:=longReservedComponentBlock G (components i) (e i) c d t' bj.val ht' (long_reserved_sigma_block_fit G components c d ⟨i,bj⟩)
        have heq:A x=B y:=by apply Subtype.ext; exact hx.trans hy.symm
        have hA:A x∈Finset.univ.image A:=Finset.mem_image.mpr ⟨x,Finset.mem_univ _,rfl⟩
        have hB:B y∈Finset.univ.image B:=Finset.mem_image.mpr ⟨y,Finset.mem_univ _,rfl⟩
        exact (Finset.disjoint_left.mp hdis) hA (heq ▸ hB)
      · apply Finset.disjoint_left.mpr
        intro v hva hvb
        obtain ⟨x,_,hx⟩:=Finset.mem_image.mp hva
        obtain ⟨y,_,hy⟩:=Finset.mem_image.mp hvb
        let A:=longReservedComponentBlock G (components i) (e i) c d t bi.val ht (long_reserved_sigma_block_fit G components c d ⟨i,bi⟩)
        let B:=longReservedComponentBlock G (components j) (e j) c d t' bj.val ht' (long_reserved_sigma_block_fit G components c d ⟨j,bj⟩)
        have hci:G.connectedComponentMk v=components i:=by
          apply (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mp
          have hv:(A x).val=v:=hx
          rw [←hv]
          exact (A x).property
        have hcj:G.connectedComponentMk v=components j:=by
          apply (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mp
          have hv:(B y).val=v:=hy
          rw [←hv]
          exact (B y).property
        exact hij (components.injective (hci.symm.trans hcj))
end Oberwolfach

module

public import Oberwolfach.ResidualActualData

@[expose] public section
/-! Reindex the selected ordinary cycles without changing the residual vertices. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V K J J' : Type} [Fintype V] [DecidableEq V] [DecidableEq K]
  [DecidableEq J] [DecidableEq J'] {F : SimpleGraph V}

def ActualResidualData.reindexCycles (a : ActualResidualData (K:=K) (J:=J) F) (e : J' ≃ J) :
    ActualResidualData (K:=K) (J:=J') F where
  s₁ := a.s₁
  s₂ := a.s₂
  hs := a.hs
  u := a.u
  v := a.v
  P := a.P
  hp := a.hp
  hP := a.hP
  c := a.c
  d := a.d
  hc := a.hc
  hd := a.hd
  hlen := a.hlen
  T := a.T
  hT := a.hT
  t := a.t.map e.symm.toEmbedding
  root j := a.root (e j)
  C j := a.C (e j)
  hcycle := by
    intro j hj
    exact a.hcycle (e j) (by simpa using hj)
  hC := by
    intro j hj k hk hjk
    apply a.hC (by simpa using hj) (by simpa using hk)
    intro h
    exact hjk (e.injective h)
  hcross := by
    intro i hi j hj
    exact a.hcross i hi (e j) (by simpa using hj)
  Cembed := a.Cembed
  hEmbed := by
    intro x hx
    obtain ⟨j,hj,hxj⟩ := Finset.mem_biUnion.mp (a.hEmbed hx)
    apply Finset.mem_biUnion.mpr
    refine ⟨e.symm j, ?_, ?_⟩
    · simpa using hj
    · change x ∈ (a.C (e (e.symm j))).support.toFinset
      rw [e.apply_symm_apply]
      exact hxj

@[simp] theorem ActualResidualData.reindexCycles_remaining
    (a : ActualResidualData (K:=K) (J:=J) F) (e : J' ≃ J) :
    (a.reindexCycles e).remaining = a.remaining := by
  have hc : (a.reindexCycles e).t.biUnion (fun j => ((a.reindexCycles e).C j).support.toFinset) =
      a.t.biUnion (fun j => (a.C j).support.toFinset) := by
    ext x
    simp only [Finset.mem_biUnion, reindexCycles]
    constructor
    · rintro ⟨j,hj,hx⟩
      exact ⟨e j, by simpa using hj, hx⟩
    · rintro ⟨j,hj,hx⟩
      refine ⟨e.symm j, by simpa using hj, ?_⟩
      rw [e.apply_symm_apply]
      exact hx
  unfold remaining deletedVertices
  rw [hc]
  rfl
end Oberwolfach

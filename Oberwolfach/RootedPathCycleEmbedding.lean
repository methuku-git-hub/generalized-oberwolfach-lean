module

public import Oberwolfach.FixedPathCycles

@[expose] public section

/-! Retain the actual labelled embedding when closing a simple path.
The two ends occupy positions zero and r-1, respectively. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V : Type*} {G : SimpleGraph V} {x y : V} {r : ℕ}

def pathCycleEmbedding (p : G.Walk x y) (hp : p.IsPath) (hlen : p.length=r-1) : Fin r ↪ V where
  toFun i := p.getVert i.val
  inj' := by
    intro i j he
    apply Fin.ext
    exact hp.getVert_injOn (by change i.val≤p.length;rw [hlen];omega)
      (by change j.val≤p.length;rw [hlen];omega) he

theorem pathCycleEmbedding_first (hr : 0<r) (p : G.Walk x y) (hp : p.IsPath) (hlen : p.length=r-1) :
    pathCycleEmbedding p hp hlen ⟨0,hr⟩=x := p.getVert_zero

theorem pathCycleEmbedding_last (hr : 0<r) (p : G.Walk x y) (hp : p.IsPath) (hlen : p.length=r-1) :
    pathCycleEmbedding p hp hlen ⟨r-1,by omega⟩=y := by
  change p.getVert (r-1)=y
  rw [←hlen,p.getVert_length]

theorem pathCycleEmbedding_hom (hr : 3≤r) (p : G.Walk x y) (hp : p.IsPath) (hlen : p.length=r-1)
    (hxy : G.Adj x y) (i j : Fin r) (h : (SimpleGraph.cycleGraph r).Adj i j) :
    G.Adj (pathCycleEmbedding p hp hlen i) (pathCycleEmbedding p hp hlen j) := by
  change G.Adj (p.getVert i.val) (p.getVert j.val)
  rcases cycleGraph_adj_natural_cases r hr i j h with hij|hji|⟨hi,hj⟩|⟨hj,hi⟩
  · rw [←hij]
    exact p.adj_getVert_succ (by rw [hlen];have hj:=j.isLt;omega)
  · rw [←hji]
    exact (p.adj_getVert_succ (by rw [hlen];have hi:=i.isLt;omega)).symm
  · rw [hi,hj,←hlen,p.getVert_zero,p.getVert_length]
    exact hxy
  · rw [hj,hi,←hlen,p.getVert_zero,p.getVert_length]
    exact hxy.symm

theorem pathCycleEmbedding_avoids (S : Set V) (p : G.Walk x y) (hp : p.IsPath) (hlen : p.length=r-1)
    (havoid : ∀ v∈p.support,v∉S) : ∀ i,pathCycleEmbedding p hp hlen i∉S := by
  intro i
  exact havoid _ (p.getVert_mem_support i.val)

end Oberwolfach

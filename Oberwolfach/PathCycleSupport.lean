module

public import Oberwolfach.FixedPathCycles
public import Oberwolfach.OrdinaryLocalCycles

@[expose] public section

/-! Closing a simple path while retaining its exact support and every
consecutive path edge. These identities allow wheel callers to verify
root edges and all required spokes. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem embedded_cycle_from_path_with_support (G : SimpleGraph V)
    (r : ℕ) (hr : 3≤r) (x y : V) (p : G.Walk x y)
    (hp : p.IsPath) (hlen : p.length=r-1) (hxy : G.Adj x y) :
    ∃ C : SimpleGraph V,IsEmbeddedCycle C r ∧ C≤G ∧ C.Adj x y ∧
      (∀ v,v∈C.support ↔ v∈p.support) ∧
      (∀ i : ℕ,i<p.length → C.Adj (p.getVert i) (p.getVert (i+1))) := by
  let f : Fin r↪V:=⟨fun i=>p.getVert i.val,by
    intro i j he
    apply Fin.ext
    exact hp.getVert_injOn (by change i.val≤p.length;rw [hlen];omega)
      (by change j.val≤p.length;rw [hlen];omega) he⟩
  let C:=(SimpleGraph.cycleGraph r).map f
  have hC : IsEmbeddedCycle C r:=⟨hr,f,rfl⟩
  have hadj (i j : Fin r) (h : (SimpleGraph.cycleGraph r).Adj i j) : G.Adj (f i) (f j):=by
    change G.Adj (p.getVert i.val) (p.getVert j.val)
    rcases cycleGraph_adj_natural_cases r hr i j h with hij|hji|⟨hi,hj⟩|⟨hj,hi⟩
    · rw [←hij];exact p.adj_getVert_succ (by rw [hlen];have hj:=j.isLt;omega)
    · rw [←hji];exact (p.adj_getVert_succ (by rw [hlen];have hi:=i.isLt;omega)).symm
    · rw [hi,hj,←hlen,p.getVert_zero,p.getVert_length];exact hxy
    · rw [hj,hi,←hlen,p.getVert_zero,p.getVert_length];exact hxy.symm
  have hCG : C≤G:=by
    intro v w h
    obtain ⟨i,j,hij,rfl,rfl⟩:=(SimpleGraph.map_adj f _ _ _).mp h
    exact hadj i j hij
  have hclose : C.Adj x y:=by
    apply (SimpleGraph.map_adj f _ _ _).mpr
    refine ⟨⟨0,by omega⟩,⟨r-1,by omega⟩,?_,p.getVert_zero,?_⟩
    · apply (cycleGraph_modular_adj (by omega) _ _).mpr
      right
      change (r-1+1)%r=0
      rw [show r-1+1=r by omega,Nat.mod_self]
    · change p.getVert (r-1)=y
      rw [←hlen,p.getVert_length]
  have hsupport : ∀ v,v∈C.support ↔ v∈p.support:=by
    intro v
    rw [cycle_map_support hr f]
    constructor
    · rintro ⟨i,rfl⟩;exact p.getVert_mem_support _
    · intro hv
      obtain ⟨i,hiv,hi⟩:=SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hv
      exact ⟨⟨i,by rw [hlen] at hi;omega⟩,hiv⟩
  refine ⟨C,hC,hCG,hclose,hsupport,?_⟩
  intro i hi
  have hir : i+1<r:=by rw [hlen] at hi;omega
  apply (SimpleGraph.map_adj f _ _ _).mpr
  refine ⟨⟨i,by omega⟩,⟨i+1,hir⟩,?_,rfl,rfl⟩
  apply (cycleGraph_modular_adj (by omega) _ _).mpr
  left
  change (i+1)%r=i+1
  exact Nat.mod_eq_of_lt hir

end Oberwolfach

module

public import Oberwolfach.FiniteWalkExtensionEdges
public import Oberwolfach.SimpleWalkIntervalEdgeConcatenation

@[expose] public section
/-! Finite-index version of the simple-walk concatenation theorem. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem simple_walk_finite_concatenation_edges
    {V:Type*} {n:ℕ} (G:SimpleGraph V) (v:Fin (n+1) → V)
    (p:∀i:Fin n,G.Walk (v i.castSucc) (v i.succ)) (c:ℕ)
    (hp:∀i,(p i).IsPath) (hlen:∀i,(p i).length=c)
    (hdis:∀i j:Fin n,i ≠ j → ∀x ∈ (p i).support.dropLast,x ∉ (p j).support.dropLast)
    (hend:∀i:Fin n,v (Fin.last n) ∉ (p i).support.dropLast):
    ∃q:G.Walk (v 0) (v (Fin.last n)),q.IsPath ∧ q.length=n*c ∧
      (∀x,x ∈ q.support ↔ x=v (Fin.last n) ∨ ∃i:Fin n,x ∈ (p i).support.dropLast) ∧
      (∀e,e ∈ q.edges ↔ ∃i:Fin n,e ∈ (p i).edges) := by
  let v':ℕ → V:=finiteWalkClamp v
  let p':∀i:ℕ,G.Walk (v' i) (v' (i+1)):=finiteWalkExtension G v p
  have h0:v' 0=v 0:=by rfl
  have hn:v' (0+n)=v (Fin.last n):=by
    dsimp [v',finiteWalkClamp]
    congr 1
    apply Fin.ext
    simp
  have hp':∀i,0 ≤ i → i < 0+n → (p' i).IsPath:=by
    intro i _ hi
    have hh:=finite_walk_extension_initial_properties G v p ⟨i,by omega⟩
    exact hh.1.mpr (hp ⟨i,by omega⟩)
  have hl':∀i,0 ≤ i → i < 0+n → (p' i).length=c:=by
    intro i _ hi
    have hh:=finite_walk_extension_initial_properties G v p ⟨i,by omega⟩
    exact hh.2.1.trans (hlen ⟨i,by omega⟩)
  have hd':∀i j,0 ≤ i → i < 0+n → 0 ≤ j → j < 0+n → i ≠ j → 
      ∀x ∈ (p' i).support.dropLast,x ∉ (p' j).support.dropLast:=by
    intro i j _ hi _ hj hij x hx hy
    have hsi:=(finite_walk_extension_initial_properties G v p ⟨i,by omega⟩).2.2
    have hsj:=(finite_walk_extension_initial_properties G v p ⟨j,by omega⟩).2.2
    rw [hsi] at hx
    rw [hsj] at hy
    have hne:(⟨i,by omega⟩:Fin n) ≠ ⟨j,by omega⟩:=fun h=>hij (congrArg Fin.val h)
    exact hdis ⟨i,by omega⟩ ⟨j,by omega⟩ hne x hx hy
  have he':∀i,0 ≤ i → i < 0+n → v' (0+n) ∉ (p' i).support.dropLast:=by
    intro i _ hi hx
    have hsi:=(finite_walk_extension_initial_properties G v p ⟨i,by omega⟩).2.2
    rw [hsi,hn] at hx
    exact hend ⟨i,by omega⟩ hx
  obtain ⟨q,hq,hqlen,hqmem,hqedges⟩:=simple_walk_interval_concatenation_edges G v' p' c n 0 hp' hl' hd' he'
  let w:G.Walk (v 0) (v (Fin.last n)):=q.copy h0 hn
  have hwpath:w.IsPath:=by simpa [w] using hq
  have hwlen:w.length=n*c:=by simpa [w] using hqlen
  refine ⟨w,hwpath,hwlen,?_,?_⟩
  · intro x
    have hwmem:x ∈ w.support ↔ x ∈ q.support:=by simp [w]
    rw [hwmem,hqmem,hn]
    constructor
    · rintro (h|⟨i,_,hi,hx⟩)
      · exact Or.inl h
      · right
        have hh:=(finite_walk_extension_initial_properties G v p ⟨i,by omega⟩).2.2
        rw [hh] at hx
        exact ⟨⟨i,by omega⟩,hx⟩
    · rintro (h|⟨i,hx⟩)
      · exact Or.inl h
      · right;refine ⟨i.val,by omega,by simpa using i.isLt,?_⟩
        have hh:=(finite_walk_extension_initial_properties G v p i).2.2
        rw [hh]
        exact hx
  · intro e
    have hwedge:e ∈ w.edges ↔ e ∈ q.edges:=by simp [w]
    rw [hwedge,hqedges]
    constructor
    · rintro ⟨i,_,hi,he⟩
      have hh:=finite_walk_extension_initial_edges G v p ⟨i,by omega⟩
      rw [hh] at he
      exact ⟨⟨i,by omega⟩,he⟩
    · rintro ⟨i,he⟩
      refine ⟨i.val,by omega,by simpa using i.isLt,?_⟩
      have hh:=finite_walk_extension_initial_edges G v p i
      rw [hh]
      exact he

end Oberwolfach

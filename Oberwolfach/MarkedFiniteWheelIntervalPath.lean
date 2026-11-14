module

public import Oberwolfach.SimpleWalkFiniteConcatenation
public import Oberwolfach.MarkedWheelWalkInitialSupport

@[expose] public section
/-! A finite successor-linked family of disjoint marked wheels reconstructs
 a simple physical path, with its exact length and vertex support. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_finite_wheel_interval_path
    {V E K:Type*} {n:ℕ} (G:SimpleGraph V) (tail head:E→V) (ktail khead:K→V)
    (m b:ℕ) (π:Equiv.Perm V) (hb:1≤b) (v:Fin (n+1)→V)
    (C:Fin n→MarkedCycleTuple tail head ktail khead m π b)
    (hroot:∀i,(C i).val 0=v i.castSucc)
    (hsucc:∀i,π ((C i).val 0)=v i.succ)
    (hnofixed:∀i,π ((C i).val 0)≠(C i).val 0)
    (hE:∀e:E,G.Adj (tail e) (head e))
    (hK:∀e:K,G.Adj (ktail e) (π (khead e)))
    (hdis:∀i j:Fin n,i≠j→∀a b:Fin (m+1),(C i).val a≠(C j).val b)
    (hend:∀i:Fin n,∀a:Fin (m+1),v (Fin.last n)≠(C i).val a):
    ∃q:G.Walk (v 0) (v (Fin.last n)),q.IsPath ∧ q.length=n*(m+1) ∧
      ∀x,x∈q.support ↔ x=v (Fin.last n) ∨ ∃i:Fin n,∃a:Fin (m+1),(C i).val a=x := by
  have hexist:∀i:Fin n,∃p:G.Walk (v i.castSucc) (v i.succ),
      p.IsPath ∧ p.length=m+1 ∧ p.support.dropLast=List.ofFn (C i).val:=by
    intro i
    obtain ⟨p,hp,hlen,hsupport⟩:=marked_wheel_walk_initial_support G tail head ktail khead m b π hb (C i) (hnofixed i) hE hK
    rw [←hsucc i,←hroot i]
    exact ⟨p,hp,hlen,hsupport⟩
  let p:∀i:Fin n,G.Walk (v i.castSucc) (v i.succ):=fun i=>Classical.choose (hexist i)
  have hp:∀i,(p i).IsPath:=fun i=>(Classical.choose_spec (hexist i)).1
  have hlen:∀i,(p i).length=m+1:=fun i=>(Classical.choose_spec (hexist i)).2.1
  have hsupport:∀i,(p i).support.dropLast=List.ofFn (C i).val:=fun i=>(Classical.choose_spec (hexist i)).2.2
  have hdis':∀i j:Fin n,i≠j→∀x∈(p i).support.dropLast,x∉(p j).support.dropLast:=by
    intro i j hij x hx hy
    rw [hsupport i] at hx
    rw [hsupport j] at hy
    obtain ⟨a,ha⟩:=List.mem_ofFn.mp hx
    obtain ⟨b,hb⟩:=List.mem_ofFn.mp hy
    exact hdis i j hij a b (ha.trans hb.symm)
  have hend':∀i:Fin n,v (Fin.last n)∉(p i).support.dropLast:=by
    intro i hx
    rw [hsupport i] at hx
    obtain ⟨a,ha⟩:=List.mem_ofFn.mp hx
    exact hend i a ha.symm
  obtain ⟨q,hq,hqlen,hqmem⟩:=simple_walk_finite_concatenation G v p (m+1) hp hlen hdis' hend'
  refine ⟨q,hq,hqlen,?_⟩
  intro x
  rw [hqmem]
  constructor
  · rintro (h|⟨i,hx⟩)
    · exact Or.inl h
    · right;refine ⟨i,?_⟩
      rw [hsupport i] at hx
      exact List.mem_ofFn.mp hx
  · rintro (h|⟨i,a,ha⟩)
    · exact Or.inl h
    · right;refine ⟨i,?_⟩
      rw [hsupport i]
      exact List.mem_ofFn.mpr ⟨a,ha⟩
end Oberwolfach

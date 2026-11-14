module

public import Oberwolfach.SimpleWalkIntervalConcatenation
public import Oberwolfach.MarkedWheelWalkInitialSupport

@[expose] public section
/-! Concatenate marked-wheel physical walks when their auxiliary rim vertices
are disjoint and the final successor lies outside those rim vertices. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_wheel_interval_from_rim_supports
    {V:Type*} (G:SimpleGraph V) (v:ℕ→V) (c n start:ℕ)
    (C:ℕ→Fin c→V) (p:∀i:ℕ,G.Walk (v i) (v (i+1)))
    (hp:∀i,start ≤ i → i < start+n → (p i).IsPath)
    (hlen:∀i,start ≤ i → i < start+n → (p i).length=c)
    (hsupport:∀i,start ≤ i → i < start+n → (p i).support.dropLast=List.ofFn (C i))
    (hdis:∀i j,start ≤ i → i < start+n → start ≤ j → j < start+n → i≠j →
      ∀a b:Fin c,C i a≠C j b)
    (hend:∀i,start ≤ i → i < start+n → ∀a:Fin c,v (start+n)≠C i a):
    ∃q:G.Walk (v start) (v (start+n)),q.IsPath ∧ q.length=n*c ∧
      ∀x,x∈q.support ↔ x=v (start+n) ∨
        ∃i,start ≤ i ∧ i < start+n ∧ ∃a:Fin c,C i a=x := by
  have hd':∀i j,start ≤ i → i < start+n → start ≤ j → j < start+n → i≠j →
      ∀x∈(p i).support.dropLast,x∉(p j).support.dropLast:=by
    intro i j hi hj hk hl hij x hx hy
    rw [hsupport i hi hj] at hx
    rw [hsupport j hk hl] at hy
    obtain ⟨a,ha⟩:=List.mem_ofFn.mp hx
    obtain ⟨b,hb⟩:=List.mem_ofFn.mp hy
    exact hdis i j hi hj hk hl hij a b (ha.trans hb.symm)
  have he':∀i,start ≤ i → i < start+n → v (start+n)∉(p i).support.dropLast:=by
    intro i hi hj hx
    rw [hsupport i hi hj] at hx
    obtain ⟨a,ha⟩:=List.mem_ofFn.mp hx
    exact hend i hi hj a ha.symm
  obtain ⟨q,hq,hqlen,hqmem⟩:=simple_walk_interval_concatenation G v p c n start hp hlen hd' he'
  refine ⟨q,hq,hqlen,?_⟩
  intro x
  rw [hqmem]
  constructor
  · rintro (h|⟨i,hi,hj,hx⟩)
    · exact Or.inl h
    · right;refine ⟨i,hi,hj,?_⟩
      rw [hsupport i hi hj] at hx
      exact List.mem_ofFn.mp hx
  · rintro (h|⟨i,hi,hj,a,ha⟩)
    · exact Or.inl h
    · right;refine ⟨i,hi,hj,?_⟩
      rw [hsupport i hi hj]
      exact List.mem_ofFn.mpr ⟨a,ha⟩
end Oberwolfach

module

public import Oberwolfach.SimpleWalkConcatSupport

@[expose] public section
/-! A finite interval of simple walks with disjoint initial supports and a
fresh terminal vertex concatenates to a simple walk of the summed length. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem simple_walk_interval_concatenation_edges
    {V:Type*} (G:SimpleGraph V) (v:ℕ → V) (p:∀i:ℕ,G.Walk (v i) (v (i+1)))
    (c n start:ℕ)
    (hp:∀i,start ≤ i → i < start+n → (p i).IsPath)
    (hlen:∀i,start ≤ i → i < start+n → (p i).length=c)
    (hdis:∀i j,start ≤ i → i < start+n → start ≤ j → j < start+n → i ≠ j → 
      ∀x ∈ (p i).support.dropLast,x ∉ (p j).support.dropLast)
    (hend:∀i,start ≤ i → i < start+n → v (start+n) ∉ (p i).support.dropLast):
    ∃q:G.Walk (v start) (v (start+n)),q.IsPath ∧ q.length=n*c ∧
      (∀x,x ∈ q.support ↔ x=v (start+n) ∨
        ∃i,start ≤ i ∧ i < start+n ∧ x ∈ (p i).support.dropLast) ∧
      (∀e,e ∈ q.edges ↔ ∃i,start ≤ i ∧ i < start+n ∧ e ∈ (p i).edges) := by
  induction n generalizing start with
  | zero =>
    refine ⟨SimpleGraph.Walk.nil,SimpleGraph.Walk.IsPath.nil,by simp,?_,?_⟩
    · intro x
      simp
      omega
    · intro e
      simp
      omega
  | succ n ih =>
    have heq:start+1+n=start+(n+1):=by omega
    have hp':∀i,start+1 ≤ i → i < start+1+n → (p i).IsPath:=by
      intro i hi hj;apply hp i  <;> omega
    have hl':∀i,start+1 ≤ i → i < start+1+n → (p i).length=c:=by
      intro i hi hj;apply hlen i  <;> omega
    have hd':∀i j,start+1 ≤ i → i < start+1+n → start+1 ≤ j → j < start+1+n → i ≠ j → 
        ∀x ∈ (p i).support.dropLast,x ∉ (p j).support.dropLast:=by
      intro i j hi hj hk hl hij x hx
      exact hdis i j (by omega) (by omega) (by omega) (by omega) hij x hx
    have he':∀i,start+1 ≤ i → i < start+1+n → v (start+1+n) ∉ (p i).support.dropLast:=by
      intro i hi hj
      rw [heq]
      exact hend i (by omega) (by omega)
    obtain ⟨q,hq,hqlen,hqmem,hqedges⟩:=ih (start+1) hp' hl' hd' he'
    have hfirst:(p start).IsPath:=hp start (by omega) (by omega)
    have hfirstlen:(p start).length=c:=hlen start (by omega) (by omega)
    have hsep:∀x ∈ (p start).support.dropLast,x ∉ q.support:=by
      intro x hx hq'
      rcases (hqmem x).mp hq' with hterminal | ⟨i,hi,hupper,hxi⟩
      · have hh:=hend start (by omega) (by omega)
        rw [←heq,←hterminal] at hh
        exact hh hx
      · exact hdis start i (by omega) (by omega) (by omega) (by omega) (by omega) x hx hxi
    obtain ⟨hsimple,hsum,hsupport⟩:=simple_walk_append_of_disjoint_initial_support (p start) q hfirst hq hsep
    have hresult:∃w:G.Walk (v start) (v (start+1+n)),w.IsPath ∧ w.length=(n+1)*c ∧
      (∀x,x ∈ w.support ↔ x=v (start+1+n) ∨
        ∃i,start ≤ i ∧ i < start+1+n ∧ x ∈ (p i).support.dropLast) ∧
      (∀e,e ∈ w.edges ↔ ∃i,start ≤ i ∧ i < start+1+n ∧ e ∈ (p i).edges):=by
      refine ⟨(p start).append q,hsimple,?_,?_,?_⟩
      · calc
          ((p start).append q).length=(p start).length+q.length:=hsum
          _=c+n*c:=by rw [hfirstlen,hqlen]
          _=(n+1)*c:=by nlinarith
      · intro x
        rw [hsupport,List.mem_append,hqmem]
        constructor
        · rintro (hx|hx|⟨i,hi,hupper,hxi⟩)
          · right;exact ⟨start,by omega,by omega,hx⟩
          · exact Or.inl hx
          · right;exact ⟨i,by omega,by omega,hxi⟩
        · rintro (hx|⟨i,hi,hupper,hxi⟩)
          · exact Or.inr (Or.inl hx)
          · by_cases h:i=start
            · subst i;left;exact hxi
            · right;right;exact ⟨i,by omega,by omega,hxi⟩
      · intro e
        rw [SimpleGraph.Walk.edges_append,List.mem_append,hqedges]
        constructor
        · rintro (he|⟨i,hi,hupper,hei⟩)
          · exact ⟨start,by omega,by omega,he⟩
          · exact ⟨i,by omega,by omega,hei⟩
        · rintro ⟨i,hi,hupper,hei⟩
          by_cases h:i=start
          · subst i;exact Or.inl hei
          · exact Or.inr ⟨i,by omega,by omega,hei⟩
    rw [←heq]
    exact hresult
end Oberwolfach

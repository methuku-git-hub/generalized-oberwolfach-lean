module

public import Oberwolfach.DirectedWalkAppend

@[expose] public section
/-! A finite interval of simple walks with disjoint initial supports and a
fresh terminal vertex concatenates to a simple walk of the summed length. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem simple_directed_walk_interval_concatenation_with_edges
    {V:Type*} (G:SimpleGraph V) (v:ℕ → V) (p:∀i:ℕ,G.Walk (v i) (v (i+1)))
    (c n start:ℕ)
    (hp:∀i,start ≤ i → i < start+n → (p i).IsPath)
    (hlen:∀i,start ≤ i → i < start+n → (p i).length=c)
    (hdis:∀i j,start ≤ i → i < start+n → start ≤ j → j < start+n → i ≠ j → 
      ∀x ∈ (p i).support.dropLast,x ∉ (p j).support.dropLast)
    (hend:∀i,start ≤ i → i < start+n → v (start+n) ∉ (p i).support.dropLast)
    (R:V→V→Prop)
    (hR:∀ i, start ≤ i → i < start+n → ∀ k, k < (p i).length → R ((p i).getVert k) ((p i).getVert (k+1))):
    ∃q:G.Walk (v start) (v (start+n)),q.IsPath ∧ q.length=n*c ∧
      (∀x,x ∈ q.support ↔ x=v (start+n) ∨
        ∃i,start ≤ i ∧ i < start+n ∧ x ∈ (p i).support.dropLast) ∧
      (∀j,j≤n→q.getVert (c*j)=v (start+j)) ∧
      (∀e:Sym2 V,e∈q.edges ↔ ∃i,start ≤ i ∧ i < start+n ∧ e∈(p i).edges) ∧
      (∀ k, k < q.length → R (q.getVert k) (q.getVert (k+1))) := by
  induction n generalizing start with
  | zero =>
    refine ⟨SimpleGraph.Walk.nil,SimpleGraph.Walk.IsPath.nil,by simp,?_,?_,?_,?_⟩
    · intro x
      simp
      omega
    · intro j hj
      have :j=0:=by omega
      subst j
      simp
    · intro e
      simp
      omega
    · intro k hk
      simp at hk
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
    have hR':∀ i, start+1 ≤ i → i < start+1+n → ∀ k, k < (p i).length → R ((p i).getVert k) ((p i).getVert (k+1)):=by
      intro i hi hj k hk
      exact hR i (by omega) (by omega) k hk
    obtain ⟨q,hq,hqlen,hqmem,hqmark,hqedges,hqR⟩:=ih (start+1) hp' hl' hd' he' hR' 
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
      (∀j,j≤n+1→w.getVert (c*j)=v (start+j)) ∧
      (∀e:Sym2 V,e∈w.edges ↔ ∃i,start ≤ i ∧ i < start+1+n ∧ e∈(p i).edges) ∧
      (∀ k, k < w.length → R (w.getVert k) (w.getVert (k+1))):=by
      refine ⟨(p start).append q,hsimple,?_,?_,?_,?_,?_⟩
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
      · intro j hj
        cases j with
        | zero => simp
        | succ j =>
          have hj':j≤n:=by omega
          have hk:c*(j+1)≥(p start).length:=by rw [hfirstlen];nlinarith
          rw [SimpleGraph.Walk.getVert_append]
          simp only [if_neg (show ¬c*(j+1)<(p start).length by omega)]
          have he:c*(j+1)-(p start).length=c*j:=by rw [hfirstlen,Nat.mul_add,Nat.mul_one,Nat.add_sub_cancel_right]
          rw [he,hqmark j hj']
          congr 1 <;> omega
      · intro e
        rw [SimpleGraph.Walk.edges_append,List.mem_append,hqedges]
        constructor
        · rintro (h|⟨i,hi,hj,he⟩)
          · exact ⟨start,by omega,by omega,h⟩
          · exact ⟨i,by omega,by omega,he⟩
        · rintro ⟨i,hi,hj,he⟩
          by_cases h:i=start
          · subst i;exact Or.inl he
          · exact Or.inr ⟨i,by omega,by omega,he⟩
      · exact walk_append_preserves_successor_relation (p start) q R (hR start (by omega) (by omega)) hqR
    rw [←heq]
    exact hresult
end Oberwolfach

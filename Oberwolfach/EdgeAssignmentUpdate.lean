module

public import Oberwolfach.PrescribedPositionPairing

@[expose] public section
/-! Extend one conflict-free capacitated partial assignment by a valid edge
and preserve every earlier assignment. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {E W:Type} [Fintype W] [DecidableEq E] [DecidableEq W]

theorem edge_assignment_update (T:Finset E) (f:E→W) (e:E) (he:e∉T)
    (L Bad:E→Finset W) (C:E→E→Prop) (hsym:∀x y,C x y→C y x) (K:ℕ)
    (hallowed:∀x∈T,f x∈L x ∧ f x∉Bad x)
    (hconf:∀x∈T,∀y∈T,x≠y→C x y→ f x≠f y)
    (hcap:∀w,(T.filter (fun x=>f x=w)).card≤K)
    (w:W) (hw:w∈L e) (hwb:w∉Bad e) (hwconf:∀x∈T,C e x→ f x≠w)
    (hwcap:(T.filter (fun x=>f x=w)).card<K):
    let g:=Function.update f e w;
    (∀x∈insert e T,g x∈L x ∧ g x∉Bad x) ∧
    (∀x∈insert e T,∀y∈insert e T,x≠y→C x y→ g x≠g y) ∧
    (∀z,((insert e T).filter (fun x=>g x=z)).card≤K) ∧
    (∀x∈T,g x=f x) := by
  intro g
  have hpres:∀x∈T,g x=f x:=by
    intro x hx
    have hne:x≠e:=by intro h;subst x;exact he hx
    simp [g,Function.update_of_ne hne]
  have hge:g e=w:=by simp [g]
  refine ⟨?_,?_,?_,hpres⟩
  · intro x hx
    rcases Finset.mem_insert.mp hx with rfl|hx
    · simpa [hge] using And.intro hw hwb
    · simpa [hpres x hx] using hallowed x hx
  · intro x hx y hy hne hc
    by_cases hxE:x=e
    · subst x
      have hyne:y≠e:=Ne.symm hne
      have hyT:y∈T:=(Finset.mem_insert.mp hy).resolve_left hyne
      rw [hge,hpres y hyT]
      exact Ne.symm (hwconf y hyT hc)
    · have hxT:x∈T:=(Finset.mem_insert.mp hx).resolve_left hxE
      by_cases hyE:y=e
      · subst y
        rw [hpres x hxT,hge]
        exact hwconf x hxT (hsym x e hc)
      · have hyT:y∈T:=(Finset.mem_insert.mp hy).resolve_left hyE
        rw [hpres x hxT,hpres y hyT]
        exact hconf x hxT y hyT hne hc
  · intro z
    by_cases hzw:z=w
    · subst z
      have hf:(insert e T).filter (fun x=>g x=w)=insert e (T.filter (fun x=>f x=w)):=by
        ext x
        simp only [Finset.mem_filter,Finset.mem_insert]
        constructor
        · rintro ⟨rfl|hx,hxg⟩
          · exact Or.inl rfl
          · exact Or.inr ⟨hx,by simpa [hpres x hx] using hxg⟩
        · rintro (rfl|⟨hx,hxf⟩)
          · exact ⟨Or.inl rfl,hge⟩
          · exact ⟨Or.inr hx,by simpa [hpres x hx] using hxf⟩
      rw [hf,Finset.card_insert_of_notMem (by simp [he])]
      omega
    · have hf:(insert e T).filter (fun x=>g x=z)=T.filter (fun x=>f x=z):=by
        ext x
        simp only [Finset.mem_filter,Finset.mem_insert]
        constructor
        · rintro ⟨rfl|hx,hxg⟩
          · exact (hzw (hxg.symm.trans hge)).elim
          · exact ⟨hx,by simpa [hpres x hx] using hxg⟩
        · rintro ⟨hx,hxf⟩
          exact ⟨Or.inr hx,by simpa [hpres x hx] using hxf⟩
      rw [hf]
      exact hcap z
end Oberwolfach

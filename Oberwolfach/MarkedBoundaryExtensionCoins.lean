module

public import Oberwolfach.MarkedBoundaryExtensionCounts
public import Oberwolfach.EdgeRetention

@[expose] public section

/-! At most three physical coins determine a marked boundary extension.
Each coin affects at most three candidate labels, including arbitrary
ambient roots. No independence of candidate indicators is asserted. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

def markedBoundaryStepCoins (π:Equiv.Perm V) (j:Bool) (x:V) (u:U) (z:V):Finset (Sym2 (V⊕U)):=
  {s(Sum.inl x,Sum.inl (if j then π z else z)),s(Sum.inl z,Sum.inr u)}
def markedBoundaryJoinCoins (x y:V) (u:U) (z:V):Finset (Sym2 (V⊕U)):=
  {s(Sum.inl x,Sum.inl z),s(Sum.inl z,Sum.inl y),s(Sum.inl z,Sum.inr u)}

theorem three_injective_coin_maps_influence {E:Type} [DecidableEq E]
    (f g h:V→E) (hf:Function.Injective f) (hg:Function.Injective g) (hh:Function.Injective h) (e:E):
    (Finset.univ.filter (fun v=>e∈({f v,g v,h v}:Finset E))).card≤3:=by
  have h1 (f:V→E) (hf:Function.Injective f):(Finset.univ.filter (fun v=>e=f v)).card≤1:=by
    apply Finset.card_le_one.mpr
    intro v hv w hw
    exact hf ((Finset.mem_filter.mp hv).2.symm.trans (Finset.mem_filter.mp hw).2)
  have he:Finset.univ.filter (fun v=>e∈({f v,g v,h v}:Finset E))=
      (Finset.univ.filter (fun v=>e=f v))∪((Finset.univ.filter (fun v=>e=g v))∪(Finset.univ.filter (fun v=>e=h v))):=by
    ext v;simp
  rw [he]
  have ha:=Finset.card_union_le (Finset.univ.filter (fun v=>e=f v))
    ((Finset.univ.filter (fun v=>e=g v))∪(Finset.univ.filter (fun v=>e=h v)))
  have hb:=Finset.card_union_le (Finset.univ.filter (fun v=>e=g v)) (Finset.univ.filter (fun v=>e=h v))
  have hc:=h1 f hf;have hd:=h1 g hg;have hi:=h1 h hh
  omega

theorem marked_boundary_step_coins_size (π:Equiv.Perm V) (j:Bool) (x:V) (u:U) (z:V):
    (markedBoundaryStepCoins π j x u z).card≤3:=by
  unfold markedBoundaryStepCoins
  have h:=Finset.card_insert_le (s(Sum.inl x,Sum.inl (if j then π z else z)):Sym2 (V⊕U)) {s(Sum.inl z,Sum.inr u)}
  simp only [Finset.card_singleton] at h
  omega
theorem marked_boundary_join_coins_size (x y:V) (u:U) (z:V):
    (markedBoundaryJoinCoins x y u z).card≤3:=by
  unfold markedBoundaryJoinCoins
  have h1:=Finset.card_insert_le (s(Sum.inl z,Sum.inl y):Sym2 (V⊕U)) {s(Sum.inl z,Sum.inr u)}
  have h2:=Finset.card_insert_le (s(Sum.inl x,Sum.inl z):Sym2 (V⊕U)) {s(Sum.inl z,Sum.inl y),s(Sum.inl z,Sum.inr u)}
  simp only [Finset.card_singleton] at h1
  omega

theorem marked_boundary_step_coins_influence (π:Equiv.Perm V) (j:Bool) (x:V) (u:U) (e:Sym2 (V⊕U)):
    (Finset.univ.filter (fun z=>e∈markedBoundaryStepCoins π j x u z)).card≤3:=by
  have hsp:Function.Injective (fun z:V=>(s(Sum.inl z,Sum.inr u):Sym2 (V⊕U))):=by
    intro z w he;exact Sum.inl.inj (Sym2.congr_left.mp he)
  have hr:Function.Injective (fun z:V=>(s(Sum.inl x,Sum.inl (if j then π z else z)):Sym2 (V⊕U))):=by
    intro z w he
    have hz:=Sum.inl.inj (Sym2.congr_right.mp he)
    cases j
    · exact hz
    · exact π.injective hz
  have h:=three_injective_coin_maps_influence
    (fun z:V=>(s(Sum.inl x,Sum.inl (if j then π z else z)):Sym2 (V⊕U)))
    (fun z:V=>(s(Sum.inl z,Sum.inr u):Sym2 (V⊕U)))
    (fun z:V=>(s(Sum.inl z,Sum.inr u):Sym2 (V⊕U))) hr hsp hsp e
  simpa only [markedBoundaryStepCoins,Finset.insert_eq_of_mem (Finset.mem_singleton_self _)] using h

theorem marked_boundary_join_coins_influence (x y:V) (u:U) (e:Sym2 (V⊕U)):
    (Finset.univ.filter (fun z=>e∈markedBoundaryJoinCoins x y u z)).card≤3:=by
  unfold markedBoundaryJoinCoins
  exact three_injective_coin_maps_influence
    (fun z:V=>(s(Sum.inl x,Sum.inl z):Sym2 (V⊕U)))
    (fun z:V=>(s(Sum.inl z,Sum.inl y):Sym2 (V⊕U)))
    (fun z:V=>(s(Sum.inl z,Sum.inr u):Sym2 (V⊕U)))
    (fun z w he=>Sum.inl.inj (Sym2.congr_right.mp he))
    (fun z w he=>Sum.inl.inj (Sym2.congr_left.mp he))
    (fun z w he=>Sum.inl.inj (Sym2.congr_left.mp he)) e
end Oberwolfach

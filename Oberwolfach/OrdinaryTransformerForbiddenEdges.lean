module

public import Oberwolfach.OrdinaryDecompositionEdges

@[expose] public section

/-! The transformer's proved vertex-avoidance conclusions already exclude
any bounded forbidden edge set whose endpoints were included in its forbidden
row and hub sets. No deletion of the host or its fixed weights is needed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U : Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

def ordinaryResourceRows (L : Finset (Sym2 V⊕(V×U))) : Finset V :=
  L.biUnion (fun e=>match e with | .inl e=>e.toFinset | .inr p=>{p.1})
def ordinaryResourceHubs (L : Finset (Sym2 V⊕(V×U))) : Finset U :=
  L.biUnion (fun e=>match e with | .inl _=>∅ | .inr p=>{p.2})

theorem ordinaryResourceRows_card (L : Finset (Sym2 V⊕(V×U))) :
    (ordinaryResourceRows L).card≤2*L.card := by
  apply Finset.card_biUnion_le.trans
  calc
    _ ≤ ∑ _e∈L,2 := by
      apply Finset.sum_le_sum
      intro e _
      cases e with
      | inl e=>rw [Sym2.card_toFinset]; split <;> omega
      | inr p=>simp
    _ = _ := by simp [Nat.mul_comm]

theorem ordinaryResourceHubs_card (L : Finset (Sym2 V⊕(V×U))) :
    (ordinaryResourceHubs L).card≤L.card := by
  apply Finset.card_biUnion_le.trans
  calc
    _ ≤ ∑ _e∈L,1 := by
      apply Finset.sum_le_sum
      intro e _;cases e <;> simp
    _ = _ := by simp

theorem ordinary_transformer_forbidden_edges (K L : Finset (Sym2 V⊕(V×U)))
    (R W : Finset V) (B : Finset U)
    (hrows : ordinaryResourceRows L⊆W) (hhubs : ordinaryResourceHubs L⊆B)
    (havoid : ∀ v∈W,∀ w,Sum.inl s(v,w)∈K→v∈R)
    (hspoke : ∀ v∈W,∀ u,Sum.inr (v,u)∈K→v∈R)
    (hRR : ∀ v∈R,∀ w∈R,Sum.inl s(v,w)∉K)
    (hRB : ∀ v∈R,∀ u∈B,Sum.inr (v,u)∉K) : Disjoint K L := by
  apply Finset.disjoint_left.mpr
  intro e he hL
  cases e with
  | inl e=>
    induction e using Sym2.ind with
    | _ v w=>
      have hv : v∈W := hrows (Finset.mem_biUnion.mpr ⟨.inl s(v,w),hL,by simp⟩)
      have hw : w∈W := hrows (Finset.mem_biUnion.mpr ⟨.inl s(v,w),hL,by simp⟩)
      have hev : Sum.inl s(w,v)∈K := by simpa only [Sym2.eq_swap] using he
      exact hRR v (havoid v hv w he) w (havoid w hw v hev) he
  | inr p=>
    rcases p with ⟨v,u⟩
    have hv : v∈W := hrows (Finset.mem_biUnion.mpr ⟨.inr (v,u),hL,by simp⟩)
    have hu : u∈B := hhubs (Finset.mem_biUnion.mpr ⟨.inr (v,u),hL,by simp⟩)
    exact hRB v (hspoke v hv u he) u hu he

end Oberwolfach

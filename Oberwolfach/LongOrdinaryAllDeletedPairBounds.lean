module

public import Oberwolfach.LongEmbeddedOrdinaryNearFar
public import Oberwolfach.LongRawDeletedIncidence

@[expose] public section
/-! Near/far omitted-pair bounds for the ordinary seed family at every root
and every deleted rim resource, retaining the mixed typed universe. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance longOrdinaryAllDeletedPairFinDecidable (n:ℕ):DecidableEq (Fin n):=Classical.decEq _
variable {n:ℕ} {U:Type} [Fintype U] [DecidableEq U] {m b:ℕ} {π:Equiv.Perm (Fin n)}

def longOrdinaryRootVertices : LongRawHubResource n U→Finset (Fin n)
  | Sum.inl (Sum.inl (x,y))=>{x,y}
  | Sum.inr (false,v,_)=>{v}
  | _=>∅

theorem long_ordinary_deleted_rim_pair_near_far
    (hm:2≤m) (hn:0<n) (hu:Fintype.card U≤n)
    (w:OrderedOrdinaryWheel (U:=U) π b (m+1)→ℝ) (B:ℝ) (hB:0≤B)
    (hw:∀W,0≤w W ∧ w W≤B/(n:ℝ)^m)
    (root:LongRawHubResource n U) (e:(Fin n×Fin n)⊕(Fin n×Fin n)):
    resourceOmittedPairWeight (fun W=>(orderedOrdinaryResources W).map ordinaryMarkedResourceEmbedding)
      w root (Sum.inl e)≤
      if longRawResourceTail (U:=U) (Sum.inl e)∈longOrdinaryRootVertices root ∨
          longRawResourceHead (U:=U) (Sum.inl e)∈longOrdinaryRootVertices root then
        ((m:ℝ)+1)^4*B/(n:ℝ)
      else ((m:ℝ)+1)^4*B/(n:ℝ)^2 :=by
  cases e with
  | inr e =>
    rcases e with ⟨a,c⟩
    rw [long_embedded_ordinary_pair_marked_rim_zero]
    split_ifs <;> positivity
  | inl e =>
    rcases e with ⟨a,c⟩
    cases root with
    | inl r =>
      cases r with
      | inl r =>
        rcases r with ⟨x,y⟩
        convert long_embedded_ordinary_rim_pair_near_far hm hn hu w B hB hw x y a c using 1 <;>
          simp [ordinaryMarkedResourceEmbedding,orderedOrdinaryResourceEmbedding,longRawResourceTail,
            longRawResourceHead,longOrdinaryRootVertices]
      | inr r =>
        have hz:=long_embedded_ordinary_pair_nonordinary_root_zero w (Sum.inl (Sum.inr r)) (by
          intro q
          cases q with
          | inl p => simp [ordinaryMarkedResourceEmbedding,orderedOrdinaryResourceEmbedding]
          | inr p => simp [ordinaryMarkedResourceEmbedding,orderedOrdinaryResourceEmbedding]) (Sum.inl (Sum.inl (a,c)))
        rw [hz]
        split_ifs <;> positivity
    | inr r =>
      rcases r with ⟨mark,v,u⟩
      cases mark with
      | false =>
        have hh:=long_embedded_ordinary_spoke_rim_near_far hm hn w B hB hw v a c u
        have hp:((m:ℝ)+1)^3≤((m:ℝ)+1)^4:=by
          have hm0:0≤((m:ℝ)+1)^3:=by positivity
          have hm1:(1:ℝ)≤(m:ℝ)+1:=le_add_of_nonneg_left (Nat.cast_nonneg m)
          calc
            _ = ((m:ℝ)+1)^3*1:=by ring
            _ ≤ ((m:ℝ)+1)^3*((m:ℝ)+1):=mul_le_mul_of_nonneg_left hm1 hm0
            _ = _:=by ring
        simp only [ordinaryMarkedResourceEmbedding,orderedOrdinaryResourceEmbedding] at hh
        simp only [longRawResourceTail,longRawResourceHead,longOrdinaryRootVertices,Finset.mem_singleton,Sum.elim_inl]
        split_ifs at hh ⊢ with hnear
        · exact hh.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hp hB) (by positivity))
        · exact hh.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hp hB) (by positivity))
      | true =>
        have hz:=long_embedded_ordinary_pair_nonordinary_root_zero w (Sum.inr (true,v,u)) (by
          intro q
          cases q with
          | inl p => simp [ordinaryMarkedResourceEmbedding,orderedOrdinaryResourceEmbedding]
          | inr p => simp [ordinaryMarkedResourceEmbedding,orderedOrdinaryResourceEmbedding]) (Sum.inl (Sum.inl (a,c)))
        rw [hz]
        split_ifs <;> positivity
end Oberwolfach

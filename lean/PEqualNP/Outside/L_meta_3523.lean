import Mathlib.Data.Set.Card
import Mathlib.Order.Fin.Basic
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_3523 :
∀ (x1 x2 : ℕ) (x3 x4 : Finset (Fin x1 × Fin x2)), x4 ⊆ x3 → (∀ x6 ∈ x4, ∀ x8 ∈ x4, x6.1 = x8.1 → x6 = x8) → (∀ x7 ∈ x4, ∀ x9 ∈ x4, x7.2 = x9.2 → x7 = x9) → ∃ (x8 : SimpleGraph (Fin (x1 + x2))), (∀ (x9 x10 : Fin (x1 + x2)), x8.Adj x9 x10 ↔ ∃ x11 ∈ x3, x9 = Fin.castAdd x2 x11.1 ∧ x10 = Fin.natAdd x1 x11.2 ∨ x10 = Fin.castAdd x2 x11.1 ∧ x9 = Fin.natAdd x1 x11.2) ∧ x8.edgeSet.ncard = x3.card ∧ ∀ (x9 : Finset (Fin (x1 + x2))), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover x8 x9 → x4.card ≤ x9.card := by
  classical
  intro n m E M hME hleft hright
  let edge (p : Fin n × Fin m) : Sym2 (Fin (n + m)) :=
    s(Fin.castAdd m p.1, Fin.natAdd n p.2)
  have separate (a : Fin n) (b : Fin m) : Fin.castAdd m a ≠ Fin.natAdd n b := by
    intro h
    have hh := congrArg Fin.val h
    change a.val = n + b.val at hh
    omega
  have inject : Function.Injective edge := by
    intro p q h
    rcases Sym2.eq_iff.mp h with h | h
    · exact Prod.ext (Fin.castAdd_injective _ _ h.1) (by simpa using h.2)
    · exact (separate _ _ h.1).elim
  let edges := edge '' (E : Set (Fin n × Fin m))
  let G := SimpleGraph.fromEdgeSet edges
  have adj (u v : Fin (n + m)) : G.Adj u v ↔ ∃ e ∈ E,
      u = Fin.castAdd m e.1 ∧ v = Fin.natAdd n e.2 ∨
      v = Fin.castAdd m e.1 ∧ u = Fin.natAdd n e.2 := by
    constructor
    · rintro ⟨⟨e, he, h⟩, _⟩
      rcases Sym2.eq_iff.mp h with h | h
      · exact ⟨e, he, Or.inl ⟨h.1.symm, h.2.symm⟩⟩
      · exact ⟨e, he, Or.inr ⟨h.1.symm, h.2.symm⟩⟩
    · rintro ⟨e, he, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
      · exact ⟨⟨e, he, rfl⟩, separate _ _⟩
      · exact ⟨⟨e, he, Sym2.eq_swap⟩, Ne.symm (separate _ _)⟩
  refine ⟨G, adj, ?_, ?_⟩
  · have hedge : G.edgeSet = edges := by
      rw [SimpleGraph.edgeSet_fromEdgeSet]
      ext x
      constructor
      · exact fun h => h.1
      · rintro ⟨p, hp, rfl⟩
        exact ⟨⟨p, hp, rfl⟩, separate _ _⟩
    rw [hedge, Set.ncard_image_of_injective _ inject, Set.ncard_coe_finset]
  · intro S cover
    let pick (p : Fin n × Fin m) := if Fin.castAdd m p.1 ∈ S then Fin.castAdd m p.1 else Fin.natAdd n p.2
    apply Finset.card_le_card_of_injOn pick
    · intro p hp
      have incident := cover _ _ ((adj _ _).2 ⟨p, hME hp, Or.inl ⟨rfl, rfl⟩⟩)
      by_cases h : Fin.castAdd m p.1 ∈ S
      · simpa [pick, h] using h
      · simpa [pick, h] using incident.resolve_left h
    · intro p hp q hq heq
      dsimp only [pick] at heq
      split at heq <;> split at heq
      · exact hleft p hp q hq (Fin.castAdd_injective _ _ heq)
      · exact (separate _ _ heq).elim
      · exact (separate _ _ heq.symm).elim
      · exact hright p hp q hq (by simpa using heq)

import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import PEqualNP.Defs

-- The wiring and monotonicity lemmas follow the checked L_meta_2902.

namespace PEqualNP.Outside.L_meta_3684

open PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_start (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_start gs w
  rw [ht]; simp [hl]

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_start gs w
  rw [ht, List.getD_append _ _ _ _ h]

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

def MOk (g : Gate) : Prop := (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2
theorem gate_mono (g : Gate) (hg : MOk g) (w w' : List Bool)
    (h : ∀ i, w.getD i false = true → w'.getD i false = true) :
    g.op.eval (g.inputs.map fun i => w.getD i false) = true →
    g.op.eval (g.inputs.map fun i => w'.getD i false) = true := by
  obtain ⟨op, inp⟩ := g
  rcases hg.1 with e | e
  · have e : op = GateOp.and := e
    subst e
    simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
    exact fun H a ha => h a (H a ha)
  · have e : op = GateOp.or := e
    subst e
    simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
    exact fun ⟨a, ha, H⟩ => ⟨a, ha, h a H⟩

theorem wires_mono (gs : List Gate) : ∀ w w' : List Bool, (∀ g ∈ gs, MOk g) →
    w.length = w'.length → (∀ i, w.getD i false = true → w'.getD i false = true) →
    ∀ i, (wiresFrom gs w).getD i false = true → (wiresFrom gs w').getD i false = true := by
  induction gs with
  | nil => intro w w' _ _ h; exact h
  | cons g gs ih =>
    intro w w' hok hl h
    refine ih (w ++ [_]) (w' ++ [_]) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (by simp [hl]) ?_
    intro i
    by_cases hil : i = w.length
    · rw [hil, getD_snoc_eq, hl, getD_snoc_eq]
      exact gate_mono g (hok g List.mem_cons_self) w w' h
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      exact h i

theorem getD_ofFn' {α : Type} (m : ℕ) (f : Fin m → α) (d : α) (j : Fin m) :
    (List.ofFn f).getD j.val d = f j := by
  simp [List.getD_eq_getElem?_getD]

theorem localMono (g : Gate) (h : MOk g) (a b : List Bool)
    (ht : ∀ i ∈ g.inputs, a.getD i false = true → b.getD i false = true) :
    g.op.eval (g.inputs.map fun i => a.getD i false) = true →
    g.op.eval (g.inputs.map fun i => b.getD i false) = true := by
  obtain ⟨op, ins⟩ := g
  rcases h.1 with e | e
  · have e : op = GateOp.and := e
    subst e
    simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
    exact fun H i hi => ht i hi (H i hi)
  · have e : op = GateOp.or := e
    subst e
    simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
    exact fun ⟨i, hi, ha⟩ => ⟨i, hi, ht i hi ha⟩

def exclusive (a b : List Bool) (i : ℕ) := a.getD i false = true ∧ b.getD i false = false

theorem firstRead (gs : List Gate) (a b : List Bool) (z : ℕ) (hl : a.length = b.length)
    (root : ∀ i, exclusive a b i → i = z) (ok : ∀ g ∈ gs, MOk g) :
    (∃ j : Fin gs.length, z ∈ (gs.get j).inputs ∧
      exclusive (wiresFrom gs a) (wiresFrom gs b) (a.length + j.val)) ∨
    (∀ i, exclusive (wiresFrom gs a) (wiresFrom gs b) i → i = z) := by
  induction gs using List.reverseRecOn with
  | nil => exact Or.inr root
  | append_singleton gs g ih =>
    let A := wiresFrom gs a
    let B := wiresFrom gs b
    let va := g.op.eval (g.inputs.map fun i => A.getD i false)
    let vb := g.op.eval (g.inputs.map fun i => B.getD i false)
    have hA : wiresFrom (gs ++ [g]) a = A ++ [va] := wiresFrom_append ..
    have hB : wiresFrom (gs ++ [g]) b = B ++ [vb] := wiresFrom_append ..
    have la : A.length = a.length + gs.length := length_wiresFrom ..
    have lb : B.length = a.length + gs.length := by dsimp [B]; rw [length_wiresFrom, ← hl]
    have old (i : ℕ) (hi : i ≠ a.length + gs.length) :
        exclusive (A ++ [va]) (B ++ [vb]) i ↔ exclusive A B i := by
      simp only [exclusive, getD_snoc_ne _ _ _ _ (show i ≠ A.length by omega),
        getD_snoc_ne _ _ _ _ (show i ≠ B.length by omega)]
    rw [hA, hB]
    rcases ih (fun g' h => ok g' (by simp [h])) with ⟨j, hj, hx⟩ | ih
    · let k : Fin (gs ++ [g]).length := ⟨j, by simp⟩
      refine Or.inl ⟨k, ?_, (old _ (by dsimp [k]; omega)).2 hx⟩
      simpa [List.get_eq_getElem, k, List.getElem_append_left] using hj
    · by_cases newGate : va = true ∧ vb = false
      · have read : z ∈ g.inputs := by
          by_contra hz
          have ht := localMono g (ok g (by simp)) A B (fun i hi hia => by
            cases h : B.getD i false with
            | true => rfl
            | false => exact False.elim (hz (ih i ⟨hia, h⟩ ▸ hi))) newGate.1
          change vb = true at ht
          simp [newGate.2] at ht
        let k : Fin (gs ++ [g]).length := ⟨gs.length, by simp⟩
        refine Or.inl ⟨k, ?_, ?_⟩
        · simpa [List.get_eq_getElem, k] using read
        · change (A ++ [va]).getD (a.length + gs.length) false = true ∧
                   (B ++ [vb]).getD (a.length + gs.length) false = false
          constructor
          · rw [← la, getD_snoc_eq]; exact newGate.1
          · rw [← lb, getD_snoc_eq]; exact newGate.2
      · refine Or.inr (fun i hi => ?_)
        by_cases eq : i = a.length + gs.length
        · subst i
          unfold exclusive at hi
          rw [← la, getD_snoc_eq, show A.length = B.length by omega, getD_snoc_eq] at hi
          exact False.elim (newGate hi)
        · exact ih i ((old i eq).1 hi)

def allPoints (n : ℕ) (k : Fin (n + n)) : Bool :=
  Fin.addCases (fun _ : Fin n => true) (fun _ : Fin n => false) k

def flag {n : ℕ} (p l : Fin n) : Fin (n + n) → Bool :=
  PEqualNP.EdgeOwnership.pairInput (Fin.castAdd n p) (Fin.natAdd n l)

theorem rawExclusive {n : ℕ} (p l : Fin n) (i : ℕ)
    (h : exclusive (List.ofFn (flag p l)) (List.ofFn (allPoints n)) i) : i = n + l.val := by
  obtain ⟨hp, hn⟩ := h
  by_cases hi : i < n + n
  · let k : Fin (n + n) := ⟨i, hi⟩
    change (List.ofFn _).getD k.val false = true at hp
    change (List.ofFn _).getD k.val false = false at hn
    rw [getD_ofFn'] at hp hn
    change decide (k = Fin.castAdd n p ∨ k = Fin.natAdd n l) = true at hp
    rcases of_decide_eq_true hp with h | h
    · rw [h] at hn
      simp [allPoints] at hn
    · exact congrArg Fin.val h
  · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hi)] at hp
    contradiction

theorem rawOutput {C D : Circuit} {input : List Bool} (he : C.output = D.output)
    (yes : C.eval input = true) (no : D.eval input = false) : input.length ≤ C.output := by
  by_contra! h
  have e : D.output < input.length := he ▸ h
  rw [Circuit.eval, wires_eq, getD_wiresFrom _ _ _ h, he] at yes
  rw [Circuit.eval, wires_eq, getD_wiresFrom _ _ _ e] at no
  exact Bool.noConfusion (yes.symm.trans no)

theorem zeroMono (gs : List Gate) (ok : ∀ g ∈ gs, MOk g) (b : List Bool) (i : ℕ) :
    (wiresFrom gs (List.replicate b.length false)).getD i false = true →
    (wiresFrom gs b).getD i false = true :=
  wires_mono gs _ _ ok (by simp) (fun k hk => by
    simp [List.getD_eq_getElem?_getD] at hk) i

theorem lineRead (n : ℕ) (C D : Circuit) (eqOut : C.output = D.output)
    (mono : Monotone2 C) (points : C.eval (List.ofFn (allPoints n)) = false)
    (p l : Fin n) (hy : C.eval (List.ofFn (flag p l)) = true)
    (hn : D.eval (List.ofFn (flag p l)) = false) :
    ∃ j : Fin C.size, n + l.val ∈ (C.gates.get j).inputs ∧
      (C.wires (List.replicate (n + n) false)).getD (n + n + j.val) false = false ∧
      PEqualNP.EdgeOwnership.gateVal (n + n) C j.val (flag p l) = true := by
  have ok : ∀ g ∈ C.gates, MOk g := fun g hg => ⟨(mono g hg).1, (mono g hg).2⟩
  obtain h | h := firstRead C.gates (List.ofFn (flag p l)) (List.ofFn (allPoints n))
    (n + l.val) (by simp) (rawExclusive p l) ok
  · obtain ⟨j, hj, hy', hn'⟩ := h
    simp only [List.length_ofFn] at hy' hn'
    refine ⟨j, hj, ?_, hy'⟩
    cases hz : (C.wires (List.replicate (n + n) false)).getD (n + n + j.val) false with
    | false => rfl
    | true =>
      have hz' := zeroMono C.gates ok (List.ofFn (allPoints n)) (n + n + j.val)
      simp only [List.length_ofFn] at hz'
      have hh := hz' hz
      exact hh.symm.trans hn'
  · have he := h C.output ⟨hy, points⟩
    have hlen := rawOutput eqOut hy hn
    simp only [List.length_ofFn] at hlen
    omega

lemma card_le_twice {α β : Type} [DecidableEq β]
    (lines : Finset α) (gates : Finset β) (charge : α → β)
    (maps : ∀ l ∈ lines, charge l ∈ gates)
    (fiber : ∀ j ∈ gates, (lines.filter (fun l => charge l = j)).card ≤ 2) :
    lines.card ≤ 2 * gates.card := by
  calc
    lines.card = ∑ j ∈ gates, (lines.filter (fun l => charge l = j)).card :=
      Finset.card_eq_sum_card_fiberwise maps
    _ ≤ ∑ _j ∈ gates, 2 := Finset.sum_le_sum fiber
    _ = 2 * gates.card := by simp [Nat.mul_comm]


end PEqualNP.Outside.L_meta_3684

open PEqualNP.Outside.L_meta_3684 in
theorem PEqualNP.Outside.L_meta_3684 : ∀ (x1 : ℕ) (x2 x3 : PEqualNP.CircuitLowerBounds.Circuit),   x2.output = x3.output →     PEqualNP.MetaComplexity.Monotone2 x2 →       x2.eval (List.ofFn fun (x6 : Fin (x1 + x1)) => Fin.addCases (fun (_ : Fin x1) => Bool.true) (fun (_ : Fin x1) => Bool.false) x6) = Bool.false →         have x7 : Fin x1 → Fin x1 → Fin (x1 + x1) → Bool := fun (x7 x8 : Fin x1) => PEqualNP.EdgeOwnership.pairInput (Fin.castAdd x1 x7) (Fin.natAdd x1 x8);         ∀ (x8 : Fin x1 → Finset (Fin x1)), (∀ (x9 x10 : Fin x1), x10 ∈ x8 x9 → x2.eval (List.ofFn (x7 x10 x9)) = Bool.true ∧ x3.eval (List.ofFn (x7 x10 x9)) = Bool.false) → Fintype.card { x10 : Fin x1 // (x8 x10).Nonempty } ≤ (2 : ℕ) * Fintype.card { x10 : Fin x2.size // (x2.wires (List.replicate (x1 + x1) Bool.false)).getD (x1 + x1 + ↑x10) Bool.false = Bool.false ∧ ∃ (x11 : Fin x1), ∃ x12 ∈ x8 x11, PEqualNP.EdgeOwnership.gateVal (x1 + x1) x2 (↑x10) (x7 x12 x11) = Bool.true } := by
  classical
  intro n C D he mono pts
  dsimp only
  intro lines h
  let L := {l : Fin n // (lines l).Nonempty}
  let J := {j : Fin C.size //
    (C.wires (List.replicate (n + n) false)).getD (n + n + j.val) false = false ∧
    ∃ (l : Fin n), ∃ p ∈ lines l,
      PEqualNP.EdgeOwnership.gateVal (n + n) C j.val (flag p l) = true}
  change Fintype.card L ≤ 2 * Fintype.card J
  have read (l : L) : ∃ j : J, n + l.val.val ∈ (C.gates.get j.val).inputs := by
    obtain ⟨p, hp⟩ := l.property
    obtain ⟨hy, hn⟩ := h l.val p hp
    obtain ⟨j, hj, zero, hit⟩ := lineRead n C D he mono pts p l.val hy hn
    exact ⟨⟨j, zero, l.val, p, hp, hit⟩, hj⟩
  choose charge rd using read
  have bound := card_le_twice (Finset.univ : Finset L) (Finset.univ : Finset J) charge
    (by simp) (fun j _ => by
      calc
        (Finset.univ.filter (fun l : L => charge l = j)).card ≤
            (C.gates.get j.val).inputs.toFinset.card := by
          apply Finset.card_le_card_of_injOn (fun (l : L) => n + l.val.val)
          · intro l hl
            have eq := (Finset.mem_filter.1 hl).2
            exact List.mem_toFinset.2 (eq ▸ rd l)
          · intro l _ k _ eq
            exact Subtype.ext (Fin.ext (Nat.add_left_cancel eq))
        _ ≤ (C.gates.get j.val).inputs.length := List.toFinset_card_le _
        _ ≤ 2 := (mono _ (List.get_mem ..)).2)
  simpa using bound

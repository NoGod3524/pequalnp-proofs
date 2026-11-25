import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_670_aux

-- Small-graph certificates adapted from dsgallups, PR 8157, including its credited 1667 source.
namespace PublicFloor
open PEqualNP.CircuitLowerBounds

abbrev Sig := BitVec 512

def zero : Sig := 0

def one : Sig := BitVec.allOnes 512

def neg (a : Sig) : Sig := ~~~a

def bin (d : Nat) (a b : Sig) : Sig :=
  if d=0 then a &&& b else if d=1 then a ||| b else if d=2 then a &&& ~~~b else ~~~a &&& b

def proper (a : Sig) : Prop := a ≠ zero ∧ a ≠ one

def allowed (u : Bool) (d : Nat) : Prop := d<2 ∨ (u=true ∧ d<4)

def flipOp (d : Nat) := if d=2 then 3 else if d=3 then 2 else d

theorem allowed_four {u d} (h : allowed u d) : d=0 ∨ d=1 ∨ (u=true ∧ d=2) ∨ (u=true ∧ d=3) := by
  rcases h with h | ⟨h,j⟩
  · omega
  · have : d=0 ∨ d=1 ∨ d=2 ∨ d=3 := by omega
    rcases this with h1 | h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr (Or.inl ⟨h,h1⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨h,h1⟩))

theorem bin_flip {u d} (h : allowed u d) (a b : Sig) : bin d a b = bin (flipOp d) b a := by
  rcases allowed_four h with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩ <;> simp [bin,flipOp,BitVec.and_comm,BitVec.or_comm]

theorem flip_flip {u d} (h : allowed u d) : allowed u (flipOp d) ∧ flipOp (flipOp d)=d := by
  rcases allowed_four h with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
  all_goals simp_all [flipOp,allowed]

def Live (u : Bool) (target : Sig) : Nat → Finset Sig → Prop
  | 0,S => S={target} ∧ proper target
  | k+1,S => ∃ (U : Finset Sig) (a b : Sig) (d : Nat), allowed u d ∧ S=insert a (insert b U) ∧
      proper a ∧ proper b ∧ a ≠ b ∧
      bin d a b ∉ insert a (insert b U) ∧ Live u target k (insert (bin d a b) U)

theorem Live.stop {u} {target : Sig} (hp : proper target) : Live u target 0 {target} := ⟨rfl,hp⟩

theorem Live.binary {u} {target : Sig} {k : Nat} {U : Finset Sig} {a b : Sig} {d : Nat} (hd : allowed u d)
    (ha : proper a) (hb : proper b) (hab : a ≠ b)
    (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live u target k (insert (bin d a b) U)) :
    Live u target (k+1) (insert a (insert b U)) :=
  ⟨U,a,b,d,hd,rfl,ha,hb,hab,hfresh,tail⟩

theorem Live.ind {u} {target : Sig} {motive : ∀ (k : Nat) (S : Finset Sig), Live u target k S → Prop}
    (stop : ∀ (hp : proper target), motive 0 {target} (Live.stop hp))
    (binary : ∀ {k : Nat} {U : Finset Sig} {a b : Sig} {d : Nat} (hd : allowed u d)
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live u target k (insert (bin d a b) U)),
      motive k (insert (bin d a b) U) tail →
      motive (k+1) (insert a (insert b U)) (Live.binary hd ha hb hab hfresh tail))
    {k : Nat} {S : Finset Sig} (h : Live u target k S) : motive k S h := by
  induction k generalizing S with
  | zero =>
    obtain ⟨rfl,hp⟩ := h
    exact stop hp
  | succ k ih =>
    obtain ⟨U,a,b,d,hd,rfl,ha,hb,hab,hf,tail⟩ := h
    exact binary hd ha hb hab hf tail (ih tail)

lemma live_proper {u target k S} (h : Live u target k S) : ∀ a ∈ S, proper a := by
  induction h using Live.ind with
  | stop hp => simpa using hp
  | binary hd ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩

lemma live_size {u target k S} (h : Live u target k S) : S.card ≤ k+1 := by
  induction h using Live.ind with
  | stop hp => simp
  | @binary k U a b d hd ha hb hab hf _ ih =>
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a := a) (s := insert b U)
    have h2 := Finset.card_insert_le (a := b) (s := U)
    omega

def bit (i : Fin 512) (a : Sig) : Bool := a.getLsbD i.val

lemma bit_zero (i) : bit i zero = false := by simp [bit,zero]

lemma bit_one (i) : bit i one = true := by unfold bit one; rw [BitVec.getLsbD_allOnes]; simp

lemma bit_neg (i) (a : Sig) : bit i (neg a) = !(bit i a) := by simp [bit,neg,i.isLt]

lemma bit_bin (i d) (a b : Sig) : bit i (bin d a b) =
    (if d=0 then bit i a && bit i b else if d=1 then bit i a || bit i b else
      if d=2 then bit i a && !(bit i b) else !(bit i a) && bit i b) := by
  unfold bin
  split_ifs <;> simp [bit]

theorem bit_ext {a b : Sig} (h : ∀ i, bit i a = bit i b) : a=b :=
  BitVec.eq_of_getLsbD_eq fun j hj => h ⟨j,hj⟩

def nrm (u : Bool) (a : Sig) : Sig := if u && bit 0 a then neg a else a

theorem nrm_false (a : Sig) : nrm false a = a := rfl

theorem nrm_bit (a : Sig) : bit 0 (nrm true a) = false := by
  cases h : bit 0 a <;> simp [nrm,h,bit_neg]

theorem nrm_id {u} {a : Sig} (h : bit 0 a = false) : nrm u a = a := by simp [nrm,h]

theorem neg_neg' (a : Sig) : neg (neg a) = a := by simp [neg]

theorem nrm_neg (a : Sig) : nrm true (neg a) = nrm true a := by
  cases h : bit 0 a <;> simp [nrm,h,bit_neg,neg_neg']

theorem proper_neg {a : Sig} (h : proper (neg a)) : proper a := by
  refine ⟨?_,?_⟩
  · rintro rfl
    exact h.2 (by simp [neg,zero,one])
  · rintro rfl
    exact h.1 (by simp [neg,zero,one])

theorem proper_nrm {u} {a : Sig} (h : proper (nrm u a)) : proper a := by
  unfold nrm at h
  split at h
  · exact proper_neg h
  · exact h

def prime (d : Bool) (a b : Sig) := if d then a ||| b else a &&& b

theorem bit_prime (i) (d : Bool) (a b : Sig) : bit i (prime d a b) =
    (if d then bit i a || bit i b else bit i a && bit i b) := by cases d <;> simp [prime,bit]

theorem nrm_prime (d : Bool) (a b : Sig) :
    ∃ e, e<4 ∧ nrm true (prime d a b) = bin e (nrm true a) (nrm true b) := by
  refine ⟨if d then (if bit 0 a then (if bit 0 b then 0 else 2) else (if bit 0 b then 3 else 1))
    else (if bit 0 a then (if bit 0 b then 1 else 3) else (if bit 0 b then 2 else 0)),?_,?_⟩
  · split_ifs <;> omega
  · apply bit_ext
    intro i
    cases d <;> cases ha : bit 0 a <;> cases hb : bit 0 b <;>
      simp only [nrm,bit_prime,ha,hb,bit_bin,bit_neg,Bool.true_and,Bool.false_and,Bool.and_true,Bool.and_false,Bool.false_or,
        Bool.or_false,Bool.true_or,Bool.or_true,Bool.false_eq_true,ite_true,ite_false] <;>
      cases hx : bit i a <;> cases hy : bit i b <;> simp [hx,hy,bit_neg,bit_prime]

def gv (w : List Sig) (g : Gate) : Sig :=
  let xs := g.inputs.map (fun i => w.getD i zero)
  match g.op with
  | .and => xs.foldr (prime false) one
  | .or => xs.foldr (prime true) zero
  | .not => neg (xs.headD zero)
  | _ => zero

def execute (gs : List Gate) (w : List Sig) : List Sig :=
  gs.foldl (fun l g => l ++ [gv l g]) w

def represented (w : List Sig) (v : Sig) : Prop := v ∈ w ∨ ¬proper v

def Repr (u : Bool) (w : List Sig) (v : Sig) : Prop := represented w (nrm u v)

lemma bin_laws (a : Sig) :
    bin 0 a one = a ∧ bin 1 a zero = a ∧
    bin 0 a zero = zero ∧ bin 1 a one = one ∧
    bin 0 a a = a ∧ bin 1 a a = a ∧ bin 2 a a = zero ∧ bin 3 a a = zero ∧ bin 2 a zero = a ∧
    bin 3 zero a = a ∧ bin 2 zero a = zero ∧ bin 3 a zero = zero ∧ bin 0 zero a = zero ∧ bin 1 zero a = a ∧
    bin 0 one a = a ∧ bin 1 one a = one := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> apply bit_ext <;> intro i <;>
    simp [bit_bin,bit_zero,bit_one]

lemma operand_cases {w : List Sig} {a : Sig} (h : represented w a) :
    a = zero ∨ a = one ∨ a ∈ w ∧ proper a := by
  by_cases hz : a = zero
  · exact Or.inl hz
  by_cases ho : a = one
  · exact Or.inr (Or.inl ho)
  exact Or.inr (Or.inr ⟨h.resolve_right (fun x => x ⟨hz,ho⟩),hz,ho⟩)

def witness (u : Bool) (w : List Sig) (z : Sig) : Prop :=
  ∃ d a b, allowed u d ∧ a ∈ w ∧ b ∈ w ∧ proper a ∧ proper b ∧ a ≠ b ∧ z = bin d a b

lemma bin_rep {u w a b} (d : Nat) (hd : allowed u d) (ha : represented w a) (hb : represented w b)
    (no : u=true → a ≠ one ∧ b ≠ one) :
    represented w (bin d a b) ∨ witness u w (bin d a b) := by
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  obtain ⟨a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16⟩ := bin_laws a
  obtain ⟨b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15,b16⟩ := bin_laws b
  by_cases he : a=b
  · subst b
    left
    rcases allowed_four hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact a5.symm ▸ ha
    · exact a6.symm ▸ ha
    · exact a7.symm ▸ rz
    · exact a8.symm ▸ rz
  rcases operand_cases ha with rfl | rfl | ⟨ham,hap⟩
  · left
    rcases allowed_four hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact b13.symm ▸ rz
    · exact b14.symm ▸ hb
    · exact b11.symm ▸ rz
    · exact b10.symm ▸ hb
  · left
    rcases allowed_four hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
    · exact b15.symm ▸ hb
    · exact b16.symm ▸ ro
    · exact absurd rfl (no hu).1
    · exact absurd rfl (no hu).1
  rcases operand_cases hb with rfl | rfl | ⟨hbm,hbp⟩
  · left
    rcases allowed_four hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact a3.symm ▸ rz
    · exact a2.symm ▸ ha
    · exact a9.symm ▸ ha
    · exact a12.symm ▸ rz
  · left
    rcases allowed_four hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
    · exact a1.symm ▸ ha
    · exact a4.symm ▸ ro
    · exact absurd rfl (no hu).2
    · exact absurd rfl (no hu).2
  exact Or.inr ⟨d,a,b,hd,ham,hbm,hap,hbp,he,rfl⟩

theorem norm_ne_one (a : Sig) : nrm true a ≠ one := by
  intro h
  have := nrm_bit a
  rw [h,bit_one] at this
  exact Bool.noConfusion this

theorem prime_rep {u w a b} (d : Bool) (ha : Repr u w a) (hb : Repr u w b) :
    Repr u w (prime d a b) ∨ witness u w (nrm u (prime d a b)) := by
  cases u
  · have e : prime d a b = bin (if d then 1 else 0) a b := by cases d <;> rfl
    have h := bin_rep (u:=false) (if d then 1 else 0) (Or.inl (by split <;> omega)) ha hb (by simp)
    unfold Repr
    simp only [nrm_false] at h ⊢
    rwa [e]
  · obtain ⟨e,he,eq⟩ := nrm_prime d a b
    unfold Repr
    rw [eq]
    exact bin_rep e (Or.inr ⟨rfl,he⟩) ha hb (fun _ => ⟨norm_ne_one a,norm_ne_one b⟩)

theorem repr_const {u w} {v : Sig} (h : v=zero ∨ v=one) : Repr u w v := by
  refine Or.inr fun hp => ?_
  have := proper_nrm hp
  rcases h with rfl | rfl
  · exact this.1 rfl
  · exact this.2 rfl

lemma pull_gate {u target} {w : List Sig} {z : Sig} {k S c} (h : Live u target k S)
    (hz : represented w z ∨ (c=1 ∧ witness u w z)) (sub : ∀ a ∈ S, a ∈ w++[z]) :
    ∃ k' S', k' ≤ k+c ∧ Live u target k' S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k,S,by omega,h,?_⟩
      intro a ha
      have hu : a ∈ w ∨ a = z := by simpa using sub a ha
      rcases hu with hu | rfl
      · exact hu
      · exact hw
    · have hp := live_proper h z hm
      rcases hz with hr | ⟨rfl,d,a,b,hd,ha,hb,pa,pb,hab,eq⟩
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U := S.erase (bin d a b)
        have ht : Live u target k (insert (bin d a b) U) := by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv
          obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf : bin d a b ∉ insert a (insert b U) := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          rcases Finset.mem_insert.mp u with eq | u
          · exact hw (eq.symm ▸ hb)
          · exact hw (hu _ u)
        exact ⟨_,_,Nat.le_refl _,Live.binary hd pa pb hab hf ht,by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k,S,by omega,h,?_⟩
    intro a ha
    have hn : a ≠ z := fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha

lemma b_read (i) (w : List Sig) (j : Nat) :
    (w.map (bit i)).getD j false = bit i (w.getD j zero) := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases w[j]? with
  | none => exact (bit_zero _).symm
  | some a => rfl

lemma run_bit (i) (g : Gate) (w : List Sig)
    (hg : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    bit i (gv w g) = g.op.eval (g.inputs.map fun j => (w.map (bit i)).getD j false) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hg
  simp only [b_read]
  rcases hg with rfl | rfl | rfl
  · induction l with
    | nil => exact bit_one _
    | cons a l ih =>
      change bit i (prime false _ _) = (_ && _)
      rw [bit_prime]; exact congrArg (fun x => bit i (w.getD a zero) && x) ih
  · induction l with
    | nil => exact bit_zero _
    | cons a l ih =>
      change bit i (prime true _ _) = (_ || _)
      rw [bit_prime]; exact congrArg (fun x => bit i (w.getD a zero) || x) ih
  · cases l with
    | nil =>
      change bit i (neg zero) = !false
      rw [bit_neg,bit_zero]
    | cons a l => exact bit_neg _ _

lemma execute_bits (gs : List Gate) (i) (w : List Sig)
    (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    (execute gs w).map (bit i) =
    gs.foldl (fun (l : List Bool) g => l++[g.op.eval (g.inputs.map fun j => l.getD j false)]) (w.map (bit i)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (execute gs (w++[gv w g])).map _ = _
    rw [ih _ (fun a ha => hg a (by simp [ha]))]
    simp only [List.foldl_cons,List.map_append,List.map_singleton,run_bit i g w (hg g (by simp))]

abbrev Wire (R : Type) := R → Bool

def inv {R} (a : Wire R) : Wire R := fun r => !(a r)

def combine {R} (isOr : Bool) (a b : Wire R) : Wire R :=
  if isOr then fun r => a r || b r else fun r => a r && b r

def comb {R} (d : Nat) (a b : Wire R) : Wire R :=
  if d=0 then combine false a b else if d=1 then combine true a b else
    if d=2 then combine false a (inv b) else combine false (inv a) b

def Constant {R} (a : Wire R) : Prop := ∃ b : Bool, a = fun _ => b

noncomputable def cost {R} (a : Wire R) : Nat := by
  classical exact if Constant a then 1 else 0

noncomputable def mass {R} (xs : List (Wire R)) : Nat := (xs.map cost).sum

def Available {R} (u : Bool) (pool : List (Wire R)) (v : Wire R) : Prop :=
  v ∈ pool ∨ Constant v ∨ (u=true ∧ inv v ∈ pool)

def supply {R} (u : Bool) (pool xs : List (Wire R)) := ∀ a ∈ xs, Available u pool a

def Reach {R} (u : Bool) (roots : List (Wire R)) : Nat → List (Wire R) → Prop
  | 0,b => b=roots
  | p+1,c => ∃ (op : Bool) (bank : List (Wire R)) (a b : Wire R), Reach u roots p bank ∧ Available u bank a ∧
      Available u bank b ∧ c=combine op a b :: bank

theorem Reach.start {R u} {roots : List (Wire R)} : Reach u roots 0 roots := rfl

theorem Reach.two {R u} {roots : List (Wire R)} {p bank a b} (op : Bool) (h : Reach u roots p bank)
    (ha : Available u bank a) (hb : Available u bank b) : Reach u roots (p+1) (combine op a b :: bank) :=
  ⟨op,bank,a,b,h,ha,hb,rfl⟩

theorem Reach.ind {R u} {roots : List (Wire R)} {motive : ∀ p bank, Reach u roots p bank → Prop}
    (start : motive 0 roots Reach.start)
    (two : ∀ {p bank a b} (op : Bool) (h : Reach u roots p bank) (ha : Available u bank a)
      (hb : Available u bank b), motive p bank h →
      motive (p+1) (combine op a b :: bank) (Reach.two op h ha hb))
    {p bank} (h : Reach u roots p bank) : motive p bank h := by
  induction p generalizing bank with
  | zero =>
    obtain rfl := h
    exact start
  | succ p ih =>
    obtain ⟨op,bank,a,b,h,ha,hb,rfl⟩ := h
    exact two op h ha hb (ih h)

def kept {α : Type} (save : Bool) (x : α) (xs : List α) := if save then x::xs else xs

def Run {R} (u : Bool) (goal : Wire R) : Nat → List (Wire R) → Prop
  | 0,zs => List.Perm [goal] zs
  | s+1,zs => ∃ (op : Nat) (ka kb : Bool) (a b : Wire R) (rest : List (Wire R)), allowed u op ∧ (a::b::rest).Perm zs ∧
      Run u goal s (comb op a b :: kept ka a (kept kb b rest))

theorem Run.stop {R u} {goal : Wire R} : Run u goal 0 [goal] := List.Perm.refl _

theorem Run.perm {R u} {goal : Wire R} {s : Nat} {xs zs : List (Wire R)} (p : xs.Perm zs)
    (h : Run u goal s xs) : Run u goal s zs := by
  cases s with
  | zero => exact List.Perm.trans h p
  | succ s =>
    obtain ⟨op,ka,kb,a,b,rest,hd,q,h⟩ := h
    exact ⟨op,ka,kb,a,b,rest,hd,q.trans p,h⟩

theorem Run.two {R u} {goal : Wire R} {s : Nat} {a b : Wire R} {rest : List (Wire R)} (op : Nat) (hd : allowed u op) (ka kb : Bool)
    (h : Run u goal s (comb op a b :: kept ka a (kept kb b rest))) : Run u goal (s+1) (a::b::rest) :=
  ⟨op,ka,kb,a,b,rest,hd,List.Perm.refl _,h⟩

theorem Run.ind {R u} {goal : Wire R} {motive : ∀ s ws, Run u goal s ws → Prop}
    (stop : motive 0 [goal] Run.stop)
    (perm : ∀ {s xs zs} (p : List.Perm xs zs) (h : Run u goal s xs), motive s xs h → motive s zs (Run.perm p h))
    (two : ∀ {s a b rest} (op : Nat) (hd : allowed u op) (ka kb : Bool) (h : Run u goal s (comb op a b :: kept ka a (kept kb b rest))),
      motive s _ h → motive (s+1) (a::b::rest) (Run.two op hd ka kb h))
    {s ws} (h : Run u goal s ws) : motive s ws h := by
  induction s generalizing ws with
  | zero => exact perm h Run.stop stop
  | succ s ih =>
    obtain ⟨op,ka,kb,a,b,rest,hd,p,h⟩ := h
    exact perm p (Run.two op hd ka kb h) (two op hd ka kb h (ih h))

theorem mass_cons {R} (a : Wire R) (xs) : mass (a::xs)=cost a + mass xs := by
  simp [mass]

theorem mass_kept {R} (a : Wire R) (xs) (k : Bool) : mass xs ≤ mass (kept k a xs) := by
  cases k <;> simp [kept,mass_cons]

theorem inv_constant {R} {a : Wire R} (h : Constant a) : Constant (inv a) := by
  obtain ⟨v,rfl⟩ := h
  exact ⟨!v,rfl⟩

theorem inv_inv' {R} (a : Wire R) : inv (inv a)=a := by
  funext r
  simp [inv]

theorem cost_inv {R} (a : Wire R) : cost (inv a)=cost a := by
  have : Constant (inv a) ↔ Constant a := ⟨fun h => inv_inv' a ▸ inv_constant h,inv_constant⟩
  by_cases h : Constant a
  · simp only [cost,if_pos h,if_pos (this.mpr h)]
  · simp only [cost,if_neg h,if_neg (fun x => h (this.mp x))]

theorem avail_inv {R u} {bank : List (Wire R)} {a} (hu : u=true) (h : Available u bank a) : Available u bank (inv a) := by
  rcases h with h | h | ⟨_,h⟩
  · exact Or.inr (Or.inr ⟨hu,(inv_inv' a).symm ▸ h⟩)
  · exact Or.inr (Or.inl (inv_constant h))
  · exact Or.inl h

theorem both_constant {R} {a b : Wire R} (op) (h : Constant a) (g : Constant b) :
    Constant (combine op a b) := by
  obtain ⟨v,rfl⟩ := h
  obtain ⟨w,rfl⟩ := g
  cases op <;> exact ⟨_,rfl⟩

theorem from_constant {R u} (op) {a b : Wire R} {bank}
    (h : Constant a ∨ Constant b) (ha : Available u bank a) (hb : Available u bank b) :
    Available u bank (combine op a b) := by
  rcases h with ⟨v,rfl⟩ | ⟨v,rfl⟩
  · cases op <;> cases v
    · exact Or.inr (Or.inl ⟨false, by funext x; simp [combine]⟩)
    · simpa [combine] using hb
    · simpa [combine] using hb
    · exact Or.inr (Or.inl ⟨true, by funext x; simp [combine]⟩)
  · cases op <;> cases v
    · exact Or.inr (Or.inl ⟨false, by funext x; simp [combine]⟩)
    · simpa [combine] using ha
    · simpa [combine] using ha
    · exact Or.inr (Or.inl ⟨true, by funext x; simp [combine]⟩)

theorem available_cons {R u} {bank v} (w : Wire R) (h : Available u bank v) :
    Available u (w::bank) v :=
  h.imp (List.mem_cons_of_mem _) (Or.imp id (And.imp id (List.mem_cons_of_mem _)))

theorem extend_two {R u} (roots : List (Wire R)) {p bank a b} (op) (hp : Reach u roots p bank)
    (ha : Available u bank a) (hb : Available u bank b) :
    ∃ q next, Reach u roots q next ∧ Available u next (combine op a b) ∧
        (∀ v, Available u bank v → Available u next v) ∧
        q+cost a+cost b ≤ p+1+cost (combine op a b) := by
  classical
  by_cases c : Constant a ∨ Constant b
  · refine ⟨p,bank,hp,from_constant op c ha hb,fun _ h => h,?_⟩
    by_cases ca : Constant a <;> by_cases cb : Constant b
    · simp [cost,ca,cb,both_constant op ca cb]
    · simp [cost,ca,cb]
    · simp [cost,ca,cb]
    · exact False.elim (c.elim ca cb)
  · have ca : ¬Constant a := fun h => c (Or.inl h)
    have cb : ¬Constant b := fun h => c (Or.inr h)
    exact ⟨p+1,_,Reach.two op hp ha hb,Or.inl (by simp),fun _ h => available_cons _ h,
      by simp [cost,ca,cb]⟩

theorem comb_prime {R u} {bank : List (Wire R)} {d a b} (hd : allowed u d) (ha : Available u bank a) (hb : Available u bank b) :
    ∃ op x y, comb d a b=combine op x y ∧ Available u bank x ∧ Available u bank y ∧ cost x=cost a ∧ cost y=cost b := by
  rcases allowed_four hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
  · exact ⟨false,a,b,rfl,ha,hb,rfl,rfl⟩
  · exact ⟨true,a,b,rfl,ha,hb,rfl,rfl⟩
  · exact ⟨false,a,inv b,rfl,ha,avail_inv hu hb,rfl,cost_inv b⟩
  · exact ⟨false,inv a,b,rfl,avail_inv hu ha,hb,cost_inv a,rfl⟩

theorem extend_comb {R u} (roots : List (Wire R)) {p bank a b} (d) (hd : allowed u d) (hp : Reach u roots p bank)
    (ha : Available u bank a) (hb : Available u bank b) :
    ∃ q next, Reach u roots q next ∧ Available u next (comb d a b) ∧
        (∀ v, Available u bank v → Available u next v) ∧
        q+cost a+cost b ≤ p+1+cost (comb d a b) := by
  obtain ⟨op,x,y,e,hx,hy,cx,cy⟩ := comb_prime hd ha hb
  rw [e,←cx,←cy]
  exact extend_two roots op hp hx hy

theorem mem_kept {α : Type} {k : Bool} {x a : α} {xs} (h : x ∈ kept k a xs) :
    x=a ∨ x∈xs := by cases k <;> simp_all [kept]

theorem contraction {R u} {goal : Wire R} (nc : ¬Constant goal) {s ws}
    (h : Run u goal s ws) (roots : List (Wire R)) {p bank}
    (hp : Reach u roots p bank) (hs : supply u bank ws) :
    ∃ q next, Reach u roots q next ∧ Available u next goal ∧ q+mass ws ≤ p+s := by
  classical
  induction h using Run.ind generalizing p bank with
  | stop =>
    exact ⟨p,bank,hp,hs _ (by simp),by simp [mass,cost,nc]⟩
  | perm eq _ ih =>
    have hsub : supply u bank _ := fun v hv => hs v (eq.mem_iff.mp hv)
    obtain ⟨q,W,hW,hv,hl⟩ := ih hp hsub
    exact ⟨q,W,hW,hv,by simpa only [mass,←(eq.map cost).sum_eq] using hl⟩
  | @two s a b rest op hd ka kb _ ih =>
    obtain ⟨r,T,hT,hz,inc,le⟩ := extend_comb roots op hd hp (hs a (by simp)) (hs b (by simp))
    have ht : supply u T (comb op a b :: kept ka a (kept kb b rest)) := by
      intro v h
      rcases List.mem_cons.mp h with rfl | hh
      · exact hz
      · apply inc v
        apply hs
        rcases mem_kept hh with rfl | hh
        · simp
        · exact List.mem_cons_of_mem _ (List.mem_cons.mpr (mem_kept hh))
    obtain ⟨q,W,hW,hv,hl⟩ := ih hT ht
    have hlen := mass_kept a (kept kb b rest) ka
    have hlen' := mass_kept b rest kb
    rw [mass_cons] at hl
    refine ⟨q,W,hW,hv,?_⟩
    rw [mass_cons,mass_cons]
    omega

def restrictRows {R S : Type} (rows : S → R) (a : Wire R) : Wire S :=
  fun r => a (rows r)

theorem restrict_kept {R S : Type} (rows : S → R) (k : Bool) (a : Wire R) (ws) :
    (kept k a ws).map (restrictRows rows) =
    kept k (restrictRows rows a) (ws.map (restrictRows rows)) := by
  cases k <;> simp [kept]

theorem restrict_comb {R S : Type} (rows : S → R) (d) (a b : Wire R) :
    restrictRows rows (comb d a b) = comb d (restrictRows rows a) (restrictRows rows b) := by
  unfold comb
  split_ifs <;> rfl

theorem restrict_run {R S : Type} {u} (rows : S → R) {goal s ws} (h : Run u goal s ws) :
    Run u (restrictRows rows goal) s (ws.map (restrictRows rows)) := by
  induction h using Run.ind with
  | stop => exact Run.stop
  | perm p _ ih => exact Run.perm (p.map _) ih
  | two op hd ka kb _ ih =>
    simp only [List.map_cons,restrict_kept,restrict_comb] at ih ⊢
    exact Run.two op hd ka kb ih

theorem projected_bound {R S : Type} {u} (rows : S → R) {goal s ws} (h : Run u goal s ws)
    (nc : ¬Constant (restrictRows rows goal)) {roots : List (Wire S)} {p bank L}
    (hp : Reach u roots p bank) (hs : supply u bank (ws.map (restrictRows rows)))
    (hl : ∀ q bs, Reach u roots q bs → Available u bs (restrictRows rows goal) → L ≤ q) :
    L + mass (ws.map (restrictRows rows)) ≤ p+s := by
  obtain ⟨q,bs,hq,ht,hle⟩ := contraction nc (restrict_run rows h) roots hp hs
  have hqle := hl q bs hq ht
  omega

abbrev Row := Fin 512

def observe (a : Sig) : Wire Row := fun r => bit r a

def table (f : Wire Row) : Sig :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast (List.length_ofFn)

theorem bit_table (f : Wire Row) (r : Row) : bit r (table f) = f r := by
  simp only [bit,table,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]; simp [r.isLt]

theorem table_observe (v : Sig) : table (observe v) = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  exact bit_table (observe v) ⟨j,hj⟩

theorem observe_table (f : Wire Row) : observe (table f) = f := by
  funext r
  exact bit_table f r

theorem obs_neg (a : Sig) : observe (neg a) = inv (observe a) := by
  funext r
  exact bit_neg _ _

theorem obs_bin (d : Nat) (a b : Sig) :
    observe (bin d a b) = comb d (observe a) (observe b) := by
  funext r
  simp only [observe,bit_bin,comb]
  split_ifs <;> rfl

theorem map_kept {α β : Type} (f : α → β) (d : Bool) (a : α) (l : List α) :
    (kept d a l).map f = kept d (f a) (l.map f) := by cases d <;> rfl

theorem kept_nd {α : Type} (k : Bool) (a : α) (l : List α)
    (hn : l.Nodup) (ha : a ∉ l) : (kept k a l).Nodup := by cases k <;> simp [kept,hn,ha]

theorem kept_fin (k : Bool) (a : Sig) (l : List Sig) :
    (kept k a l).toFinset = if k then insert a l.toFinset else l.toFinset := by
  cases k <;> simp [kept]

theorem list_run {u} {T : Sig} {k S} (h : Live u T k S) (v : List Sig)
    (hv : v.Nodup) (eqv : v.toFinset = S) : Run u (observe T) k (v.map observe) := by
  classical
  induction h using Live.ind generalizing v with
  | stop hp =>
    have eq : [T].Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp) hv
      simpa [eqv]
    exact Run.perm (eq.map _) Run.stop
  | @binary k U a b d hd ha hb hab fresh _ ih =>
    let rest := ((U.erase a).erase b).toList
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let mid := kept kb b rest
    let tail := kept ka a mid
    have er : rest.toFinset = (U.erase a).erase b := by simp [rest]
    have ar : a ∉ rest := by simp [rest]
    have br : b ∉ rest := by simp [rest]
    have hr : rest.Nodup := Finset.nodup_toList _
    have bm := kept_nd kb b rest hr br
    have am : a ∉ mid := by cases h : kb <;> simp [mid,kept,h,hab,ar]
    have nd := kept_nd ka a mid bm am
    have ht : tail.toFinset = U := by
      change (kept ka a (kept kb b rest)).toFinset = U
      rw [kept_fin,kept_fin,er]
      ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases aj : j=a <;>
        by_cases bj : j=b <;> simp_all [ka,kb]
    have hf : bin d a b ∉ tail := by
      intro hz
      exact fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ht ▸ List.mem_toFinset.mpr hz)))
    have progress := ih (bin d a b::tail) (List.nodup_cons.mpr ⟨hf,nd⟩) (by simp [ht])
    change Run _ _ _ ((bin d a b::kept ka a (kept kb b rest)).map observe) at progress
    rw [List.map_cons,map_kept,map_kept,obs_bin] at progress
    have perm : (a::b::rest).Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp [hab,ar,br,hr]) hv
      ext j
      by_cases ja : j=a <;> by_cases jb : j=b <;> simp_all [er]
    exact Run.perm (perm.map _) (Run.two d hd ka kb progress)

theorem table_inv (f : Wire Row) : table (inv f) = neg (table f) := by
  rw [←table_observe (neg (table f)),obs_neg,observe_table]

theorem table_prime (d : Bool) (f g : Wire Row) :
    table (combine d f g) = prime d (table f) (table g) := by
  apply bit_ext
  intro r
  rw [bit_table,bit_prime,bit_table,bit_table]
  cases d <;> rfl

theorem available_rep {u} {bank : List (Wire Row)} {a} (h : Available u bank a) :
    Repr u ((bank.map table).map (nrm u)) (table a) := by
  rcases h with hm | ⟨b,rfl⟩ | ⟨rfl,hm⟩
  · exact Or.inl (List.mem_map_of_mem (List.mem_map_of_mem hm))
  · apply repr_const
    cases b
    · exact Or.inl (bit_ext fun i => (bit_table _ i).trans (bit_zero i).symm)
    · exact Or.inr (bit_ext fun i => (bit_table _ i).trans (bit_one i).symm)
  · have := table_inv a
    refine Or.inl ?_
    rw [←nrm_neg,←this]
    exact List.mem_map_of_mem (List.mem_map_of_mem hm)

theorem reach_live_sub {u} {roots : List (Wire Row)} {p bank}
    (h : Reach u roots p bank) {T k S} (run : Live u T k S)
    (sub : ∀ a ∈ S, a ∈ (bank.map table).map (nrm u)) :
    ∃ l V, l ≤ p+k ∧ Live u T l V ∧ ∀ a ∈ V, a ∈ (roots.map table).map (nrm u) := by
  induction h using Reach.ind generalizing k S with
  | start => exact ⟨k,S,by omega,run,sub⟩
  | @two p bank a b d h ha hb ih =>
    rw [List.map_cons,List.map_cons,table_prime] at sub
    have rep := prime_rep d (available_rep ha) (available_rep hb)
    obtain ⟨k',S',hk,run',sub'⟩ := pull_gate (c:=1) run (rep.imp id (fun h => ⟨rfl,h⟩))
      (fun a hm => by simpa [or_comm] using sub a hm)
    obtain ⟨l,V,hl,hr,hs⟩ := ih run' sub'
    exact ⟨l,V,by omega,hr,hs⟩

def plainWord (a : Sig) : Bool := !(bit 0 a)

theorem nrm_map {u} {w : List Sig} (h : w.all plainWord=true) : w.map (nrm u)=w := by
  have e : w.map (nrm u) = w.map id := by
    apply List.map_congr_left
    intro a ha
    exact nrm_id (by simpa [plainWord] using List.all_eq_true.mp h a ha)
  rw [e,List.map_id]

theorem reach_live {u} {roots : List Sig} {p bank T} (hp : proper T) (nT : plainWord T=true) (nR : roots.all plainWord=true)
    (h : Reach u (roots.map observe) p bank) (hit : Available u bank (observe T)) :
    ∃ k S, k ≤ p ∧ Live u T k S ∧ ∀ a ∈ S, a ∈ roots := by
  have hm := available_rep hit
  rw [table_observe] at hm
  unfold Repr at hm
  rw [nrm_id (by simpa [plainWord] using nT)] at hm
  have mem := hm.resolve_right (fun hn => hn hp)
  obtain ⟨l,V,hl,hr,hs⟩ := reach_live_sub h (Live.stop hp) (by simpa using mem)
  refine ⟨l,V,by omega,hr,?_⟩
  have e : (roots.map observe).map table = roots := by simp [List.map_map,Function.comp_def,table_observe]
  rw [e,nrm_map nR] at hs
  exact hs

theorem live_row_difference {u T k S} (h : Live u T k S) {r s : Row}
    (diff : bit r T ≠ bit s T) : ∃ a ∈ S, bit r a ≠ bit s a := by
  induction h using Live.ind with
  | stop hp => exact ⟨_,by simp,diff⟩
  | @binary k U a b d hd ha hb hab hf _ ih =>
    obtain ⟨v,hv,hd⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · by_cases aeq : bit r a = bit s a
      · refine ⟨b,by simp,?_⟩
        intro beq
        exact hd (by rw [bit_bin,bit_bin,aeq,beq])
      · exact ⟨a,by simp,aeq⟩
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hd⟩

theorem raw_required {u T k S} (h : Live u T k S) (roots : List Sig) (a : Sig)
    (sub : ∀ v ∈ S, v ∈ roots) (r s : Row) (diff : bit r T ≠ bit s T)
    (isolated : ∀ v ∈ roots, v ≠ a → bit r v = bit s v) : a ∈ S := by
  obtain ⟨v,hv,hd⟩ := live_row_difference h diff
  by_cases veq : v=a
  · simpa [veq] using hv
  · exact False.elim (hd (isolated v (sub v hv) veq))

def inputs : List Sig := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000]

def graph : Sig := 0xfffffffffffffffffffffffffffafff8ffffffffffffffffffffffffffeaffc8fffffffffffefcfcfffffffffffaf8f8ffeefeeeffeefcccffeafaeaffeaf8c8

def seed : Sig := inputs.getD 0 zero ||| inputs.getD 3 zero

def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)

def edge (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
  (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) ||
  (x 6 && x 8) || (x 8 && x 5)

theorem edge_table : ∀ r : Row, bit r graph = edge (sample r) := by decide +kernel

theorem graph_proper : proper graph := by unfold proper; decide +kernel

theorem input_list : List.ofFn (fun j : Fin 9 => inputs.getD j.val zero) = inputs := rfl

theorem sampled (r : Row) : List.ofFn (sample r) = inputs.map (bit r) := by
  rw [←input_list]
  rw [List.map_ofFn]
  rfl

theorem table_eval (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (i : Nat) (r : Row) : bit r ((execute C.gates inputs).getD i zero) =
      (C.wires (List.ofFn (sample r))).getD i false := by
  rw [←b_read,execute_bits _ _ _ (fun g hg => (h g hg).1),sampled]
  rfl

def rename (f : Row → Row) (a : Sig) := table fun r => bit (f r) a

theorem bit_rename (f : Row → Row) (a : Sig) (r : Row) :
    bit r (rename f a) = bit (f r) a := bit_table _ _

theorem observe_rename (f : Row → Row) (a : Sig) :
    observe (rename f a) = restrictRows f (observe a) := by funext r; exact bit_rename f a r

theorem rename_bin (f : Row → Row) (d : Nat) (a b : Sig) :
    rename f (bin d a b) = bin d (rename f a) (rename f b) := by
  apply bit_ext
  intro r
  simp only [bit_rename,bit_bin]

theorem rename_inj (f : Row → Row) (onto : Function.Surjective f) :
    Function.Injective (rename f) := by
  intro a b h
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  obtain ⟨r,hr⟩ := onto ⟨j,hj⟩
  have he := congrArg (bit r) h
  change bit ⟨j,hj⟩ a = bit ⟨j,hj⟩ b
  rw [bit_rename,bit_rename,hr] at he
  exact he

theorem rename_constants (f : Row → Row) : rename f zero = zero ∧ rename f one = one := by
  constructor <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj
  · exact (bit_rename f zero ⟨j,hj⟩).trans ((bit_zero _).trans (bit_zero ⟨j,hj⟩).symm)
  · exact (bit_rename f one ⟨j,hj⟩).trans ((bit_one _).trans (bit_one ⟨j,hj⟩).symm)

theorem live_rename {u T k S} (h : Live u T k S) (f : Row → Row) (onto : Function.Surjective f) :
    Live u (rename f T) k (S.image (rename f)) := by
  have inj := rename_inj f onto
  obtain ⟨fz,fo⟩ := rename_constants f
  have pp (v) (p : proper v) : proper (rename f v) :=
    ⟨fun e => p.1 (inj (e.trans fz.symm)),fun e => p.2 (inj (e.trans fo.symm))⟩
  induction h using Live.ind with
  | stop hp => simpa using Live.stop (pp _ hp)
  | @binary k U a b d hd ha hb hab hf _ ih =>
    have fresh : rename f (bin d a b) ∉ (insert a (insert b U)).image (rename f) := by
      intro hm
      obtain ⟨v,hv,eq⟩ := Finset.mem_image.mp hm
      exact hf (inj eq ▸ hv)
    simp only [Finset.image_insert,rename_bin] at fresh ih ⊢
    exact Live.binary hd (pp _ ha) (pp _ hb) (fun hh => hab (inj hh)) fresh ih

theorem mono_row_difference {u T k S} (h : Live u T k S) (none : u=false) {r s : Row}
    (pos : bit r T = true) (negRow : bit s T = false) :
    ∃ a ∈ S, bit r a = true ∧ bit s a = false := by
  induction h using Live.ind with
  | stop hp => exact ⟨_,by simp,pos,negRow⟩
  | @binary k U a b d hd ha hb hab hf _ ih =>
    obtain ⟨v,hv,hp,hn⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · rw [bit_bin] at hp hn
      subst none
      rcases allowed_four hd with rfl | rfl | ⟨h,_⟩ | ⟨h,_⟩
      · cases p : bit r a <;> cases q : bit s a <;> cases u : bit r b <;> cases z : bit s b <;> simp_all
      · cases p : bit r a <;> cases q : bit s a <;> cases u : bit r b <;> cases z : bit s b <;> simp_all
      · exact Bool.noConfusion h
      · exact Bool.noConfusion h
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hp,hn⟩

def Lower (u : Bool) (roots : List Sig) (T : Sig) (L : Nat) : Prop :=
  ∀ p bank, Reach u (roots.map observe) p bank → Available u bank (observe T) → L ≤ p

def Impossible (u : Bool) (T : Sig) (cap : Nat) (S : Finset Sig) : Prop :=
  ∀ k, k ≤ cap → ¬Live u T k S

def Essential (T : Sig) (roots : List Sig) (a : Sig) : Prop :=
  ∃ r s : Row, bit r T ≠ bit s T ∧ ∀ v ∈ roots, v ≠ a → bit r v = bit s v

theorem lower_impossible {u roots T L} (hp : proper T) (nT : plainWord T=true) (nR : roots.all plainWord=true)
    (essential : ∀ a ∈ roots, Essential T roots a)
    (noRun : Impossible u T L roots.toFinset) : Lower u roots T (L+1) := by
  intro p bank h ha
  obtain ⟨k,S,hk,run,hs⟩ := reach_live hp nT nR h ha
  have he : roots.toFinset = S := by
    ext a
    rw [List.mem_toFinset]
    refine ⟨fun hm => ?_,hs a⟩
    obtain ⟨r,s,hd,iso⟩ := essential _ hm
    exact raw_required run roots a hs r s hd iso
  by_contra! small
  exact noRun k (by omega) (he.symm ▸ run)

theorem observe_proper {v : Sig} (hv : proper v) : ¬Constant (observe v) := by
  rintro ⟨b,h⟩
  have hr : Repr false [] v := by
    apply repr_const
    cases b
    · exact Or.inl (bit_ext fun i => (congrFun h i).trans (bit_zero i).symm)
    · exact Or.inr (bit_ext fun i => (congrFun h i).trans (bit_one i).symm)
  have hr' : represented [] v := hr
  exact (hr'.resolve_left (by simp)) hv

theorem mass_append {R} (a b : List (Wire R)) : mass (a++b) = mass a + mass b := by
  simp [mass]

theorem mass_constants {R} (xs : List (Wire R)) (hc : ∀ x ∈ xs, Constant x) :
    mass xs = xs.length := by
  induction xs with
  | nil => simp [mass]
  | cons a xs ih =>
    have ha := hc a (by simp)
    simp only [mass_cons,List.length_cons,cost,if_pos ha,ih (fun x hx => hc x (by simp [hx]))]
    omega

theorem lower_slice {u} {roots other : List Sig} {T G : Sig} (pT : proper T) (nT : plainWord T=true) (nR : roots.all plainWord=true) (pG : proper G)
    (r : Row → Row) (eq : rename r T = G)
    (covered : ∀ a ∈ roots, Available u (other.map observe) (observe (rename r a)))
    (singles : Finset Sig) (necessary : ∀ a ∈ singles, Essential T roots a)
    (constant : ∀ a ∈ singles, Constant (observe (rename r a)))
    (L : Nat) (prior : Lower u other G L) : Lower u roots T (L + singles.card) := by
  classical
  intro p bank hh ha
  obtain ⟨k,S,hk,run,sub⟩ := reach_live pT nT nR hh ha
  have subS : singles ⊆ S := by
    intro a hs
    obtain ⟨i,j,hd,hiso⟩ := necessary a hs
    exact raw_required run roots a sub i j hd hiso
  let front := singles.toList ++ (S \ singles).toList
  have nd : front.Nodup := by
    simp only [front,List.nodup_append]
    refine ⟨Finset.nodup_toList _,Finset.nodup_toList _,?_⟩
    intro a ha b hb he
    subst b
    exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hb)).2 (Finset.mem_toList.mp ha)
  have fe : front.toFinset=S := by ext a; simp [front,Finset.union_sdiff_of_subset subS]
  have run' := list_run run front nd fe
  have gc : restrictRows r (observe T) = observe G := (observe_rename _ _).symm.trans (congrArg observe eq)
  have supp : supply u (other.map observe) ((front.map observe).map (restrictRows r)) := by
    intro v hv
    obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
    obtain ⟨a,hmem,rfl⟩ := List.mem_map.mp hm
    rw [←observe_rename]
    exact covered a (sub _ (fe ▸ List.mem_toFinset.mpr hmem))
  have bound := projected_bound r run' (gc ▸ observe_proper pG) Reach.start supp
    (L:=L) (gc ▸ prior)
  have massLo : singles.card ≤ mass ((front.map observe).map (restrictRows r)) := by
    simp only [front,List.map_append,mass_append]
    let xs := (singles.toList.map observe).map (restrictRows r)
    have only : ∀ v ∈ xs, Constant v := by
      intro v hv
      obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
      obtain ⟨a,hmem,rfl⟩ := List.mem_map.mp hm
      rw [←observe_rename]
      exact constant _ (Finset.mem_toList.mp hmem)
    have sz := mass_constants xs only
    simp only [xs,List.length_map,Finset.length_toList] at sz
    change singles.card ≤ mass xs + _
    rw [sz]
    omega
  omega

def childTwo (ws : List Sig) (a b : Sig) (d : Nat) (ka kb : Bool) : List Sig :=
  bin d a b :: kept ka a (kept kb b ((ws.erase a).erase b))

theorem erase_fin {l : List Sig} (h : l.Nodup) (a : Sig) : (l.erase a).toFinset = l.toFinset.erase a := by
  ext x
  simp [h.mem_erase_iff]

theorem enum_step {u} {T : Sig} {cap : Nat} {ws : List Sig} (hn : ws.Nodup) (out : T ∉ ws)
    (twoStep : ∀ a ∈ ws, ∀ b ∈ ws, ∀ d, allowed u d → ∀ ka kb, a ≠ b → bin d a b ∉ ws →
      proper (bin d a b) → (childTwo ws a b d ka kb).length ≤ cap →
      Impossible u T (cap-1) (childTwo ws a b d ka kb).toFinset) :
    Impossible u T cap ws.toFinset := by
  classical
  intro k hk h
  generalize he : ws.toFinset = S at h
  induction h using Live.ind with
  | stop hp =>
    have mem : T ∈ ws.toFinset := he.symm ▸ Finset.mem_singleton_self _
    exact out (List.mem_toFinset.mp mem)
  | @binary k U a b d hd ha hb hab hf tail _ =>
    have am : a ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    have bm : b ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    have fresh : bin d a b ∉ ws := fun h => hf (he ▸ List.mem_toFinset.mpr h)
    have hz := live_proper tail _ (Finset.mem_insert_self _ _)
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let rest := (ws.erase a).erase b
    have er : rest.toFinset = (ws.toFinset.erase a).erase b := by
      rw [show rest=(ws.erase a).erase b by rfl,erase_fin (hn.erase _) b,
        erase_fin hn a]
    have ke : (kept ka a (kept kb b rest)).toFinset = U := by
      rw [kept_fin,kept_fin,er,he]
      ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases ja : j=a <;>
        by_cases jb : j=b <;> simp_all [ka,kb]
    have rn : rest.Nodup := (hn.erase _).erase _
    have ar : a ∉ rest := fun h => (hn.not_mem_erase) (List.mem_of_mem_erase h)
    have br : b ∉ rest := (hn.erase a).not_mem_erase
    have nk := kept_nd kb b rest rn br
    have ax : a ∉ kept kb b rest := by cases kb <;> simp [kept,ar,hab]
    have nd : (childTwo ws a b d ka kb).Nodup := by
      refine List.nodup_cons.mpr ⟨?_,kept_nd ka a _ nk ax⟩
      intro h
      exact hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ke ▸ List.mem_toFinset.mpr h)))
    have eq : (childTwo ws a b d ka kb).toFinset = insert (bin d a b) U := by
      change (bin d a b::kept ka a (kept kb b rest)).toFinset = _
      simp [ke]
    have sc := live_size tail
    have len : (childTwo ws a b d ka kb).length ≤ cap := by
      rw [←List.toFinset_card_of_nodup nd,eq]
      omega
    exact twoStep a am b bm d hd ka kb hab fresh hz len k (by omega) (eq.symm ▸ tail)

def Sep (T : Sig) (width : Nat) (pos negRow : Fin width → Row)
    (asig : Sig → BitVec width × BitVec width) : Prop :=
  (∀ i, bit (pos i) T = true ∧ bit (negRow i) T = false) ∧
  ∀ w i, (asig w).1.getLsbD i.val = bit (pos i) w ∧
    (asig w).2.getLsbD i.val = bit (negRow i) w

def column {n} (oriented : Bool) (s : BitVec n × BitVec n) : BitVec n :=
  if oriented then s.1 &&& ~~~s.2 else s.1 ^^^ s.2

def covered {n} (oriented : Bool) (sig : Sig → BitVec n × BitVec n) : List Sig → BitVec n
  | [] => 0
  | a::ws => column oriented (sig a) ||| covered oriented sig ws

theorem covered_bit {n : Nat} {oriented : Bool} {sig : Sig → BitVec n × BitVec n} {ws : List Sig} {i : Fin n} :
    (covered oriented sig ws).getLsbD i.val = true ↔
    ∃ a ∈ ws, (column oriented (sig a)).getLsbD i.val = true := by
  induction ws with
  | nil => simp [covered]
  | cons a ws ih =>
    simp only [covered,BitVec.getLsbD_or,Bool.or_eq_true,ih,List.mem_cons,exists_eq_or_imp]

theorem cover_sound {u T k S} (h : Live u T k S) {ws : List Sig} (he : ws.toFinset=S)
    {width : Nat} {r s : Fin width → Row} {sig} (correct : Sep T width r s sig)
    (oriented : Bool) (zeroNot : oriented=true → u=false) :
    covered oriented sig ws = BitVec.allOnes width := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  let i : Fin width := ⟨j,hj⟩
  have yes := (correct.1 i).1
  have no := (correct.1 i).2
  rw [BitVec.getLsbD_allOnes]; simp only [hj,decide_true]
  apply (covered_bit (i:=i)).mpr
  cases oriented with
  | false =>
    obtain ⟨a,ha,hd⟩ := live_row_difference h (show bit (r i) T ≠ bit (s i) T by simp [yes,no])
    refine ⟨a,List.mem_toFinset.mp (he.symm ▸ ha),?_⟩
    simp only [column,Bool.false_eq_true,ite_false,BitVec.getLsbD_xor,(correct.2 a i).1,(correct.2 a i).2]
    cases hx : bit (r i) a <;> cases hy : bit (s i) a <;> simp_all
  | true =>
    obtain ⟨a,ha,hp,hn⟩ := mono_row_difference h (zeroNot rfl) yes no
    refine ⟨a,List.mem_toFinset.mp (he.symm ▸ ha),?_⟩
    simp only [column,ite_true,BitVec.getLsbD_and,BitVec.getLsbD_not,i.isLt,decide_true,
      Bool.true_and,(correct.2 a i).1,(correct.2 a i).2,hp,hn,Bool.not_false,Bool.and_self]

theorem cover_required {u T ws k} (h : Live u T k (List.toFinset ws)) {n : Nat} {r s : Fin n → Row} {sig}
    (correct : Sep T n r s sig) :
    covered (!u) sig ws = BitVec.allOnes n := by
  apply cover_sound h rfl correct
  simp

def Slice (u : Bool) (raw : List Sig) (T d : Sig) (L : Nat) : Prop :=
  ∃ (f : Row → Row) (roots : List Sig), (∀ r, bit (f r) d = true) ∧
    (∀ a ∈ raw, Available u (roots.map observe) (restrictRows f (observe a))) ∧
    ¬Constant (restrictRows f (observe T)) ∧
    ∀ p bank, Reach u (roots.map observe) p bank → Available u bank (restrictRows f (observe T)) → L ≤ p

def masked (d a : Sig) := a &&& d

def availableB (u : Bool) (d : Sig) (pool : List Sig) (a : Sig) :=
  let m := masked d a
  m == zero || m == d || (pool.map (masked d)).any (fun v => v==m) ||
    (u && (let c := masked d (neg a); (pool.map (masked d)).any (fun v => v==c)))

theorem masked_eq {f : Row → Row} {d a b : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = masked d b) :
    restrictRows f (observe a) = restrictRows f (observe b) := by
  funext r
  have h := congrArg (bit (f r)) eq
  change bit (f r) a = bit (f r) b
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using h

theorem masked_zero {f : Row → Row} {d a : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = zero) : restrictRows f (observe a) = fun _ => false := by
  funext r
  have he := congrArg (bit (f r)) eq
  change bit (f r) a = false
  rw [bit_zero] at he
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using he

theorem masked_one {f : Row → Row} {d a : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = d) : restrictRows f (observe a) = fun _ => true := by
  funext r
  have he := congrArg (bit (f r)) eq
  change bit (f r) a = true
  rw [dom r] at he
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using he

def poolSupply (u : Bool) (f : Row → Row) (bank : List (Wire Row)) (pool : List Sig) :=
  ∀ a ∈ pool, Available u bank (restrictRows f (observe a))

theorem availableB_sound {u} {f : Row → Row} {d a : Sig} {bank pool}
    (dom : ∀ r, bit (f r) d = true) (supplyB : poolSupply u f bank pool)
    (check : availableB u d pool a = true) : Available u bank (restrictRows f (observe a)) := by
  simp only [availableB,List.any_map,Function.comp_def,Bool.or_eq_true,Bool.and_eq_true,beq_iff_eq,List.any_eq_true] at check
  rcases check with ((hz | ho) | ⟨v,hv,he⟩) | ⟨hu,v,hv,he⟩
  · exact Or.inr (Or.inl ⟨false,masked_zero dom hz⟩)
  · exact Or.inr (Or.inl ⟨true,masked_one dom ho⟩)
  · exact masked_eq dom he ▸ supplyB v hv
  · have h := avail_inv hu (masked_eq dom he ▸ supplyB v hv)
    rw [obs_neg] at h
    have e : inv (restrictRows f (inv (observe a))) = restrictRows f (observe a) := by
      funext r
      simp [inv,restrictRows]
    rwa [e] at h

abbrev Choice := Nat × Sig × Sig

def choiceVal (c : Choice) := bin c.1 c.2.1 c.2.2

def allowedB (u : Bool) (d : Nat) := decide (d<2) || (u && decide (d<4))

theorem allowedB_ok {u d} (h : allowedB u d=true) : allowed u d := by
  simpa [allowedB,allowed] using h

def choiceOK (u : Bool) (d : Sig) (pool : List Sig) (c : Choice) :=
  allowedB u c.1 && (availableB u d pool c.2.1 && availableB u d pool c.2.2)

theorem pay_choice {u} {f : Row → Row} {d : Sig} {roots bank pool q}
    (dom : ∀ r, bit (f r) d = true) (hp : Reach u roots q bank) (hs : poolSupply u f bank pool)
    (c : Choice) (valid : choiceOK u d pool c = true) :
    ∃ next, Reach u roots (q+1) next ∧ poolSupply u f next (choiceVal c :: pool) := by
  simp only [choiceOK,Bool.and_eq_true] at valid
  obtain ⟨op,x,y,e,hx,hy,_,_⟩ := comb_prime (allowedB_ok valid.1) (availableB_sound dom hs valid.2.1)
    (availableB_sound dom hs valid.2.2)
  refine ⟨_,Reach.two op hp hx hy,?_⟩
  intro a hm
  rcases List.mem_cons.mp hm with rfl | hm
  · rw [choiceVal,obs_bin,restrict_comb,e]
    exact Or.inl (by simp)
  · exact available_cons _ (hs _ hm)

def makePool (u : Bool) (d : Sig) (pool : List Sig) : List Choice → Option (List Sig)
  | [] => some pool
  | c::cs => if choiceOK u d pool c then makePool u d (choiceVal c::pool) cs else none

theorem makePool_sound {u} {d : Sig} {f : Row → Row} (dom : ∀ r, bit (f r) d = true)
    {roots bank q pool} (hp : Reach u roots q bank) (hs : poolSupply u f bank pool)
    (cs : List Choice) {result} (ok : makePool u d pool cs = some result) :
    ∃ next, Reach u roots (q+cs.length) next ∧ poolSupply u f next result := by
  induction cs generalizing bank q pool with
  | nil => cases ok; exact ⟨_,hp,hs⟩
  | cons c cs ih =>
    simp only [makePool] at ok
    split at ok
    next h =>
      obtain ⟨next,hr,sh⟩ := pay_choice dom hp hs c h
      obtain ⟨out,hr',sh'⟩ := ih hr sh ok
      exact ⟨out,by simpa [Nat.add_assoc,Nat.add_comm 1] using hr',sh'⟩
    next => contradiction

def isMaskedConstant (d a : Sig) := masked d a == zero || masked d a == d

theorem count_constants {d : Sig} {f : Row → Row} (dom : ∀ r, bit (f r) d = true)
    (ws : List Sig) : ws.countP (isMaskedConstant d) ≤ mass ((ws.map observe).map (restrictRows f)) := by
  classical
  induction ws with
  | nil => simp [mass]
  | cons a ws ih =>
    simp only [List.countP_cons,List.map_cons,mass_cons]
    cases h : isMaskedConstant d a
    · simpa using (Nat.le_add_left _ _ |> ih.trans)
    · have hc : Constant (restrictRows f (observe a)) := by
        have hh : masked d a = zero ∨ masked d a = d := by simpa only [isMaskedConstant,Bool.or_eq_true,beq_iff_eq] using h
        rcases hh with hz | ho
        · exact ⟨false,masked_zero dom hz⟩
        · exact ⟨true,masked_one dom ho⟩
      simpa [cost,hc,Nat.add_comm] using Nat.succ_le_succ ih

def poolCut (u : Bool) (d : Sig) (L k p : Nat) (pool ws : List Sig) :=
  decide (k+p < L+ws.countP (isMaskedConstant d)) && ws.all (availableB u d pool)

theorem poolCut_sound {u raw T d L} (slice : Slice u raw T d L) (cs : List Choice)
    {pool ws cap} (built : makePool u d raw cs = some pool)
    (nd : ws.Nodup) (cut : poolCut u d L cap cs.length pool ws = true) :
    Impossible u T cap ws.toFinset := by
  intro k hk h
  obtain ⟨f,roots,dom,base,nc,lo⟩ := slice
  obtain ⟨bank,hr,hs⟩ := makePool_sound dom (Reach.start (roots:=roots.map observe)) base cs built
  simp only [poolCut,Bool.and_eq_true,decide_eq_true_eq] at cut
  obtain ⟨ineq,all⟩ := cut
  have coveredS : supply u bank ((ws.map observe).map (restrictRows f)) := by
    intro v hv
    obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hm
    exact availableB_sound dom hs (List.all_eq_true.mp all a ha)
  have b := projected_bound f (list_run h ws nd rfl) nc hr coveredS lo
  have massLo := count_constants dom ws
  have hu := ineq
  simp only [Nat.zero_add] at b
  omega

abbrev Move := Sig × Sig × Row

def shifted (d r : Row) : Row :=
  if h : r.val < 512-d.val then ⟨d.val+r.val,by omega⟩ else ⟨r.val-(512-d.val),by omega⟩

def backwards (d : Row) : Row := Fin.ofNat 512 (512-d.val)

def rowMove (m : Move) (r : Row) : Row :=
  if bit r m.1 then shifted m.2.2 r else if bit r m.2.1 then shifted (backwards m.2.2) r else r

def mux (m a b : Sig) := (m &&& a) ||| (~~~m &&& b)

def wordMove (m : Move) (a : Sig) :=
  mux m.1 (a.rotateRight m.2.2.val) (mux m.2.1 (a.rotateRight (backwards m.2.2).val) a)

theorem bit_shift (d r : Row) (a : Sig) : bit r (a.rotateRight d.val) = bit (shifted d r) a := by
  unfold bit
  rw [BitVec.getLsbD_rotateRight_of_lt d.isLt]
  by_cases h : r.val < 512-d.val <;> simp [shifted,h,r.isLt]

theorem bool_mux (p x y : Bool) : (p && x || !p && y) = (if p then x else y) := by cases p <;> simp

theorem bit_mux (r : Row) (m a b : Sig) :
    bit r (mux m a b) = if bit r m then bit r a else bit r b := by
  simp only [bit,mux,BitVec.getLsbD_and,BitVec.getLsbD_or,BitVec.getLsbD_not,r.isLt,
    decide_true,Bool.true_and]
  exact bool_mux _ _ _

theorem bit_move (r : Row) (m : Move) (a : Sig) : bit r (wordMove m a) = bit (rowMove m r) a := by
  simp only [wordMove,bit_mux,bit_shift,rowMove]
  cases bit r m.1 <;> cases bit r m.2.1 <;> rfl

def movedRow (ms : List Move) (r : Row) := ms.foldl (fun j m => rowMove m j) r

def movedWord (ms : List Move) (a : Sig) := ms.foldr wordMove a

theorem bit_moved (ms : List Move) (a : Sig) (r : Row) :
    bit r (movedWord ms a) = bit (movedRow ms r) a := by
  induction ms generalizing r with
  | nil => rfl
  | cons m ms ih => exact (bit_move r m _).trans (ih _)

theorem moved_eq_rename (ms : List Move) (a : Sig) : movedWord ms a = rename (movedRow ms) a := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  exact (bit_moved ms a ⟨j,hj⟩).trans (bit_rename _ _ ⟨j,hj⟩).symm

def freeWord (roots : List Sig) (w : Sig) := w==zero || w==one || roots.contains w

theorem freeWord_ok {u roots w} (ok : freeWord roots w = true) :
    Available u (roots.map observe) (observe w) := by
  simp only [freeWord,Bool.or_eq_true,beq_iff_eq,List.contains_eq_mem,decide_eq_true_eq] at ok
  rcases ok with (rfl | rfl) | hm
  · exact Or.inr (Or.inl ⟨false,funext bit_zero⟩)
  · exact Or.inr (Or.inl ⟨true,funext bit_one⟩)
  · exact Or.inl (List.mem_map_of_mem hm)

def checkMap (ms : List Move) (raw : List Sig) (T : Sig) (base : List Sig) (G : Sig) :=
  movedWord ms T == G && raw.all (fun a => freeWord base (movedWord ms a))

theorem map_correct {u ms raw T base G} (ok : checkMap ms raw T base G = true) :
    rename (movedRow ms) T = G ∧
    ∀ a ∈ raw, Available u (base.map observe) (observe (rename (movedRow ms) a)) := by
  simp only [checkMap,Bool.and_eq_true,beq_iff_eq,List.all_eq_true,moved_eq_rename] at ok
  exact ⟨ok.1,fun a ha => freeWord_ok (ok.2 a ha)⟩

theorem lower_map {u ms raw T base G L} (ok : checkMap ms raw T base G = true)
    (pT : proper T) (nT : plainWord T=true) (nR : raw.all plainWord=true) (pG : proper G)
    (hL : Lower u base G L) : Lower u raw T L := by
  obtain ⟨eq,supp⟩ := map_correct ok
  simpa using lower_slice pT nT nR pG (movedRow ms) eq supp ∅ (by simp) (by simp) L hL

theorem slice_correct {u ms raw T base G L d} (ok : checkMap ms raw T base G = true)
    (all : movedWord ms d = one) (properG : proper G) (hL : Lower u base G L) :
    Slice u raw T d L := by
  obtain ⟨eq,supp⟩ := map_correct ok
  have obs : restrictRows (movedRow ms) (observe T) = observe G :=
    (observe_rename _ _).symm.trans (congrArg observe eq)
  refine ⟨movedRow ms,base,?_,?_,?_,?_⟩
  · intro r
    rw [←bit_moved,all,bit_one]
  · intro a ha
    rw [←observe_rename]
    exact supp a ha
  · rw [obs]
    exact observe_proper properG
  · rw [obs]
    exact hL

def witnessB (T : Sig) (roots : List Sig) (a : Sig) (rs : Row × Row) :=
  (bit rs.1 T != bit rs.2 T) &&
  roots.all (fun w => w == a || bit rs.1 w == bit rs.2 w)

theorem witnessB_sound {T roots a rs} (ok : witnessB T roots a rs = true) : Essential T roots a := by
  simp only [witnessB,Bool.and_eq_true,bne_iff_ne,List.all_eq_true,Bool.or_eq_true,beq_iff_eq] at ok
  exact ⟨rs.1,rs.2,ok.1,fun w hw hne => (ok.2 w hw).resolve_left hne⟩

def checkEssential (T : Sig) (raw : List Sig) (xs : List (Sig × Row × Row)) :=
  plainWord T && raw.all plainWord && xs.all (fun a => witnessB T raw a.1 a.2)

theorem essential_ok {T raw xs} (ok : checkEssential T raw xs = true) :
    ∀ a ∈ (xs.map Prod.fst).toFinset, Essential T raw a := by
  simp only [checkEssential,Bool.and_eq_true] at ok
  intro a ha
  obtain ⟨⟨a,r,s⟩,hm,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
  exact witnessB_sound (List.all_eq_true.mp ok.2 _ hm)

theorem essential_plain {T raw xs} (ok : checkEssential T raw xs = true) :
    plainWord T=true ∧ raw.all plainWord=true := by
  simp only [checkEssential,Bool.and_eq_true] at ok
  exact ok.1

theorem lower_count {u raw T} (properT : proper T) (xs : List (Sig × Row × Row))
    (ok : checkEssential T raw xs = true) :
    Lower u raw T ((xs.map Prod.fst).toFinset.card-1) := by
  intro p bank hr hit
  obtain ⟨k,S,hk,run,sub⟩ := reach_live properT (essential_plain ok).1 (essential_plain ok).2 hr hit
  have le : (xs.map Prod.fst).toFinset.card ≤ S.card := by
    apply Finset.card_le_card
    intro a ha
    obtain ⟨r,s,hd,iso⟩ := essential_ok ok a ha
    exact raw_required run raw a sub r s hd iso
  have bound := live_size run
  omega

def checkLift (ms : List Move) (T : Sig) (raw : List Sig) (base : List Sig) (G : Sig)
    (xs : List (Sig × Row × Row)) :=
  checkMap ms raw T base G && checkEssential T raw xs &&
    xs.all (fun a => movedWord ms a.1 == zero || movedWord ms a.1 == one)

theorem lift_ok {u ms T raw base G xs L} (ok : checkLift ms T raw base G xs = true)
    (properT : proper T) (properG : proper G) (low : Lower u base G L) :
    Lower u raw T (L+(xs.map Prod.fst).toFinset.card) := by
  simp only [checkLift,Bool.and_eq_true] at ok
  obtain ⟨eq,supp⟩ := map_correct ok.1.1
  apply lower_slice properT (essential_plain ok.1.2).1 (essential_plain ok.1.2).2 properG _ eq supp _ (essential_ok ok.1.2) _ L low
  intro a ha
  obtain ⟨⟨v,r,s⟩,hm,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
  have hh := List.all_eq_true.mp ok.2 _ hm
  simp only [Bool.or_eq_true,beq_iff_eq,moved_eq_rename] at hh
  rcases hh with h | h
  · rw [h]
    exact ⟨false,funext bit_zero⟩
  · rw [h]
    exact ⟨true,funext bit_one⟩

def selected (m : Nat) : List (Nat × Sig) :=
  (List.range 9).filterMap fun i => if m.testBit i then some (i,inputs.getD i zero) else none

def vars (m : Nat) := (selected m).map Prod.snd

def varsX (m : Nat) : List Sig := if m.testBit 9 then vars m ++ [seed] else vars m

def vertex (m j : Nat) := if m.testBit j then inputs.getD j zero else zero

def graphGoal (m : Nat) : Sig :=
  let x := vertex m
  (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 2 &&& x 3) ||| (x 3 &&& x 4) |||
    (x 4 &&& x 0) ||| (x 0 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 7) |||
    (x 3 &&& x 8) ||| (x 5 &&& x 7) ||| (x 6 &&& x 8) ||| (x 8 &&& x 5)

def cube0 : Nat → Nat
  | 0 => 0xff
  | 1 => 0x55
  | 2 => 0x33
  | 3 => 0x11
  | 4 => 0xf
  | 5 => 0x5
  | 6 => 0x3
  | _ => 0x1

def cube3 : Nat → Nat
  | 0 => 0x101010101010101
  | 1 => 0x1000100010001
  | 2 => 0x10100000101
  | 3 => 0x100000001
  | 4 => 0x1010101
  | 5 => 0x10001
  | 6 => 0x101
  | _ => 0x1

def cube6 : Nat → Nat
  | 0 => 0x10000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001
  | 1 => 0x1000000000000000000000000000000010000000000000000000000000000000100000000000000000000000000000001
  | 2 => 0x100000000000000010000000000000000000000000000000000000000000000010000000000000001
  | 3 => 0x10000000000000000000000000000000000000000000000000000000000000001
  | 4 => 0x1000000000000000100000000000000010000000000000001
  | 5 => 0x100000000000000000000000000000001
  | 6 => 0x10000000000000001
  | _ => 0x1

def subcube (z o : Nat) : Sig :=
  let fixed := z ||| o
  if z &&& o != 0 then zero else
    BitVec.ofNat 512 ((cube0 (fixed &&& 7)*cube3 ((fixed >>> 3) &&& 7)*cube6 ((fixed >>> 6) &&& 7)) <<< o)

def fixRows (z o : Nat) : List Move :=
  (List.range 9).filterMap fun j =>
    let x := inputs.getD j zero
    let step := Fin.ofNat 512 (1 <<< j)
    if z.testBit j then some (zero,x,step)
    else if o.testBit j then some (~~~x,zero,step) else none

def swapRows (v : Nat) : Move :=
  let i := v &&& 15
  let j := v >>> 4
  let a := inputs.getD i zero
  let b := inputs.getD j zero
  let d := (1 <<< j)-(1 <<< i)
  (a &&& ~~~b,b &&& ~~~a,Fin.ofNat 512 d)

def supportPairs (w : Bool) (mask : Nat) : List (Sig × Row × Row) :=
  (selected mask).map fun (i,a) =>
    let r := if w && i==0 then 8 else if w && i==3 then 1 else 0
    (a,Fin.ofNat 512 r,Fin.ofNat 512 (r ||| (1 <<< i)))

def graphPairs (m hints : Nat) : List (Sig × Row × Row) :=
  (selected m).map fun (i,a) =>
    let r := 1 <<< ((hints >>> (4*i)) &&& 15)
    (a,Fin.ofNat 512 r,Fin.ofNat 512 (r ||| (1 <<< i)))

def properB (T : Sig) := T != zero && T != one

theorem proper_of (T : Sig) (h : properB T = true) : proper T := by
  simpa only [properB,proper,Bool.and_eq_true,bne_iff_ne] using h

def assertSize (m hints L : Nat) :=
  let xs := graphPairs m hints
  properB (graphGoal m) && checkEssential (graphGoal m) (vars m) xs &&
    decide (L ≤ (xs.map Prod.fst).toFinset.card-1)

theorem size_of {u m hints L} (h : assertSize m hints L = true) :
    Lower u (vars m) (graphGoal m) L := by
  simp only [assertSize,Bool.and_eq_true,decide_eq_true_eq] at h
  intro p bank hr ha
  exact h.2.trans (lower_count (proper_of _ h.1.1) _ h.1.2 p bank hr ha)

abbrev ColumnInfo := Nat × Nat × Nat × Nat × Nat

def colFree (m z o : Nat) := m ^^^ (m &&& (z ||| o))

def chartGoal (m : Nat) : Sig := graphGoal m

def rawMask (m : Nat) (c : ColumnInfo) : Nat := m ^^^ (m &&& (c.1 &&& 512))

def colCheck (m : Nat) (c : ColumnInfo) (prior : Nat → Nat) : Bool :=
  let (z,o,q,s,L) := c
  let ms := fixRows z o
  let raw := rawMask m c
  let free := colFree raw z o
  let G := movedWord ms (chartGoal m)
  let xs := supportPairs (free.testBit 9) s
  let count := (xs.map Prod.fst).toFinset.card
  properB G && checkMap ms (varsX raw) (chartGoal m) (varsX free) G &&
    (movedWord ms (subcube z o)==one) &&
    (if q=0 then checkEssential G (varsX free) xs && decide (L ≤ count-1)
     else properB (graphGoal q) &&
       checkLift (fixRows (colFree free q 0) 0) G (varsX free) (varsX q) (graphGoal q) xs &&
       decide (L ≤ prior q+count))

theorem col_sound {u} {m : Nat} (c : ColumnInfo) (prior : Nat → Nat)
    (valid : ∀ q, Lower u (varsX q) (graphGoal q) (prior q))
    (ok : colCheck m c prior = true) : Slice u (varsX (rawMask m c)) (chartGoal m) (subcube c.1 c.2.1) c.2.2.2.2 := by
  revert ok
  obtain ⟨z,o,q,s,L⟩ := c
  intro ok
  let ms := fixRows z o
  let raw := rawMask m (z,o,q,s,L)
  let free := colFree raw z o
  let G := movedWord ms (chartGoal m)
  let xs := supportPairs (free.testBit 9) s
  change (((properB G && checkMap ms (varsX raw) (chartGoal m) (varsX free) G) &&
    (movedWord ms (subcube z o)==one)) && _) = true at ok
  simp only [Bool.and_eq_true,beq_iff_eq] at ok
  apply slice_correct ok.1.1.2 ok.1.2 (proper_of _ ok.1.1.1)
  intro p bank hr ha
  have hh := ok.2
  by_cases hq : q=0
  · simp only [colCheck,hq,if_true,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hh.2.trans (lower_count (proper_of _ ok.1.1.1) xs hh.1 p bank hr ha)
  · simp only [colCheck,hq,if_false,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hh.2.trans (lift_ok hh.1.2 (proper_of _ ok.1.1.1) (proper_of _ hh.1.1) (valid q) p bank hr ha)

def relabelOK (old rep : Nat) (swaps : List Nat) :=
  (properB (graphGoal old) && plainWord (graphGoal old) && (varsX old).all plainWord) && properB (graphGoal rep) &&
    checkMap (swaps.map swapRows) (varsX old) (graphGoal old) (varsX rep) (graphGoal rep)

theorem relabel_of {u old rep L swaps} (ok : relabelOK old rep swaps = true)
    (h : Lower u (varsX rep) (graphGoal rep) L) : Lower u (varsX old) (graphGoal old) L := by
  simp only [relabelOK,Bool.and_eq_true] at ok
  exact lower_map ok.2 (proper_of _ ok.1.1.1.1) ok.1.1.1.2 ok.1.1.2 (proper_of _ ok.1.2) h

def boundsBefore (entries : List (Nat × Nat)) (q : Nat) :=
  ((entries.find? (fun a => a.1 == q)).map Prod.snd).getD 0

theorem before_sound {u} (entries : List (Nat × Nat))
    (sound : ∀ e ∈ entries, Lower u (varsX e.1) (graphGoal e.1) e.2) (q : Nat) :
    Lower u (varsX q) (graphGoal q) (boundsBefore entries q) := by
  unfold boundsBefore
  cases h : entries.find? (fun a => a.1 == q) with
  | none => exact fun _ _ _ _ => Nat.zero_le _
  | some e =>
    have he := List.mem_of_find?_eq_some h
    have hit : (fun a : Nat × Nat => a.1 == q) e = true := List.find?_some (p:=fun a : Nat × Nat => a.1 == q) (a:=e) h
    have eq : e.1=q := beq_iff_eq.mp hit
    simpa only [Option.map_some,Option.getD_some,eq] using sound e he

abbrev BoundPool := Sig × Nat × Nat × List Sig

def BoundPool.domain (c : BoundPool) : Sig := c.1

def BoundPool.bound (c : BoundPool) : Nat := c.2.1

def BoundPool.paid (c : BoundPool) : Nat := c.2.2.1

def BoundPool.wires (c : BoundPool) : List Sig := c.2.2.2

def ValidPool (u : Bool) (raw : List Sig) (T : Sig) (c : BoundPool) :=
  ∃ (f : Row → Row) (roots : List Sig) (bank : List (Wire Row)),
    (∀ r, bit (f r) c.domain = true) ∧ ¬Constant (restrictRows f (observe T)) ∧
    (∀ q ws, Reach u (roots.map observe) q ws → Available u ws (restrictRows f (observe T)) → c.bound ≤ q) ∧
    Reach u (roots.map observe) c.paid bank ∧ poolSupply u f bank c.wires ∧ True

theorem build_valid {u raw T d lb} (h : Slice u raw T d lb) (cs : List Choice) {ws}
    (build : makePool u d raw cs = some ws) : ValidPool u raw T ⟨d,lb,cs.length,ws⟩ := by
  obtain ⟨f,roots,dom,sup,nc,prior⟩ := h
  obtain ⟨bank,hr,hs⟩ := makePool_sound dom (Reach.start (roots:=roots.map observe)) sup cs build
  exact ⟨f,roots,bank,dom,nc,prior,by simpa [BoundPool.paid] using hr,hs,trivial⟩

theorem valid_exclude {u raw T c} (valid : ValidPool u raw T c) (k : Nat) (rest : List Sig)
    (choice : Choice) (paid : Bool)
    (known : ∀ a ∈ rest, availableB u c.domain c.wires a = true)
    (buy : if paid then choiceOK u c.domain c.wires choice = true
       else availableB u c.domain c.wires (choiceVal choice) = true)
    (bound : k+c.paid+paid.toNat <
      c.bound+(choiceVal choice :: rest).countP (isMaskedConstant c.domain))
    (nd : (choiceVal choice :: rest).Nodup) :
    Impossible u T k (choiceVal choice :: rest).toFinset := by
  intro t ht run
  obtain ⟨f,roots,bank,dom,nc,lo,hp,hs,_⟩ := valid
  let ws := choiceVal choice::rest
  have done (n : Nat) (out : List (Wire Row)) (reach : Reach u (roots.map observe) n out)
      (zs : poolSupply u f out (choiceVal choice::rest)) (le : n = c.paid+paid.toNat) : False := by
    have covered : supply u out ((ws.map observe).map (restrictRows f)) := by
      intro v hv
      obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hm
      exact zs _ ha
    have b := projected_bound f (list_run run ws nd rfl) nc reach covered lo
    have cm := count_constants dom ws
    change k+c.paid+paid.toNat < c.bound+ws.countP (isMaskedConstant c.domain) at bound
    omega
  cases paid with
  | false =>
    apply done _ _ hp _ rfl
    intro a h
    rcases List.mem_cons.mp h with rfl | hm
    · exact availableB_sound dom hs buy
    · exact availableB_sound dom hs (known _ hm)
  | true =>
    obtain ⟨out,hr,hc⟩ := pay_choice dom hp hs choice buy
    apply done _ _ hr _ rfl
    intro a h
    rcases List.mem_cons.mp h with rfl | hm
    · exact hc _ (by simp)
    · have point : ∀ v ∈ c.wires, Available u out (restrictRows f (observe v)) :=
        fun v hu => hc v (List.mem_cons_of_mem _ hu)
      exact availableB_sound dom point (known _ hm)

def scalarPoolCut (u : Bool) (c : BoundPool) (k : Nat) (rest : List Sig) (op : Choice) :=
  let z := choiceVal op
  let extra := !(availableB u c.domain c.wires z)
  ((k+c.paid+extra.toNat < c.bound+(z::rest).countP (isMaskedConstant c.domain)) &&
    rest.all (availableB u c.domain c.wires)) && (!extra || choiceOK u c.domain c.wires op)

theorem scalarPoolCut_sound {u raw T c} (valid : ValidPool u raw T c) {k rest op}
    (nd : (choiceVal op::rest).Nodup) (cut : scalarPoolCut u c k rest op = true) :
    Impossible u T k (choiceVal op::rest).toFinset := by
  let extra := !(availableB u c.domain c.wires (choiceVal op))
  apply valid_exclude valid k rest op extra _ _ _ nd
  · simp only [scalarPoolCut,Bool.and_eq_true,List.all_eq_true] at cut
    exact cut.1.2
  · simp only [scalarPoolCut,Bool.and_eq_true,Bool.or_eq_true] at cut
    cases he : availableB u c.domain c.wires (choiceVal op) <;> simp_all [extra]
  · simp only [scalarPoolCut,Bool.and_eq_true,decide_eq_true_eq] at cut
    exact cut.1.1

def materialize (u : Bool) (raw : List Sig) (cs : List Choice) (d : Sig) (lb : Nat) : Option BoundPool :=
  (makePool u d raw cs).map (fun pool => ⟨d,lb,cs.length,pool⟩)

theorem materialize_sound {u raw T d L cs c} (slice : Slice u raw T d L)
    (h : materialize u raw cs d L = some c) : ValidPool u raw T c := by
  unfold materialize at h
  cases he : makePool u d raw cs with
  | none => simp [he] at h
  | some pool =>
    simp only [he,Option.map_some,Option.some.injEq] at h
    subst c
    exact build_valid slice cs he

abbrev Bits := BitVec 768

abbrev Signals := Bits × Bits

abbrev Decor := Sig × Signals

def ofRows {n : Nat} (r : Fin n → Row) (v : Sig) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn (fun i => bit (r i) v))).cast List.length_ofFn

theorem ofRows_bit {n : Nat} (r : Fin n → Row) (v : Sig) (i : Fin n) :
    (ofRows r v).getLsbD i.val = bit (r i) v := by
  simp only [ofRows,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]

def pairSig (r s : Fin 768 → Row) (a : Sig) : Signals := (ofRows r a,ofRows s a)

def properPairs (T : Sig) (r s : Fin 768 → Row) :=
  ∀ i, bit (r i) T = true ∧ bit (s i) T = false

theorem pair_sep {T r s} (h : properPairs T r s) : Sep T 768 r s (pairSig r s) := by
  exact ⟨h,fun a i => ⟨ofRows_bit _ _ _,ofRows_bit _ _ _⟩⟩

def faithful (r s : Fin 768 → Row) (x : Decor) := x.2 = pairSig r s x.1

def bv {n : Nat} (d : Nat) (a b : BitVec n) : BitVec n :=
  if d=0 then a &&& b else if d=1 then a ||| b else if d=2 then a &&& ~~~b else ~~~a &&& b

def dbin (d : Nat) (x y : Decor) : Decor := (bin d x.1 y.1,bv d x.2.1 y.2.1,bv d x.2.2 y.2.2)

theorem ofRows_bin {n : Nat} (r : Fin n → Row) (d : Nat) (a b : Sig) :
    ofRows r (bin d a b) = bv d (ofRows r a) (ofRows r b) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have h := ofRows_bit r (bin d a b) ⟨j,hj⟩
  rw [bit_bin,←ofRows_bit r a ⟨j,hj⟩,←ofRows_bit r b ⟨j,hj⟩] at h
  rw [h]
  unfold bv
  split_ifs <;> simp [hj]

theorem faithful_bin {r s x y} (d) (hx : faithful r s x) (hy : faithful r s y) :
    faithful r s (dbin d x y) := by
  change x.2 = _ at hx
  change y.2 = _ at hy
  simp only [faithful,dbin,pairSig,ofRows_bin,hx,hy]

def defaultDecor : Decor := (zero,0,0)

theorem faithful_default (r s) : faithful r s defaultDecor := by
  apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj
  · change (0 : Bits).getLsbD j = (ofRows r zero).getLsbD j
    rw [show (ofRows r zero).getLsbD j = bit (r ⟨j,hj⟩) zero from ofRows_bit _ _ ⟨j,hj⟩,bit_zero]
    simp
  · change (0 : Bits).getLsbD j = (ofRows s zero).getLsbD j
    rw [show (ofRows s zero).getLsbD j = bit (s ⟨j,hj⟩) zero from ofRows_bit _ _ ⟨j,hj⟩,bit_zero]
    simp

theorem faithful_get {r s ws} (all : ∀ v ∈ ws, faithful r s v) (i : Nat) :
    faithful r s (List.getD ws i defaultDecor) := by
  simp only [List.getD_eq_getElem?_getD]
  cases e : ws[i]? with
  | none => exact faithful_default _ _
  | some v => exact all _ (List.mem_of_getElem? e)

def decodeBank (n : Nat) (bits : Nat) (ws : List Decor) : List Decor :=
  match n with
  | 0 => ws
  | k+1 =>
    let a := ws.getD (bits &&& 15) defaultDecor
    let b := ws.getD ((bits >>> 4) &&& 15) defaultDecor
    decodeBank k (bits >>> 10) (ws++[dbin ((bits >>> 8) &&& 3) a b])

theorem decode_faithful (n bits) (ws) (r s) (base : ∀ v ∈ ws, faithful r s v) :
    ∀ v ∈ decodeBank n bits ws, faithful r s v := by
  induction n generalizing ws bits with
  | zero => exact base
  | succ n ih =>
    apply ih
    intro v hv
    rcases List.mem_append.mp hv with hw | hz
    · exact base _ hw
    · obtain rfl := List.mem_singleton.mp hz
      exact faithful_bin _ (faithful_get base _) (faithful_get base _)

def asRow (cols : Nat → Bits) (i : Fin 768) : Row :=
  (BitVec.ofBoolListLE (List.ofFn (fun j : Fin 9 => (cols j.val).getLsbD i.val))).toFin.cast
    (by simp [List.length_ofFn])

theorem coordinate0 : ∀ r : Row, bit r (inputs.getD 0 zero) = r.val.testBit 0 := by decide +kernel

theorem coordinate1 : ∀ r : Row, bit r (inputs.getD 1 zero) = r.val.testBit 1 := by decide +kernel

theorem coordinate2 : ∀ r : Row, bit r (inputs.getD 2 zero) = r.val.testBit 2 := by decide +kernel

theorem coordinate3 : ∀ r : Row, bit r (inputs.getD 3 zero) = r.val.testBit 3 := by decide +kernel

theorem coordinate4 : ∀ r : Row, bit r (inputs.getD 4 zero) = r.val.testBit 4 := by decide +kernel

theorem coordinate5 : ∀ r : Row, bit r (inputs.getD 5 zero) = r.val.testBit 5 := by decide +kernel

theorem coordinate6 : ∀ r : Row, bit r (inputs.getD 6 zero) = r.val.testBit 6 := by decide +kernel

theorem coordinate7 : ∀ r : Row, bit r (inputs.getD 7 zero) = r.val.testBit 7 := by decide +kernel

theorem coordinate8 : ∀ r : Row, bit r (inputs.getD 8 zero) = r.val.testBit 8 := by decide +kernel

theorem input_coords : ∀ (j : Fin 9) (r : Row),
    bit r (inputs.getD j.val zero) = r.val.testBit j.val := by
  intro j r
  fin_cases j
  · exact coordinate0 r
  · exact coordinate1 r
  · exact coordinate2 r
  · exact coordinate3 r
  · exact coordinate4 r
  · exact coordinate5 r
  · exact coordinate6 r
  · exact coordinate7 r
  · exact coordinate8 r

theorem asRow_bit (cols : Nat → Bits) (i : Fin 768) (j : Fin 9) :
    bit (asRow cols i) (inputs.getD j.val zero) = (cols j.val).getLsbD i.val := by
  rw [input_coords]
  change (BitVec.ofBoolListLE (List.ofFn (fun h : Fin 9 => (cols h.val).getLsbD i.val))).getLsbD j.val = _
  simp only [BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [j.isLt]

def rawDecor (m : Nat) (p q : Nat → Bits) : List Decor :=
  (selected m).map (fun (j,a) => (a,p j,q j))

theorem selected_entry {m j a} (h : (j,a) ∈ selected m) :
    j<9 ∧ a=inputs.getD j zero := by
  obtain ⟨v,hv,hh⟩ := List.mem_filterMap.mp h
  simp only [List.mem_range] at hv
  split at hh
  next =>
    cases hh
    exact ⟨hv,rfl⟩
  next => contradiction

theorem raw_faithful (m) (p q : Nat → Bits) :
    ∀ a ∈ rawDecor m p q, faithful (asRow p) (asRow q) a := by
  intro a ha
  obtain ⟨⟨j,v⟩,hv,rfl⟩ := List.mem_map.mp ha
  obtain ⟨hj,rfl⟩ := selected_entry hv
  apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi
  · exact (asRow_bit p ⟨i,hi⟩ ⟨j,hj⟩).symm.trans (ofRows_bit _ _ ⟨i,hi⟩).symm
  · exact (asRow_bit q ⟨i,hi⟩ ⟨j,hj⟩).symm.trans (ofRows_bit _ _ ⟨i,hi⟩).symm

def liftGoal (m : Nat) (v : Nat → Bits) : Bits :=
  let x := fun j => if m.testBit j then v j else 0
  (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 2 &&& x 3) ||| (x 3 &&& x 4) |||
    (x 4 &&& x 0) ||| (x 0 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 7) |||
    (x 3 &&& x 8) ||| (x 5 &&& x 7) ||| (x 6 &&& x 8) ||| (x 8 &&& x 5)

theorem bit_vertex (m : Nat) (v : Nat → Bits) (i : Fin 768) (j : Fin 9) :
    bit (asRow v i) (vertex m j.val) =
    ((if m.testBit j.val then v j.val else 0) : Bits).getLsbD i.val := by
  by_cases hh : m.testBit j.val = true
  · simpa [vertex,hh] using asRow_bit v i j
  · simp [vertex,hh,bit_zero]

theorem bit_liftGoal (m : Nat) (v : Nat → Bits) (i : Fin 768) :
    bit (asRow v i) (graphGoal m) = (liftGoal m v).getLsbD i.val := by
  have pos (j : Nat) (hj : j<9) : (vertex m j).getLsbD (asRow v i).val = ((if m.testBit j then v j else 0) : Bits).getLsbD i.val := bit_vertex m v i ⟨j,hj⟩
  simp only [bit,graphGoal,liftGoal,BitVec.getLsbD_and,BitVec.getLsbD_or]
  simp only [pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 3 (by decide),pos 4 (by decide),pos 5 (by decide),pos 6 (by decide),pos 7 (by decide),pos 8 (by decide)]

abbrev Cov := Bits × Bits × Bits

def addCov (z : Bits) (c : Cov) : Cov :=
  (z ||| c.1, (z &&& ~~~c.1) ||| (c.2.1 &&& ~~~z),
   (z &&& c.2.1) ||| (c.2.2 &&& ~~~z))

def coverage (d : Bool) (v : List Decor) : Cov :=
  v.foldr (fun a c => addCov (column d a.2) c) (0,0,0)

def takeOne (c : Cov) (a : Bits) : Bits := c.1 &&& ~~~(c.2.1 &&& a)

def takeTwo (c : Cov) (a b : Bits) : Bits :=
  c.1 &&& ~~~((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b)))

theorem cov_one (c : Cov) (a : Bits) : takeOne (addCov a c) a=c.1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [takeOne,addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases c.1.getLsbD i <;> cases c.2.1.getLsbD i <;> rfl

theorem cov_two (c : Cov) (a b : Bits) : takeTwo (addCov a (addCov b c)) a b=c.1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [takeTwo,addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
    cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl

theorem add_swap (c : Cov) (a b : Bits) : addCov a (addCov b c)=addCov b (addCov a c) := by
  apply Prod.ext
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [addCov,BitVec.getLsbD_or]
    cases a.getLsbD i <;> cases b.getLsbD i <;> rfl
  · apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
      simp only [addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and] <;>
      cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
      cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl

theorem cov_perm (d : Bool) {l r : List Decor} (h : l.Perm r) : coverage d l=coverage d r := by
  induction h with
  | nil => rfl
  | cons a _ ih => exact congrArg (addCov (column d a.2)) ih
  | swap a b t => exact add_swap _ _ _
  | trans _ _ h1 h2 => exact h1.trans h2

theorem cov_word (d : Bool) (v : List Decor) {r s} (good : ∀ a ∈ v, faithful r s a) :
    (coverage d v).1 = covered d (pairSig r s) (v.map Prod.fst) := by
  induction v with
  | nil => rfl
  | cons a v ih =>
    change (column d a.2 ||| (coverage d v).1) = column d (pairSig r s a.1) ||| _
    rw [show a.2=pairSig r s a.1 from good _ (by simp),ih (fun a ha => good a (by simp [ha]))]

def delOne (ws : List Decor) (a : Decor) (keep : Bool) :=
  if keep then ws else ws.erase a

def delTwo (ws : List Decor) (a b : Decor) (ka kb : Bool) :=
  delOne (delOne ws a ka) b kb

theorem delOne_perm {ws : List Decor} (a : Decor) (ha : a ∈ ws) :
    ws.Perm (a::ws.erase a) := List.perm_cons_erase ha

theorem cover_one {ws : List Decor} (d : Bool) (a : Decor) (ha : a ∈ ws) (keep : Bool) :
    (coverage d (delOne ws a keep)).1 =
      (if keep then (coverage d ws).1 else takeOne (coverage d ws) (column d a.2)) := by
  cases keep
  · change (coverage d (ws.erase a)).1 = takeOne (coverage d ws) _
    rw [cov_perm d (delOne_perm a ha)]
    exact (cov_one _ _).symm
  · rfl

theorem delTwo_perm {ws : List Decor} (a b : Decor) (ha : a ∈ ws) (hb : b ∈ ws) (hne : a≠b) :
    ws.Perm (a::b::(ws.erase a).erase b) := by
  have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm hne)).mpr hb
  exact (delOne_perm a ha).trans (List.Perm.cons _ (delOne_perm b hm))

theorem cover_two {ws : List Decor} (d : Bool) (a b : Decor) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : a ≠ b) (ka kb : Bool) :
    (coverage d (delTwo ws a b ka kb)).1 =
      (if ka then (if kb then (coverage d ws).1 else takeOne (coverage d ws) (column d b.2))
       else if kb then takeOne (coverage d ws) (column d a.2)
       else takeTwo (coverage d ws) (column d a.2) (column d b.2)) := by
  cases ka <;> cases kb
  · change (coverage d ((ws.erase a).erase b)).1 = takeTwo (coverage d ws) _ _
    rw [cov_perm d (delTwo_perm a b ha hb ne)]
    exact (cov_two _ _ _).symm
  · exact cover_one d a ha false
  · exact cover_one d b hb false
  · rfl

def sameWords (a b : List Sig) := (a.all (fun x => b.contains x)) && (b.all (fun x => a.contains x))

theorem sameWords_sound {xs ys} (h : sameWords xs ys = true) : xs.toFinset=ys.toFinset := by
  simp only [sameWords,Bool.and_eq_true,List.all_eq_true,List.contains_eq_mem,decide_eq_true_eq] at h
  ext a
  simp only [List.mem_toFinset]
  exact ⟨h.1 a,h.2 a⟩

def keyWord (v : Sig) :=
  let n := v.toNat % 2305843009213693951
  (n*(n+971)) % 2305843009213693951

def keySet (xs : List Sig) := xs.foldl (fun v x => v+keyWord x) 0

def closeChild (u : Bool) (pools : List BoundPool) (links : Nat → List (List Sig)) (k : Nat)
    (rest : List Sig) (op : Choice) :=
  let ws := choiceVal op::rest
  (links (keySet ws)).any (sameWords ws) || pools.any (fun p => scalarPoolCut u p k rest op)

theorem closeChild_sound {u raw T pools links k rest op}
    (pValid : ∀ p ∈ pools, ValidPool u raw T p)
    (lValid : ∀ tag xs, xs ∈ links tag → Impossible u T k (List.toFinset xs))
    (nd : (choiceVal op :: rest).Nodup)
    (h : closeChild u pools links k rest op = true) :
    Impossible u T k (choiceVal op :: rest).toFinset := by
  simp only [closeChild,Bool.or_eq_true,List.any_eq_true] at h
  rcases h with ⟨xs,hx,ok⟩ | ⟨p,hp,ok⟩
  · rw [sameWords_sound ok]
    exact lValid _ _ hx
  · exact scalarPoolCut_sound (pValid _ hp) nd ok

abbrev CovPair := Cov × Bool

def preCov (u : Bool) (ws : List Decor) : CovPair := (coverage (!u) ws,u)

def restCov (v : Cov) (a b : Bits) (ka kb : Bool) :=
  if ka then (if kb then v.1 else takeOne v b) else if kb then takeOne v a else takeTwo v a b

theorem delOne_sub (ws : List Decor) (a : Decor) (k : Bool) : (delOne ws a k).Sublist ws := by
  cases k
  · exact List.erase_sublist
  · exact List.Sublist.refl _

theorem keep_sub (ws : List Decor) (a b : Decor) (ka kb : Bool) :
    (delTwo ws a b ka kb).Sublist ws := (delOne_sub _ _ _).trans (delOne_sub _ _ _)

theorem len_keep (ws : List Decor) (a b : Decor) (ka kb : Bool) (ha : a ∈ ws) (hb : b ∈ ws) (ne : a≠b) :
    (delTwo ws a b ka kb).length =
      ws.length - (if ka then 0 else 1) - (if kb then 0 else 1) := by
  have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm ne)).mpr hb
  cases ka <;> cases kb <;> simp [delTwo,delOne,List.length_erase_of_mem ha,List.length_erase_of_mem hb,List.length_erase_of_mem hm]

def movedChoice (op : Nat) (a b : Decor) : Choice := (op,a.1,b.1)

abbrev NodeContext := Nat × Nat × List Decor × CovPair × List BoundPool × (Nat → List (List Sig))

def evalMove (c : NodeContext) (op : Nat) (a b z : Decor) (ka kb : Bool) :=
  let (cap,n,ws,cov,pools,links) := c
  let len := 1+(n - (if ka then 0 else 1) - (if kb then 0 else 1))
  if len>cap then true else
    let d := !cov.2
    let rs := restCov cov.1 (column d a.2) (column d b.2) ka kb
    if (rs ||| column d z.2) != BitVec.allOnes 768 then true else
    if !properB z.1 || ws.any (fun v => v.1==z.1) then true else
      let rest := (delTwo ws a b ka kb).map Prod.fst
      closeChild cov.2 pools links (cap-1) rest (movedChoice op a b)

def moveFront (ws : List Decor) (op : Nat) (a b : Decor) (ka kb : Bool) :=
  (dbin op a b).1 :: (delTwo ws a b ka kb).map Prod.fst

theorem evalMove_sound {u raw T r s ws pools links cap a b op ka kb}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : a≠b) (hcap : 0<cap)
    (pv : ∀ p ∈ pools, ValidPool u raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → Impossible u T (cap-1) (List.toFinset xs))
    (pro : proper (dbin op a b).1) (fresh : (dbin op a b).1 ∉ ws.map Prod.fst)
    (test : evalMove (cap,ws.length,ws,preCov u ws,pools,links) op a b (dbin op a b) ka kb = true) :
    Impossible u T (cap-1) (moveFront ws op a b ka kb).toFinset := by
  let z := dbin op a b
  let rest := delTwo ws a b ka kb
  let child := z.1 :: rest.map Prod.fst
  have sub : rest.Sublist ws := keep_sub _ _ _ _ _
  have ndc : child.Nodup := List.nodup_cons.mpr ⟨fun hm => fresh ((sub.map _).subset hm),
    nd.sublist (sub.map _)⟩
  have fr : ws.any (fun v => v.1==z.1) = false := by
    apply Bool.eq_false_iff.mpr
    intro hh
    obtain ⟨x,hx,he⟩ := List.any_eq_true.mp hh
    exact fresh (beq_iff_eq.mp he ▸ List.mem_map_of_mem hx)
  have pp : properB z.1 = true := by simpa [properB,proper] using pro
  have leq : 1+(ws.length-(if ka then 0 else 1)-(if kb then 0 else 1)) = child.length := by
    change _ = (z.1::rest.map Prod.fst).length
    rw [List.length_cons,List.length_map,len_keep _ _ _ _ _ ha hb ne,Nat.add_comm 1]
  intro k hk h
  have hsz := live_size h
  change child.toFinset.card ≤ k+1 at hsz
  rw [List.toFinset_card_of_nodup ndc] at hsz
  have len : child.length ≤ cap := by omega
  unfold evalMove at test
  change (if 1+(ws.length-_ - _) > cap then true else _) = true at test
  rw [leq,if_neg (by omega)] at test
  have sep := cover_required h (pair_sep pairs)
  let d := !u
  have g : (coverage d rest).1 = covered d (pairSig r s) (rest.map Prod.fst) :=
    cov_word _ _ (fun v hv => faith _ (sub.subset hv))
  have rz : (coverage d rest).1 = restCov (coverage d ws) (column d a.2) (column d b.2) ka kb :=
    cover_two d a b ha hb ne ka kb
  have hf := faithful_bin op (faith _ ha) (faith _ hb)
  change column d (pairSig r s z.1) ||| covered d (pairSig r s) (rest.map Prod.fst) = _ at sep
  change z.2 = pairSig r s z.1 at hf
  rw [←hf,←g,rz,BitVec.or_comm] at sep
  have be : ((restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 768) = false := by
    simpa using sep
  change (if (restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 768 then true else if !properB z.1 || ws.any (fun v => v.1==z.1) then true else _) = true at test
  rw [be,pp,fr] at test
  exact closeChild_sound (op:=movedChoice op a b) (rest:=rest.map Prod.fst) pv lv ndc test k hk h

def testPair (ctx : NodeContext) (a b : Decor) (op : Nat) :=
  let z := dbin op a b
  let attempt := evalMove ctx op a b z
  attempt false false && attempt true false && attempt false true && attempt true true

def opsOf (u : Bool) : List Nat := if u then [0,1,2,3] else [0,1]

theorem opsOf_mem {u d} (h : allowed u d) : d ∈ opsOf u := by
  rcases allowed_four h with rfl | rfl | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · cases u <;> simp [opsOf]
  · cases u <;> simp [opsOf]
  · simp [opsOf]
  · simp [opsOf]

def testRow (ctx : NodeContext) (a : Decor) (bs : List Decor) :=
    bs.all (fun b => (opsOf ctx.2.2.2.1.2).all (testPair ctx a b))

def testAll (ctx : NodeContext) : List Decor → Bool
  | [] => true
  | a::bs => testRow ctx a bs && testAll ctx bs

theorem all_binary {ctx ws} (h : testAll ctx ws=true) {a b : Decor} (ha : a∈ws) (hb : b∈ws)
    (ne : a≠b) : (∀ d, allowed ctx.2.2.2.1.2 d → testPair ctx a b d=true) ∨
      (∀ d, allowed ctx.2.2.2.1.2 d → testPair ctx b a d=true) := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    simp only [testAll,Bool.and_eq_true,testRow,List.all_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | haTail
    · have bm := (List.mem_cons.mp hb).resolve_left (Ne.symm ne)
      exact Or.inl fun d hd => h.1 b bm d (opsOf_mem hd)
    · rcases List.mem_cons.mp hb with rfl | hbTail
      · exact Or.inr fun d hd => h.1 a haTail d (opsOf_mem hd)
      · exact ih h.2 haTail hbTail

theorem testPair_at {ctx a b d} (h : testPair ctx a b d = true) (ka kb : Bool) :
    evalMove ctx d a b (dbin d a b) ka kb = true := by
  simp only [testPair,Bool.and_eq_true] at h
  cases ka <;> cases kb <;> first | exact h.1.1.1 | exact h.1.2 | exact h.1.1.2 | exact h.2

theorem keep_mem {v : List Sig} {w : Sig} (a : Sig) (k : Bool) :
    w ∈ kept k a v ↔ (w=a ∧ k=true) ∨ w∈v := by cases k <;> simp [kept]

theorem mem_delone {v : List Decor} (nd : v.Nodup) (a w : Decor) (k : Bool) :
    w ∈ delOne v a k ↔ w∈v ∧ (w≠a ∨ k=true) := by
  cases k <;> simp [delOne,nd.mem_erase_iff,and_comm]

theorem unique_value {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a∈ws) (hb : b∈ws) (eq : a.1=b.1) : a=b := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    obtain ⟨hn,ht⟩ := List.nodup_cons.mp nd
    rcases List.mem_cons.mp ha with rfl | haTail <;> rcases List.mem_cons.mp hb with rfl | hbTail
    · rfl
    · exact False.elim (hn (eq ▸ List.mem_map_of_mem hbTail))
    · exact False.elim (hn (eq.symm ▸ List.mem_map_of_mem haTail))
    · exact ih ht haTail hbTail

theorem kept_value {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a ∈ ws) (hb : b ∈ ws) (ka kb : Bool) (v : Sig) :
    v ∈ (delTwo ws a b ka kb).map Prod.fst ↔
    v ∈ ws.map Prod.fst ∧ (v≠a.1 ∨ ka=true) ∧ (v≠b.1 ∨ kb=true) := by
  have wn := nd.of_map
  have dn := wn.sublist (delOne_sub ws a ka)
  simp only [delTwo,List.mem_map,mem_delone wn,mem_delone dn]
  constructor
  · rintro ⟨w,hw,rfl⟩
    exact ⟨⟨_,hw.1.1,rfl⟩,hw.1.2.imp (fun ne eq => ne (unique_value nd hw.1.1 ha eq)) id,
          hw.2.imp (fun ne eq => ne (unique_value nd hw.1.1 hb eq)) id⟩
  · rintro ⟨⟨w,hm,rfl⟩,h1,h2⟩
    exact ⟨w,⟨⟨hm,h1.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,
        h2.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,rfl⟩

theorem binary_front {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a∈ws) (hb : b∈ws) (ne : a.1≠b.1) (d : Nat) (ka kb : Bool) :
    (moveFront ws d a b ka kb).toFinset =
      (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
  ext v
  have av := List.mem_map_of_mem (f:=Prod.fst) ha
  have bv' := List.mem_map_of_mem (f:=Prod.fst) hb
  simp only [moveFront,childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    kept_value nd ha hb,keep_mem,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,dbin]
  by_cases va : v=a.1 <;> by_cases vb : v=b.1 <;> cases ka <;> cases kb <;> simp_all

theorem childTwo_swap {u} (v : List Sig) (nd : v.Nodup) (a b : Sig) (d : Nat) (hd : allowed u d) (ka kb : Bool) :
    (childTwo v a b d ka kb).toFinset = (childTwo v b a (flipOp d) kb ka).toFinset := by
  ext x
  simp only [childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    keep_mem,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,bin_flip hd a b]
  tauto

theorem node_sound {u raw T r s ws pools links cap}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (out : T ∉ ws.map Prod.fst)
    (pv : ∀ p ∈ pools, ValidPool u raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → Impossible u T (cap-1) (List.toFinset xs))
    (checks : testAll (cap,ws.length,ws,preCov u ws,pools,links) ws = true) :
    Impossible u T cap (ws.map Prod.fst).toFinset := by
  by_cases hc : cap=0
  · intro k hk h
    have ke : k=0 := by omega
    subst k
    generalize he : (ws.map Prod.fst).toFinset = S at h
    obtain ⟨hS,_⟩ := h
    exact out (List.mem_toFinset.mp (by rw [he,hS]; exact Finset.mem_singleton_self _))
  have hc' : 0<cap := by omega
  apply enum_step nd out
  intro a ha b hb d hd ka kb ne fresh pro len
  obtain ⟨a,haW,rfl⟩ := List.mem_map.mp ha
  obtain ⟨b,hbW,rfl⟩ := List.mem_map.mp hb
  have ab : a≠b := fun e => ne (congrArg Prod.fst e)
  have one (a b : Decor) (d : Nat) (aa : a∈ws) (bb : b∈ws) (ne' : a.1≠b.1) (ka kb : Bool)
      (pr : proper (bin d a.1 b.1)) (fr : bin d a.1 b.1 ∉ ws.map Prod.fst)
      (test : testPair (cap,ws.length,ws,preCov u ws,pools,links) a b d = true) :
      Impossible u T (cap-1) (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
    rw [←binary_front nd aa bb ne']
    exact evalMove_sound pairs faith nd aa bb (fun e => ne' (congrArg Prod.fst e)) hc' pv lv
      pr fr (testPair_at test ka kb)
  rcases all_binary checks haW hbW ab with hh | hh
  · exact one a b d haW hbW ne ka kb pro fresh (hh d hd)
  · rw [childTwo_swap _ nd _ _ d hd]
    exact one b a (flipOp d) hbW haW (Ne.symm ne) kb ka (bin_flip hd a.1 b.1 ▸ pro)
      (bin_flip hd a.1 b.1 ▸ fresh) (hh _ (flip_flip hd).1)

theorem agree_inputs (r s : Row) (h : ∀ a ∈ inputs, bit r a = bit s a) : r=s := by
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j<9
  · let i : Fin 9 := ⟨j,hj⟩
    have hm : inputs.getD i.val zero ∈ inputs := by
      rw [← input_list]
      exact List.mem_ofFn.mpr ⟨i,rfl⟩
    exact (input_coords i r).symm.trans ((h _ hm).trans (input_coords i s))
  · have le : 512 ≤ 2^j := by
      change 2^9 ≤ 2^j
      exact Nat.pow_le_pow_right (by decide) (by omega)
    exact (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le r.isLt le)).trans
      (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le s.isLt le)).symm

def composedOK (p q : List Move) := inputs.all (fun a => movedWord p (movedWord q a) == a)

theorem composed_id {p q} (h : composedOK p q = true) (r : Row) :
    movedRow q (movedRow p r) = r := by
  apply agree_inputs
  intro a ha
  rw [←bit_moved,←bit_moved]
  have eq := beq_iff_eq.mp (List.all_eq_true.mp h a ha)
  rw [eq]

def autoOK (T : Sig) (p : List Move) :=
  (movedWord p T == T) && composedOK p p.reverse && composedOK p.reverse p

theorem rotate_excluded {u T n} {ws : List Sig} (hi : Impossible u T n ws.toFinset)
    (p : List Move) (ok : autoOK T p = true) : Impossible u T n (ws.map (movedWord p.reverse)).toFinset := by
  simp only [autoOK,Bool.and_eq_true,beq_iff_eq] at ok
  have onto : Function.Surjective (movedRow p) := fun r => ⟨movedRow p.reverse r,composed_id ok.2 r⟩
  intro k hk h
  have run := live_rename h (movedRow p) onto
  have goal : rename (movedRow p) T = T := (moved_eq_rename p T).symm.trans ok.1.1
  have inv (x : Sig) : rename (movedRow p) (movedWord p.reverse x) = x := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    change bit ⟨j,hj⟩ _ = bit ⟨j,hj⟩ _
    rw [bit_rename,bit_moved,composed_id ok.1.2]
  have back : (ws.map (movedWord p.reverse)).toFinset.image (rename (movedRow p)) = ws.toFinset := by
    ext a
    simp only [Finset.mem_image,List.mem_toFinset,List.mem_map]
    constructor
    · rintro ⟨v,⟨w,hw,rfl⟩,rfl⟩
      simpa only [inv] using hw
    · intro ha
      exact ⟨_,⟨a,ha,rfl⟩,inv a⟩
  rw [goal,back] at run
  exact hi k hk run

abbrev Packing := Nat × Nat × Nat × Nat × Nat × Nat × Nat × (Nat → Nat)

def emptyPacking : Packing := (0,0,0,0,0,0,0,fun _ => 0)

def packedAt (word : Nat → Nat) (pos len : Nat) :=
  let i := pos/8192
  let shift := pos % 8192
  let lo := word i >>> shift
  if shift+len ≤ 8192 then lo &&& ((1 <<< len)-1)
  else (lo ||| (word (i+1) <<< (8192-shift))) &&& ((1 <<< len)-1)

def lookupWord (nb slots sw vw iw pw : Nat) (data : Nat → Nat) (h : Nat) : Option (Nat × Nat) :=
  let a := h % nb
  let sh := packedAt data (a*sw) sw
  let row := (h/nb+sh)%slots
  let word := packedAt data (nb*sw+row*vw) vw
  if (word >>> (iw+pw)) == h/(nb*slots)%16 then
    some (word &&& ((1 <<< iw)-1),(word >>> iw) &&& ((1 <<< pw)-1))
  else none

abbrev Forest := Nat × Nat × (Nat → Bits × Bits) × List ColumnInfo × List (List Nat) ×
  (Nat → Packing) × (Nat → Nat → Option (Nat × Nat))

def Forest.mask (g : Forest) : Nat := g.1

def Forest.mode (g : Forest) : Bool := !(g.1.testBit 10)

def Forest.cap (g : Forest) : Nat := g.2.1

def Forest.samples (g : Forest) : Nat → Bits × Bits := g.2.2.1

def Forest.cols (g : Forest) : List ColumnInfo := g.2.2.2.1

def Forest.autos (g : Forest) : List (List Nat) := g.2.2.2.2.1

def Forest.levels (g : Forest) : Nat → Packing := g.2.2.2.2.2.1

def Forest.index (g : Forest) : Nat → Nat → Option (Nat × Nat) := g.2.2.2.2.2.2

def wiresOf (g : Forest) :=
  let ws := rawDecor g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)
  ws

theorem wires_faithful (g : Forest) : ∀ a ∈ wiresOf g,
    faithful (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2) a := by
  exact raw_faithful g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)

def targetOf (g : Forest) := chartGoal g.mask

def chartSamples (m : Nat) (v : Nat → Bits) :=
  liftGoal m v

theorem chart_bit (m : Nat) (v : Nat → Bits) (i : Fin 768) :
    bit (asRow v i) (chartGoal m) = (chartSamples m v).getLsbD i.val := by
  exact bit_liftGoal m v i

theorem chart_pairs {m : Nat} {p q : Nat → Bits}
    (hp : chartSamples m p = BitVec.allOnes 768) (hq : chartSamples m q = 0) :
    properPairs (chartGoal m) (asRow p) (asRow q) := by
  intro i
  simp only [chart_bit,hp,hq,BitVec.getLsbD_allOnes,i.isLt,decide_true,BitVec.getLsbD_zero]
  simp

def selectLive {α : Type} (bits : Nat) : List α → List α
  | [] => []
  | w::ws => if bits &&& 1 == 1 then w::selectLive (bits >>> 1) ws else selectLive (bits >>> 1) ws

theorem selectLive_sub {α : Type} (bits : Nat) (ws : List α) : (selectLive bits ws).Sublist ws := by
  induction ws generalizing bits with
  | nil => exact List.Sublist.slnil
  | cons a ws ih =>
    unfold selectLive
    split
    · exact List.Sublist.cons₂ _ (ih _)
    · exact List.Sublist.cons _ (ih _)

def storedDepth (_g : Forest) (depth : Nat) := depth

def readNode (g : Forest) (k i : Nat) : Nat × List Decor × List Decor :=
  let raw := wiresOf g
  let (_,depth,_,_,_,_,_,data) := g.levels k
  let len := 10*storedDepth g depth
  let width := len+raw.length+depth
  let recp := packedAt data (i*width) width
  let stored := recp &&& ((1 <<< len)-1)
  let ops := stored
  let bank := decodeBank depth ops raw
  (ops,bank,selectLive (recp >>> len) bank)

def getFieldV (x pos width : Nat) := (x >>> pos) &&& ((1 <<< width)-1)

def chosenSteps (bank : List Decor) (ops paid : Nat) : Nat → List Choice
  | 0 => []
  | n+1 =>
    let more := chosenSteps bank (ops >>> 10) (paid >>> 1) n
    if paid &&& 1 == 0 then more else
      (getFieldV ops 8 2,(bank.getD (ops &&& 15) defaultDecor).1,
        (bank.getD (getFieldV ops 4 4) defaultDecor).1) :: more

def buildRule (g : Forest) (ops d : Nat) (bank : List Decor) (idx paid : Nat) : Option BoundPool :=
  (g.cols[idx]?).bind fun ci =>
    materialize g.mode (varsX (rawMask g.mask ci)) (chosenSteps bank ops paid d) (subcube ci.1 ci.2.1) ci.2.2.2.2

theorem buildRule_sound (g : Forest)
    (cols : ∀ ci ∈ g.cols, Slice g.mode (varsX (rawMask g.mask ci)) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    {i ops depth bank paid c} (h : buildRule g ops depth bank i paid = some c) :
    ValidPool g.mode (vars g.mask) (targetOf g) c := by
  unfold buildRule at h
  cases e : g.cols[i]? with
  | none => simp [e] at h
  | some ci =>
    simp only [e,Option.bind_some] at h
    apply materialize_sound _ h
    exact cols ci (List.mem_of_getElem? e)

def getPairs (data : Nat → Nat) (w v : Nat) : Nat → Nat → List (Nat × Nat)
  | 0,_ => []
  | n+1,pos =>
    let x := packedAt data pos (w+v)
    (x &&& ((1 <<< w)-1),x >>> w) :: getPairs data w v n (pos+w+v)

def stateSet (g : Forest) (k i : Nat) := (readNode g k i).2.2.map Prod.fst

def linkedSet (g : Forest) (k : Nat) (pair : Nat × Nat) : Option (List Sig) :=
  if pair.1 ≥ (g.levels k).1 then none else
    (g.autos[pair.2]?).map fun perm => (stateSet g k pair.1).map (movedWord (perm.map swapRows).reverse)

theorem linkedSet_sound (g : Forest) (k : Nat)
    (names : ∀ x ∈ g.autos, autoOK (targetOf g) (x.map swapRows) = true)
    (earlier : ∀ i < (g.levels k).1, Impossible g.mode (targetOf g) k (stateSet g k i).toFinset)
    {pair out} (h : linkedSet g k pair = some out) :
    Impossible g.mode (targetOf g) k out.toFinset := by
  unfold linkedSet at h
  split at h
  · contradiction
  next valid =>
    cases e : g.autos[pair.2]? with
    | none => simp [e] at h
    | some perm =>
      simp only [e,Option.map_some,Option.some.injEq] at h
      subst out
      exact rotate_excluded (earlier _ (by omega)) _ (names _ (List.mem_of_getElem? e))

def nodeVerified (g : Forest) (k i : Nat) :=
  let raw := wiresOf g
  let (num,depth,cw,iw,pw,offw,lw,data) := g.levels k
  let (ops,bank,ws) := readNode g k i
  let values := ws.map Prod.fst
  let start := num*(10*storedDepth g depth+raw.length+depth)
  let pos := start+num*offw+packedAt data (start+i*offw) offw
  let nr := packedAt data pos 5
  let nl := packedAt data (pos+5) lw
  let st := pos+5+lw
  let rules := (getPairs data cw depth nr st).filterMap (fun (a,b) => buildRule g ops depth bank a b)
  let ls := fun tag => ((g.index k tag).bind (linkedSet g (k-1))).toList
  decide values.Nodup && !(values.contains (targetOf g)) &&
    (if k=0 then true else testAll (k,ws.length,ws,preCov g.mode ws,rules,ls) ws)

theorem nodeVerified_sound (g : Forest) (k i : Nat)
    (samples : properPairs (targetOf g) (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2))
    (cols : ∀ ci ∈ g.cols, Slice g.mode (varsX (rawMask g.mask ci)) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    (names : ∀ x ∈ g.autos, autoOK (targetOf g) (x.map swapRows) = true)
    (prior : k>0 → ∀ j < (g.levels (k-1)).1, Impossible g.mode (targetOf g) (k-1) (stateSet g (k-1) j).toFinset)
    (checked : nodeVerified g k i = true) : Impossible g.mode (targetOf g) k (stateSet g k i).toFinset := by
  simp only [nodeVerified,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true',List.contains_eq_mem] at checked
  have hN := checked.1.1
  have hT : targetOf g ∉ stateSet g k i := by simpa [stateSet] using checked.1.2
  by_cases h0 : k=0
  · subst k
    intro t lo h
    have ht : t=0 := by omega
    subst t
    generalize he : (stateSet g 0 i).toFinset = S at h
    obtain ⟨hS,_⟩ := h
    exact hT (List.mem_toFinset.mp (by rw [he,hS]; exact Finset.mem_singleton_self _))
  apply node_sound (raw:=vars g.mask) samples _ hN hT _ _ (by simpa only [h0,if_false] using checked.2)
  · intro v hv
    apply decode_faithful _ _ _ _ _ (wires_faithful g) v
    exact (selectLive_sub _ _).subset hv
  · intro p hp
    obtain ⟨⟨a,b⟩,_,h⟩ := List.mem_filterMap.mp hp
    exact buildRule_sound g cols h
  · intro tag xs hx
    have e : ((g.index k tag).bind (linkedSet g (k-1)))=some xs := by simpa using hx
    obtain ⟨pair,_,h⟩ := Option.bind_eq_some_iff.mp e
    exact linkedSet_sound g _ names (prior (by omega)) h

def block (g : Forest) (k start : Nat) : Nat → Bool
  | 0 => true
  | n+1 => nodeVerified g k (start+n) && block g k start n

theorem block_at {g k start n} (h : block g k start n=true) (j : Nat) (lo : start≤j) (hi : j<start+n) :
    nodeVerified g k j=true := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [block,Bool.and_eq_true] at h
    by_cases eq : j=start+n
    · simpa [eq] using h.1
    · exact ih h.2 (by omega)

theorem block_merge {g k start a b} (h : block g k start a=true)
    (h' : block g k (start+a) b=true) : block g k start (a+b)=true := by
  induction b with
  | zero => simpa using h
  | succ b ih =>
    simp only [block,Bool.and_eq_true] at h'
    simp only [Nat.add_succ,block,Bool.and_eq_true]
    exact ⟨by simpa [Nat.add_assoc] using h'.1,ih h'.2⟩

def checkedTables (g : Forest) (top : Nat) :=
  ∀ k ≤ top, block g k 0 (g.levels k).1 = true

def graphValid (g : Forest) (prior : Nat → Nat) :=
  (chartSamples g.mask (fun j => (g.samples j).1) == BitVec.allOnes 768) &&
  (chartSamples g.mask (fun j => (g.samples j).2) == 0) &&
  g.cols.all (fun c => colCheck g.mask c prior) &&
  g.autos.all (fun p => autoOK (targetOf g) (p.map swapRows))

theorem forest_all (g : Forest) (top : Nat) (prior : Nat → Nat)
    (lower : ∀ q, Lower g.mode (varsX q) (graphGoal q) (prior q))
    (geometry : graphValid g prior = true) (rows : checkedTables g top) :
    ∀ k ≤ top, ∀ i < (g.levels k).1, Impossible g.mode (targetOf g) k (stateSet g k i).toFinset := by
  simp only [graphValid,Bool.and_eq_true,List.all_eq_true,beq_iff_eq] at geometry
  intro k
  induction k with
  | zero =>
    intro hk i hi
    apply nodeVerified_sound g 0 i (chart_pairs geometry.1.1.1 geometry.1.1.2)
      (fun x hx => col_sound _ prior lower (geometry.1.2 x hx)) geometry.2 (by omega)
    exact block_at (rows 0 hk) i (by omega) (by omega)
  | succ k ih =>
    intro hk i hi
    apply nodeVerified_sound g _ i (chart_pairs geometry.1.1.1 geometry.1.1.2)
      (fun x hx => col_sound _ prior lower (geometry.1.2 x hx)) geometry.2
      (fun _ => by simpa using ih (by omega))
    exact block_at (rows _ hk) i (by omega) (by omega)

def indexedRoot (g : Forest) (k i : Nat) (ws : List Sig) :=
  decide (i < (g.levels k).1) && sameWords (stateSet g k i) ws

theorem root_index {g top prior k i ws} (low : ∀ q, Lower g.mode (varsX q) (graphGoal q) (prior q))
    (geom : graphValid g prior = true) (blocks : checkedTables g top) (le : k ≤ top)
    (idx : indexedRoot g k i ws = true) : Impossible g.mode (targetOf g) k ws.toFinset := by
  simp only [indexedRoot,Bool.and_eq_true,decide_eq_true_eq] at idx
  rw [←sameWords_sound idx.2]
  exact forest_all g top prior low geom blocks _ le i idx.1

def Known (u : Bool) (entries : List (Nat × Nat)) := ∀ e ∈ entries, Lower u (varsX e.1) (graphGoal e.1) e.2

def extendKnown (old : List (Nat × Nat)) (L : Nat) (relabels : List (Nat × List Nat)) :=
  relabels.map (fun v => (v.1,L)) ++ old

theorem extendKnown_ok {u old L m relabels} (previous : Known u old)
    (main : Lower u (varsX m) (graphGoal m) L)
    (ok : relabels.all (fun v => relabelOK v.1 m v.2) = true) :
    Known u (extendKnown old L relabels) := by
  intro e he
  rcases List.mem_append.mp he with hx | h
  · obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hx
    exact relabel_of (List.all_eq_true.mp ok _ hv) main
  · exact previous e h

theorem baseKnown : Known true [] := by simp [Known]

def lanePlace (v : Nat) (upper : Nat) := 2^769*upper+v

def combineLanes {α : Type} (f : α → Bits) : List α → Nat
  | [] => 0
  | x::xs => lanePlace (f x).toNat (combineLanes f xs)

def units : Nat → Nat
  | 0 => 0
  | n+1 => lanePlace 1 (units n)

theorem laneSmall (x : Bits) : x.toNat < 2^769 :=
  lt_trans x.isLt (by decide +kernel)

theorem place_and (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u &&& lanePlace b.toNat v = lanePlace (a &&& b).toNat (u &&& v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_and,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<769 <;> simp only [h,ite_true,ite_false,BitVec.toNat_and,Nat.testBit_and]

theorem place_or (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ||| lanePlace b.toNat v = lanePlace (a ||| b).toNat (u ||| v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_or,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<769 <;> simp only [h,ite_true,ite_false,BitVec.toNat_or,Nat.testBit_or]

theorem place_xor (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ^^^ lanePlace b.toNat v = lanePlace (a ^^^ b).toNat (u ^^^ v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_xor,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<769 <;> simp only [h,ite_true,ite_false,BitVec.toNat_xor,Nat.testBit_xor]

theorem lanes_and {α} (f g : α → Bits) (xs) :
    combineLanes f xs &&& combineLanes g xs = combineLanes (fun x => f x &&& g x) xs := by
  induction xs with
  | nil => simp [combineLanes]
  | cons a xs ih => simp only [combineLanes,place_and,ih]

theorem lanes_or {α} (f g : α → Bits) (xs) :
    combineLanes f xs ||| combineLanes g xs = combineLanes (fun x => f x ||| g x) xs := by
  induction xs with
  | nil => simp [combineLanes]
  | cons a xs ih => simp only [combineLanes,place_or,ih]

theorem lanes_xor {α} (f g : α → Bits) (xs) :
    combineLanes f xs ^^^ combineLanes g xs = combineLanes (fun x => f x ^^^ g x) xs := by
  induction xs with
  | nil => simp [combineLanes]
  | cons a xs ih => simp only [combineLanes,place_xor,ih]

def fullMarks (r packed : Nat) := ((packed+r) >>> 768) &&& r

theorem unit_bit (n i : Nat) (hi : i<n) : (units n).testBit (769*i) = true := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    rw [units,lanePlace,Nat.testBit_two_pow_mul_add _ (by decide +kernel : 1 < 2^769)]
    cases i with
    | zero => simp
    | succ i =>
      have di : 769*(i+1)-769=769*i := by omega
      have ge : ¬769*(i+1)<769 := by omega
      simp only [ge,ite_false,di]
      exact ih _ (by omega)

set_option maxRecDepth 8192 in
theorem guardBit (a : Bits) : (a.toNat+1).testBit 768 = (a==BitVec.allOnes 768) := by
  by_cases h : a=BitVec.allOnes 768
  · subst a
    decide +kernel
  · have lim := a.isLt
    have ne : a.toNat ≠ 2^768-1 := by
      intro eq
      apply h
      apply BitVec.eq_of_toNat_eq
      simpa only [BitVec.toNat_allOnes] using eq
    have lt : a.toNat+1<2^768 := by omega
    rw [Nat.testBit_eq_false_of_lt lt]
    exact (beq_eq_false_iff_ne.mpr h).symm

set_option maxRecDepth 8192 in
theorem mark_at {α} (f : α → Bits) (xs : List α) (i : Nat) (hi : i<xs.length) :
    (fullMarks (units xs.length) (combineLanes f xs)).testBit (769*i) =
      (f xs[i]==BitVec.allOnes 768) := by
  simp only [fullMarks,Nat.testBit_and,Nat.testBit_shiftRight,unit_bit _ _ hi,Bool.and_true]
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
    simp only [combineLanes,List.length_cons,units,lanePlace]
    have sum (u v x : Nat) : 2^769*u+x+(2^769*v+1)=2^769*(u+v)+(x+1) := by omega
    rw [sum,Nat.testBit_two_pow_mul_add _ (show (f a).toNat+1<2^769 from by have := (f a).isLt; omega)]
    have hi' : i < xs.length+1 := hi
    cases i with
    | zero => simpa using guardBit (f a)
    | succ i =>
      have ge : ¬769*(i+1)+768<769 := by omega
      have di : 769*(i+1)+768-769=769*i+768 := by omega
      simp only [ge,ite_false,di,List.getElem_cons_succ]
      apply ih i (by omega)

abbrev PackedSig := Nat × Nat

abbrev PackedCov := Nat × Nat × Nat

def packedSig {α} (s : α → Signals) (xs : List α) : PackedSig :=
  (combineLanes (fun x => (s x).1) xs,combineLanes (fun x => (s x).2) xs)

def packedCov {α} (c : α → Cov) (xs : List α) : PackedCov :=
  (combineLanes (fun x => (c x).1) xs,combineLanes (fun x => (c x).2.1) xs,
   combineLanes (fun x => (c x).2.2) xs)

def packedColumn (d : Bool) (a : PackedSig) :=
  if d then a.1 ^^^ (a.1 &&& a.2) else a.1 ^^^ a.2

theorem xor_meet (a b : Bits) : a ^^^ (a &&& b) = a &&& ~~~b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_xor,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> rfl

theorem packed_column {α} (s : α → Signals) (xs : List α) (d : Bool) :
    packedColumn d (packedSig s xs) = combineLanes (fun x => column d (s x)) xs := by
  cases d <;> simp only [packedColumn,packedSig,column,Bool.false_eq_true,ite_false,ite_true,lanes_and,lanes_xor,xor_meet]

def packedOp (op : Nat) (a b : PackedSig) : PackedSig :=
  if op=0 then (a.1 &&& b.1,a.2 &&& b.2) else if op=1 then (a.1 ||| b.1,a.2 ||| b.2)
  else if op=2 then (a.1 ^^^ (a.1 &&& b.1),a.2 ^^^ (a.2 &&& b.2))
  else (b.1 ^^^ (b.1 &&& a.1),b.2 ^^^ (b.2 &&& a.2))

theorem packed_op {α} (a b : α → Decor) (xs : List α) (op : Nat) :
    packedOp op (packedSig (fun x => (a x).2) xs) (packedSig (fun x => (b x).2) xs) =
    packedSig (fun x => (dbin op (a x) (b x)).2) xs := by
  by_cases h0 : op=0
  · simp only [packedOp,h0,ite_true,packedSig,lanes_and,dbin,bv]
  by_cases h1 : op=1
  · simp [packedOp,h1,packedSig,lanes_or,dbin,bv]
  by_cases h2 : op=2
  · simp [packedOp,h2,packedSig,lanes_and,lanes_xor,xor_meet,dbin,bv]
  · have e (x y : Bits) : ~~~x &&& y = y &&& ~~~x := BitVec.and_comm _ _
    simp only [packedOp,h0,h1,h2,ite_false,packedSig,lanes_and,lanes_xor,xor_meet,dbin,bv,e]

def takePacked (c : PackedCov) (a b : Nat) (ka kb : Bool) :=
  let without1 := fun w => c.1 ^^^ (c.1 &&& (c.2.1 &&& w))
  let without2 := c.1 ^^^ (c.1 &&& ((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b))))
  if ka then (if kb then c.1 else without1 b)
  else if kb then without1 a else without2

theorem takePacked_ok {α} (c : α → Cov) (a b : α → Bits) (xs : List α) (ka kb : Bool) :
    takePacked (packedCov c xs) (combineLanes a xs) (combineLanes b xs) ka kb =
    combineLanes (fun x => restCov (c x) (a x) (b x) ka kb) xs := by
  cases ka <;> cases kb <;>
    simp only [takePacked,packedCov,lanes_and,lanes_or,lanes_xor,xor_meet,restCov,takeOne,takeTwo,
      Bool.false_eq_true,ite_false,ite_true]

def contextWire (c : NodeContext) (i : Nat) := c.2.2.1.getD i defaultDecor

def checkAt (c : NodeContext) (i j op : Nat) (ka kb : Bool) :=
  let a := contextWire c i
  let b := contextWire c j
  evalMove c op a b (dbin op a b) ka kb

def combField (c : NodeContext) (d ka kb : Bool) (op i j : Nat) :=
  let a := contextWire c i
  let b := contextWire c j
  restCov c.2.2.2.1.1 (column d a.2) (column d b.2) ka kb |||
    column d (dbin op a b).2

def onMarks {α : Type} (f : α → Bool) (mask : Nat) : List α → Bool
  | [] => true
  | x::xs => if mask=0 then true else
    ((mask &&& 1 == 0) || f x) && onMarks f (mask >>> 769) xs

theorem marked_ok {α} (f : α → Bool) (mask : Nat) (xs : List α) (i : Nat) (hi : i<xs.length)
    (bitOn : mask.testBit (769*i)=true) (ok : onMarks f mask xs=true) : f xs[i]=true := by
  induction xs generalizing mask i with
  | nil => simp at hi
  | cons x xs ih =>
    have ne : mask≠0 := by intro e; simp [e] at bitOn
    simp only [onMarks,ne,ite_false,Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq] at ok
    cases i with
    | zero =>
      have nonzero : mask &&& 1 ≠ 0 := by
        intro he
        have at0 := congrArg (fun n : Nat => n.testBit 0) he
        simp only [Nat.testBit_and] at at0
        change mask.testBit 0=true at bitOn
        simp [bitOn] at at0
      exact ok.1.resolve_left nonzero
    | succ i =>
      apply ih (mask:=mask >>> 769) (i:=i) (by simpa using hi) _ ok.2
      simpa only [Nat.testBit_shiftRight,Nat.mul_succ,Nat.add_comm] using bitOn

abbrev Batch := Nat × Nat × Nat × List PackedSig × PackedCov

def makeBatch (k n : Nat) (xs : List NodeContext) : Batch :=
  (k,n,units xs.length,(List.range n).map (fun i => packedSig (fun c => (contextWire c i).2) xs),
    packedCov (fun c => c.2.2.2.1.1) xs)

def laneWire (b : Batch) (i : Nat) := b.2.2.2.1.getD i (0,0)

theorem laneWire_at (k n) (xs) {i : Nat} (h : i<n) :
    laneWire (makeBatch k n xs) i = packedSig (fun c => (contextWire c i).2) xs := by
  simp [laneWire,makeBatch,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range,h]

def availableMasked (u : Bool) (p : BoundPool) (m : Sig) :=
  m==zero || m==p.domain || (p.wires.map (masked p.domain)).any (fun v => v==m) ||
    (u && (p.wires.map (masked p.domain)).any (fun v => v==(p.domain ^^^ m)))

theorem masked_comp (d x : Sig) : masked d (neg x) = d ^^^ masked d x := by
  apply bit_ext
  intro r
  simp only [masked,neg,bit,BitVec.getLsbD_and,BitVec.getLsbD_not,BitVec.getLsbD_xor,r.isLt,decide_true,Bool.true_and]
  cases d.getLsbD r.val <;> cases x.getLsbD r.val <;> rfl

theorem available_mask (u) (p : BoundPool) (x : Sig) :
    availableB u p.domain p.wires x = availableMasked u p (masked p.domain x) := by
  simp only [availableB,availableMasked,masked_comp]

def constantLoss (p : Decor → Bool) (a : Decor) (keep : Bool) :=
  if keep then 0 else (p a).toNat

theorem lossBound (p : Decor → Bool) (ws : List Decor) (a : Decor) (keep : Bool) :
    ws.countP p ≤ (delOne ws a keep).countP p + constantLoss p a keep := by
  cases keep
  · simp only [delOne,Bool.false_eq_true,ite_false,constantLoss,List.countP_erase]
    split
    next h => simp [h.2]; omega
    next => omega
  · simp [delOne,constantLoss]

theorem keptCount (p : Decor → Bool) (ws : List Decor) (a b : Decor) (ka kb : Bool) :
    ws.countP p - constantLoss p a ka - constantLoss p b kb ≤
    (delTwo ws a b ka kb).countP p := by
  have h1 := lossBound p ws a ka
  have h2 := lossBound p (delOne ws a ka) b kb
  simp only [delTwo]
  omega

abbrev QuickPool := BoundPool × Nat × Bool

def summarizePool (u : Bool) (ws : List Decor) (p : BoundPool) : QuickPool :=
  (p,ws.countP (fun w => isMaskedConstant p.domain w.1),
     ws.all (fun w => availableB u p.domain p.wires w.1))

def fastCost (s : QuickPool) (k : Nat) (a b : Decor) (op : Nat) (ka kb : Bool) :=
  if !s.2.2 then false else
  let p := s.1
  let const := fun w : Decor => isMaskedConstant p.domain w.1
  let z := choiceVal (movedChoice op a b)
  let zm := masked p.domain z
  let zc := isMaskedConstant p.domain z
  let cm := s.2.1 - constantLoss const a ka - constantLoss const b kb + zc.toNat
  let free := zc || zm==masked p.domain a.1 || zm==masked p.domain b.1
  decide (k+p.paid+(!free).toNat < p.bound+cm)

theorem fastCost_good {u p k ws a b op ka kb} (ha : a∈ws) (hb : b∈ws) (al : allowedB u op=true)
    (h : fastCost (summarizePool u ws p) k a b op ka kb=true) :
    scalarPoolCut u p k ((delTwo ws a b ka kb).map Prod.fst) (movedChoice op a b)=true := by
  let z := choiceVal (movedChoice op a b)
  let const := fun w : Decor => isMaskedConstant p.domain w.1
  let free := isMaskedConstant p.domain z || masked p.domain z==masked p.domain a.1 ||
      masked p.domain z==masked p.domain b.1
  let rest := delTwo ws a b ka kb
  have ck := keptCount const ws a b ka kb
  change ws.countP const - constantLoss const a ka - constantLoss const b kb ≤ rest.countP const at ck
  by_cases all : ws.all (fun w => availableB u p.domain p.wires w.1)=true
  · have hav := List.all_eq_true.mp all
    have ready : free=true → availableB u p.domain p.wires z=true := by
      intro f
      simp only [free,Bool.or_eq_true,beq_iff_eq] at f
      rcases f with (zc|za)|zb
      · simp only [availableB,isMaskedConstant,Bool.or_eq_true] at zc ⊢
        exact Or.inl (Or.inl zc)
      · rw [available_mask,za,←available_mask]
        exact hav _ ha
      · rw [available_mask,zb,←available_mask]
        exact hav _ hb
    have extra : (!availableB u p.domain p.wires z).toNat ≤ (!free).toNat := by
      cases hf : free <;> cases he : availableB u p.domain p.wires z <;> simp_all
    have hs : (rest.map Prod.fst).all (availableB u p.domain p.wires)=true := by
      apply List.all_eq_true.mpr
      intro _ hm
      obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hm
      exact hav w ((keep_sub ws a b ka kb).subset hw)
    have opOK : choiceOK u p.domain p.wires (movedChoice op a b)=true := by
      simp [choiceOK,movedChoice,hav _ ha,hav _ hb,al]
    simp only [fastCost,summarizePool,all,Bool.not_true,Bool.false_eq_true,ite_false,decide_eq_true_eq] at h
    change k+p.paid+(!free).toNat < p.bound+(ws.countP const - constantLoss const a ka -
        constantLoss const b kb+(isMaskedConstant p.domain z).toNat) at h
    dsimp only [rest] at hs
    simp only [scalarPoolCut,hs,opOK,Bool.or_true,Bool.and_true,decide_eq_true_eq,List.countP_cons,
      List.countP_map,Function.comp_def]
    change k+p.paid+(!availableB u p.domain p.wires z).toNat <
      p.bound+(rest.countP const + if isMaskedConstant p.domain z then 1 else 0)
    cases hc : isMaskedConstant p.domain z <;> simp [hc] at h ⊢ <;> omega
  · simp [fastCost,summarizePool,all] at h

def quickAt (c : NodeContext) (i j op : Nat) (ka kb : Bool) :=
  let a := contextWire c i
  let b := contextWire c j
  (c.2.2.2.2.1.map (summarizePool c.2.2.2.1.2 c.2.2.1)).any (fun s => fastCost s (c.1-1) a b op ka kb)

theorem quickAt_good {c i j op ka kb} (hi : i<c.2.2.1.length) (hj : j<c.2.2.1.length) (al : allowedB c.2.2.2.1.2 op=true)
    (h : quickAt c i j op ka kb=true) : checkAt c i j op ka kb=true := by
  have mem (t) (ht : t<c.2.2.1.length) : contextWire c t ∈ c.2.2.1 := by
    simp [contextWire,List.getD_eq_getElem?_getD,ht]
  obtain ⟨_,hm,ok⟩ := List.any_eq_true.mp h
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hm
  have closed := fastCost_good (mem _ hi) (mem _ hj) al ok
  have cut : c.2.2.2.2.1.any (fun p => scalarPoolCut c.2.2.2.1.2 p (c.1-1)
      ((delTwo c.2.2.1 (contextWire c i) (contextWire c j) ka kb).map Prod.fst)
      (movedChoice op (contextWire c i) (contextWire c j)))=true :=
    List.any_eq_true.mpr ⟨p,hp,closed⟩
  simp only [checkAt,evalMove,closeChild,cut,Bool.or_true]
  repeat' split
  all_goals rfl

def fallbackAt (c : NodeContext) (i j op : Nat) (ka kb : Bool) :=
  (if (i<c.2.2.1.length ∧ j<c.2.2.1.length) ∧ allowedB c.2.2.2.1.2 op=true then quickAt c i j op ka kb else false) ||
    checkAt c i j op ka kb

theorem fallback_sound {c i j op ka kb} (h : fallbackAt c i j op ka kb=true) :
    checkAt c i j op ka kb=true := by
  simp only [fallbackAt,Bool.or_eq_true] at h
  rcases h with h | h
  · split at h
    next yes => exact quickAt_good yes.1.1 yes.1.2 yes.2 h
    next => contradiction
  · exact h

def batchMove (u : Bool) (b : Batch) (xs : List NodeContext) (i j op : Nat) (ka kb : Bool) :=
  let (k,n,r,_,cov) := b
  let len := 1+(n-(if ka then 0 else 1)-(if kb then 0 else 1))
  if len>k then true else
    let a := laneWire b i
    let b' := laneWire b j
    let z := packedOp op a b'
    let mask := fullMarks r (takePacked cov (packedColumn (!u) a) (packedColumn (!u) b') ka kb ||| packedColumn (!u) z)
    onMarks (fun c => fallbackAt c i j op ka kb) mask xs

theorem batchMove_at {u} (k n) (xs : List NodeContext) {i j op : Nat} {ka kb}
    (hi : i<n) (hj : j<n) {q : Nat} (hq : q<xs.length)
    (budget : xs[q].1=k) (arity : xs[q].2.1=n) (mode : xs[q].2.2.2.1.2=u)
    (pass : batchMove u (makeBatch k n xs) xs i j op ka kb=true) :
    checkAt xs[q] i j op ka kb=true := by
  let len := 1+(n-(if ka then 0 else 1)-(if kb then 0 else 1))
  have eval : checkAt xs[q] i j op ka kb =
      if len>k then true else if combField xs[q] (!u) ka kb op i j != BitVec.allOnes 768 then true
      else if !properB (dbin op (contextWire xs[q] i) (contextWire xs[q] j)).1 ||
        xs[q].2.2.1.any (fun v => v.1==(dbin op (contextWire xs[q] i) (contextWire xs[q] j)).1)
      then true else closeChild u xs[q].2.2.2.2.1 xs[q].2.2.2.2.2 (k-1)
        ((delTwo xs[q].2.2.1 (contextWire xs[q] i) (contextWire xs[q] j) ka kb).map Prod.fst)
        (movedChoice op (contextWire xs[q] i) (contextWire xs[q] j)) := by
    simp only [checkAt,evalMove,budget,arity,mode,len,combField] <;> rfl
  by_cases small : len>k
  · simp [eval,small]
  · let r := units xs.length
    let a := laneWire (makeBatch k n xs) i
    let b := laneWire (makeBatch k n xs) j
    let cov := packedCov (fun c : NodeContext => c.2.2.2.1.1) xs
    change (if len>k then true else onMarks _ (fullMarks r
       (takePacked cov (packedColumn (!u) a) (packedColumn (!u) b) ka kb |||
        packedColumn (!u) (packedOp op a b))) xs) = true at pass
    rw [if_neg small] at pass
    have ca : a = _ := laneWire_at k n xs hi
    have cb : b = _ := laneWire_at k n xs hj
    dsimp only [r,cov] at pass
    rw [ca,cb,packed_op,packed_column,packed_column,packed_column,takePacked_ok,lanes_or] at pass
    by_cases hit : combField xs[q] (!u) ka kb op i j = BitVec.allOnes 768
    · apply fallback_sound
      apply marked_ok _ _ _ q hq _ pass
      rw [mark_at _ _ _ hq]
      exact beq_iff_eq.mpr hit
    · rw [eval,if_neg small,if_pos (bne_iff_ne.mpr hit)]

def batchPair (u : Bool) (b : Batch) (xs : List NodeContext) (i j op : Nat) :=
  let f := batchMove u b xs i j op
  f false false && f true false && f false true && f true true

def batchRow (u : Bool) (b : Batch) (xs : List NodeContext) (i : Nat) (js : List Nat) :=
    js.all (fun j => (opsOf u).all (batchPair u b xs i j))

def batchRows (u : Bool) (b : Batch) (xs : List NodeContext) : List Nat → Bool
  | [] => true
  | i::js => batchRow u b xs i js && batchRows u b xs js

theorem batchRows_at {u} (k n) (xs : List NodeContext) {q : Nat} (hq : q<xs.length)
    (budget : xs[q].1=k) (arity : xs[q].2.1=n) (mode : xs[q].2.2.2.1.2=u) (js : List Nat)
    (bounds : ∀ j ∈ js, j<n) (allRows : batchRows u (makeBatch k n xs) xs js=true) :
    testAll xs[q] (js.map (contextWire xs[q])) = true := by
  induction js with
  | nil => rfl
  | cons i js ih =>
    simp only [batchRows,Bool.and_eq_true,batchRow,List.all_eq_true] at allRows
    simp only [List.map_cons,testAll,testRow,Bool.and_eq_true,List.all_eq_true,List.mem_map]
    have hi := bounds i List.mem_cons_self
    refine ⟨?_,ih (fun j hj => bounds j (List.mem_cons_of_mem _ hj)) allRows.2⟩
    rintro _ ⟨j,hj,rfl⟩ op hop
    have hj' := bounds j (List.mem_cons_of_mem _ hj)
    rw [mode] at hop
    have pass := allRows.1 j hj op hop
    have check := @batchMove_at u k n xs i j op
    simp only [batchPair,Bool.and_eq_true] at pass
    simp only [testPair,Bool.and_eq_true]
    exact ⟨⟨⟨check hi hj' hq budget arity mode pass.1.1.1,check hi hj' hq budget arity mode pass.1.1.2⟩,
      check hi hj' hq budget arity mode pass.1.2⟩,check hi hj' hq budget arity mode pass.2⟩

def runBatch (u : Bool) (k n : Nat) (xs : List NodeContext) :=
    batchRows u (makeBatch k n xs) xs (List.range n)

theorem runBatch_at {u k n} {xs : List NodeContext} {q} (hq : q<xs.length)
    (hb : xs[q].1=k) (ha : xs[q].2.1=n) (hm : xs[q].2.2.2.1.2=u) (hn : xs[q].2.2.1.length=n)
    (pass : runBatch u k n xs=true) : testAll xs[q] xs[q].2.2.1=true := by
  have all := batchRows_at k n xs hq hb ha hm (List.range n) (fun _ => List.mem_range.mp) pass
  have eq : (List.range n).map (contextWire xs[q]) = xs[q].2.2.1 := by
    apply List.ext_getElem
    · simp [hn]
    · intro i h1 h2
      simp [contextWire,List.getD_eq_getElem?_getD,h2]
  rwa [eq] at all

def contextOf (g : Forest) (k i : Nat) : NodeContext :=
  let raw := wiresOf g
  let (num,depth,cw,iw,pw,offw,lw,data) := g.levels k
  let (ops,bank,ws) := readNode g k i
  let start := num*(10*storedDepth g depth+raw.length+depth)
  let pos := start+num*offw+packedAt data (start+i*offw) offw
  let nr := packedAt data pos 5
  let nl := packedAt data (pos+5) lw
  let st := pos+5+lw
  let rules := (getPairs data cw depth nr st).filterMap (fun (a,b) => buildRule g ops depth bank a b)
  let ls := fun tag => ((g.index k tag).bind (linkedSet g (k-1))).toList
  (k,ws.length,ws,preCov g.mode ws,rules,ls)

def prelim (T : Sig) (c : NodeContext) :=
  let ws := c.2.2.1.map Prod.fst
  decide ws.Nodup && !(ws.contains T)

theorem from_context (g : Forest) (k i : Nat) :
    nodeVerified g k i = (prelim (targetOf g) (contextOf g k i) &&
      (if k=0 then true else testAll (contextOf g k i) (contextOf g k i).2.2.1)) := rfl

theorem makeBlock {g k start n} (h : ∀ (i : Nat), start ≤ i → i < start + n → nodeVerified g k i = true) :
    block g k start n=true := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [block,Bool.and_eq_true]
    exact ⟨h _ (by omega) (by omega),ih (fun i le lt => h i le (by omega))⟩

def contexts (g : Forest) (k start n : Nat) :=
  ((List.range n).map (start+·)).map (contextOf g k)

def header (g : Forest) (k start n ar : Nat) :=
  (contexts g k start n).all (fun c => c.2.1==ar && prelim (targetOf g) c)

def rowCut (g : Forest) (k start n ar lo len : Nat) :=
  let xs := contexts g k start n
  let b := makeBatch k ar xs
  (List.range len).all (fun d =>
    let i := lo+d
    batchRow g.mode b xs i (List.range' (i+1) (ar-(i+1))))

theorem rowCut_at {g k start n ar lo len} (h : rowCut g k start n ar lo len=true)
    (i : Nat) (l : lo ≤ i) (r : i < lo+len) :
    batchRow g.mode (makeBatch k ar (contexts g k start n)) (contexts g k start n)
      i (List.range' (i+1) (ar-(i+1)))=true := by
  have ha := List.all_eq_true.mp h (i-lo) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le l] using ha

theorem rowCut_merge {g k start n ar lo a b}
    (h : rowCut g k start n ar lo a=true) (t : rowCut g k start n ar (lo+a) b=true) :
    rowCut g k start n ar lo (a+b)=true := by
  apply List.all_eq_true.mpr
  intro j hj
  have jlt := List.mem_range.mp hj
  by_cases first : j<a
  · exact rowCut_at h (lo+j) (by omega) (by omega)
  · exact rowCut_at t (lo+j) (by omega) (by omega)

theorem cutsRun {g k start n ar} (h : rowCut g k start n ar 0 ar=true) :
    runBatch g.mode k ar (contexts g k start n)=true := by
  let xs := contexts g k start n
  have go (lo num : Nat) (eq : lo+num=ar) :
      batchRows g.mode (makeBatch k ar xs) xs (List.range' lo num)=true := by
    induction num generalizing lo with
    | zero => rfl
    | succ num ih =>
      simp only [List.range'_succ,batchRows,Bool.and_eq_true]
      refine ⟨?_,ih (lo+1) (by omega)⟩
      have ok := rowCut_at h lo (by omega) (by omega)
      simpa only [show ar-(lo+1)=num by omega] using ok
  unfold runBatch
  rw [List.range_eq_range']
  exact go 0 ar (by omega)

theorem cutsBlock {g k start n ar} (hd : header g k start n ar=true)
    (h : rowCut g k start n ar 0 ar=true) : block g k start n=true := by
  apply makeBlock
  intro i lo hi
  let xs := contexts g k start n
  have hm : contextOf g k i ∈ xs := by
    apply List.mem_map.mpr
    exact ⟨i,List.mem_map.mpr ⟨i-start,List.mem_range.mpr (by omega),by omega⟩,rfl⟩
  obtain ⟨q,hq,e⟩ := List.getElem_of_mem hm
  have one := List.all_eq_true.mp hd _ hm
  simp only [Bool.and_eq_true,beq_iff_eq] at one
  have hb : xs[q].1=k := by rw [e]; rfl
  have ha : xs[q].2.1=ar := e ▸ one.1
  have hm : xs[q].2.2.2.1.2=g.mode := by rw [e]; rfl
  have hn : xs[q].2.2.1.length=ar := by rw [e]; exact one.1
  rw [from_context,Bool.and_eq_true]
  refine ⟨one.2,?_⟩
  split
  · rfl
  · exact e ▸ runBatch_at hq hb ha hm hn (cutsRun h)

def boxes (g : Forest) (k start n ar lo num : Nat) : Nat → Prop
  | 0 => rowCut g k start n ar lo num=true
  | d+1 => boxes g k start n ar lo (num/2) d ∧ boxes g k start n ar (lo+num/2) (num-num/2) d

theorem boxesCut {g k start n ar lo num d} (h : boxes g k start n ar lo num d) :
    rowCut g k start n ar lo num=true := by
  induction d generalizing lo num with
  | zero => exact h
  | succ d ih =>
    have v := rowCut_merge (ih h.1) (ih h.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self num 2)] using v

def cells (g : Forest) (k start n ar rows : Nat) : Nat → Prop
  | 0 => header g k start n ar=true ∧ boxes g k start n ar 0 ar rows
  | d+1 => cells g k start (n/2) ar rows d ∧ cells g k (start+n/2) (n-n/2) ar rows d

theorem cellsBlock {g k start n ar rows d} (h : cells g k start n ar rows d) :
    block g k start n=true := by
  induction d generalizing start n with
  | zero => exact cutsBlock h.1 (boxesCut h.2)
  | succ d ih =>
    have v := block_merge (ih h.1) (ih h.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self n 2)] using v

def listPieces {α} (f : α → Bool) (xs : List α) : Nat → Prop
  | 0 => xs.all f=true
  | d+1 => listPieces f (xs.take (xs.length/2)) d ∧ listPieces f (xs.drop (xs.length/2)) d

theorem listPieces_all {α f xs d} (h : @listPieces α f xs d) : xs.all f=true := by
  induction d generalizing xs with
  | zero => exact h
  | succ d ih =>
    have ap : ((xs.take (xs.length/2)) ++ (xs.drop (xs.length/2))).all f=true := by
      simp only [List.all_append,ih h.1,ih h.2,Bool.and_self]
    simpa only [List.take_append_drop] using ap

theorem cut_root {u} {m cap : Nat} {prior : Nat → Nat} {ws : List Sig}
    (low : ∀ q, Lower u (varsX q) (graphGoal q) (prior q)) (ci : ColumnInfo)
    (ok : colCheck m ci prior = true)
    (cut : (decide ws.Nodup && poolCut u (subcube ci.1 ci.2.1) ci.2.2.2.2 cap 0 (varsX (rawMask m ci)) ws)=true) :
    Impossible u (graphGoal m) cap ws.toFinset := by
  simp only [Bool.and_eq_true,decide_eq_true_eq] at cut
  exact poolCut_sound (col_sound ci prior low ok) [] rfl cut.1 cut.2

theorem index_root {u} {g : Forest} {m cap i : Nat} {prior : Nat → Nat} {ws : List Sig}
    (hm : g.mask=m) (hu : g.mode=u) (low : ∀ q, Lower u (varsX q) (graphGoal q) (prior q))
    (geom : graphValid g prior = true) (blocks : checkedTables g cap)
    (idx : indexedRoot g cap i ws = true) : Impossible u (graphGoal m) cap ws.toFinset := by
  subst hm
  subst hu
  exact root_index low geom blocks (Nat.le_refl _) idx

def essOK (m hints : Nat) : Bool :=
  let xs := graphPairs m hints
  properB (graphGoal m) && checkEssential (graphGoal m) (vars m) xs && (xs.map Prod.fst == vars m)

theorem plain_low {u} {m hints cap : Nat} (ok : essOK m hints = true)
    (a : Impossible u (graphGoal m) cap (vars m).toFinset) : Lower u (vars m) (graphGoal m) (cap+1) := by
  simp only [essOK,Bool.and_eq_true,beq_iff_eq] at ok
  apply lower_impossible (proper_of _ ok.1.1) (essential_plain ok.1.2).1 (essential_plain ok.1.2).2 _ a
  intro v hv
  apply essential_ok ok.1.2 v
  rw [ok.2]
  exact List.mem_toFinset.mpr hv

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low3 : Lower true (vars 3) (graphGoal 3) 1 := size_of (hints:=1) (by decide +kernel)

def known3 := extendKnown [] 1 [(12,[49,32])]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid3 : Known true known3 := extendKnown_ok (m:=3) baseKnown low3 (by decide +kernel)

def g15d3 (i : Nat) : Nat := 0xf

def g15l3 : Packing := (1,0,1,0,0,0,0,g15d3)

def g15samples : Array (Bits × Bits) := #[(0xefe47cfaf79fcbe2267eff82033cfbeeb8ffe977f4f9cbdc18acec7fcf75aafdffdd73ef57ceff77f9f3c69fef3aba8bc60e65baef3608e7d155c295bd604db07a7fa33ff1da267d7faf155d5d3b284e7df8b57ed3ebf3d93ee7ca6f3c47473,0x362118ac45916a9d02222292091025e029311c08210147faa44c85bd94a89bfc029b3023630ad4268a551db8a04260300e6a101419c00907c94709580b244a221a32941f500020046b12be00c1022a20825c0800009d60c00c99dd6a5373652),(0xffdbfbffffb9fdacebfbfeffffbeb7fe5f7deee77ebffa7f9e57ed236c3ffedbeffff77ef65d33fcefdd1fffeb7fff7f9f0b7b4fa1eb7f7af7af7ef7f24f35ffde5d99797b9da1feda7bbde3c25aff4577f6cf7ff5776f3fd8da5daee9e97a7f,0xb890ec001102e9102c414c828844b900b84480200501228000a315802011224005c008494008000891022c00455200746b0910ee24210209030803400504ba0448100480000e41fb200a000f21a4085cb0980651e39620d1311200091888c829),(0xf7a5fe75d0eef75bdffe135fffeffac3fdff157aebf8ffcfffff7fffbfddf5f5bcc6fef31fa7ff9f977fffb6d5ac56d767ff9ffd5f1ddff7aafbffdfbff9fb64fffbfffe9eeedf9d7dbddebebfbfcdfbfeebfdff1fedf3e36f77f77b7eff8f9c,0x420000b6080008b10028125029302384439010200b840088c404824cda644328204061021844047682141908a00ea09801484018106f04240c45011988244d2800428011180860403800a600e11040302050082006844200000970041221714),(0x1034b7f7c54637fbbf9df36abcd7cdafbbbe77dff94045836dfe73fcdff3e726dd347ddfebbeffeb77f2f673bcadb4916efed7fcdf5eefcd8d5693fdeff6effafff6eedfefe3df1d759cc23cbfff64ffcb1d7ba06fbafdcb776db2d977d68de0,0xe98f99f410317a046ed922cabd2095808b842221ec47b15242be0242124188c855bab1620a23b88080900c22107e15922841688c74e9059c8c39a8864264210d3af003ea604c79f0246b0405b026fb8ca8c2dd69b1031955e4f520d92e1de8e0),(0,0),(0,0),(0,0),(0,0),(0,0)]

def g15columns : List ColumnInfo := []

def g15autos : List (List Nat) := [[],[48,33]]

def g15levels : Nat → Packing
  | 3 => g15l3
  | _ => emptyPacking

def g15index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none

def g15 : Forest := ⟨15,3,fun j => g15samples[j]?.getD (0,0),g15columns,g15autos,g15levels,g15index⟩

set_option maxHeartbeats 0 in
theorem geomg15 : graphValid g15 (boundsBefore known3) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel

namespace Brief
abbrev Piece := Nat × Nat × Nat × Nat

def total : List Piece → Nat
  | [] => 0
  | p::ps => p.1+total ps

def covered (g : Forest) (k start : Nat) : List Piece → Prop
  | [] => True
  | (n,a,r,d)::ps => cells g k start n a r d ∧ covered g k (start+n) ps

theorem covered_ok {g k s ps} (h : covered g k s ps) : block g k s (total ps)=true := by
  induction ps generalizing s with
  | nil => rfl
  | cons p ps ih =>
    obtain ⟨n,a,r,d⟩ := p
    exact block_merge (cellsBlock h.1) (ih h.2)

def scheduled (g : Forest) (k : Nat) : List (List Piece) → Prop
  | [] => True
  | ps::rest => (g.levels k).1=total ps ∧ covered g k 0 ps ∧ scheduled g (k+1) rest

theorem scheduled_at {g k s ps} (h : scheduled g s ps) (lo : s≤k) (hi : k<s+ps.length) :
    block g k 0 (g.levels k).1=true := by
  induction ps generalizing s with
  | nil => simp only [List.length_nil,Nat.add_zero] at hi; omega
  | cons q ps ih =>
    by_cases eq : k=s
    · subst k
      rw [h.1]
      exact covered_ok h.2.1
    · simp only [List.length_cons] at hi
      exact ih h.2.2 (by omega) (by omega)

theorem schedule_ok {g t} (ps : List (List Piece)) (len : ps.length=t+1) (h : scheduled g 0 ps) :
    checkedTables g t := by
  intro k hk
  exact scheduled_at h (Nat.zero_le _) (by omega)
end Brief

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tablesg15 : checkedTables g15 3 := by
  apply Brief.schedule_ok [[],[],[],[(1,4,0,0)]] rfl
  simp only [Brief.scheduled,Brief.covered,Brief.total,cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals first | exact True.intro | decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low15 : Lower true (vars 15) (graphGoal 15) 4 := plain_low (hints:=8449) (by decide +kernel) (index_root (g:=g15) (i:=0) rfl rfl (before_sound known3 valid3) geomg15 tablesg15 (by decide +kernel))

def known15 := extendKnown known3 4 [(15,[]),(23,[64,48,32,16]),(27,[66,16]),(29,[50,65]),(30,[50,33,16,64]),(39,[80,64,48,32,16]),(57,[32,82,64,16]),(78,[96,80,64]),(83,[99,83,64,32,16]),(99,[48,96,83,64,32,16]),(135,[115,99,83,67]),(156,[112,96,48,50,33,81,64]),(163,[115,50,98,83,66,16]),(165,[114,33,97,82,50,65]),(166,[114,98,83,33,16,64]),(172,[114,50,99,48,33,81,64]),(177,[115,99,82,64,16]),(198,[115,96,83,64]),(270,[131,115,99,83,50,33,16,64]),(281,[131,115,99,50,82,65]),(291,[131,115,50,98,83,66,16]),(300,[130,114,98,49,32,81,64]),(305,[131,115,99,82,64,16]),(312,[130,114,49,98,81,64]),(323,[131,115,98,83,66]),(326,[131,115,98,83,32,64]),(330,[130,114,97,82,16,64]),(332,[130,50,115,98,49,32,81,64]),(344,[130,50,115,49,98,81,64]),(353,[130,33,113,99,82,65]),(354,[130,33,50,113,99,82,16,64]),(396,[48,128,115,96,50,33,81,64]),(420,[131,33,114,99,32,81,64]),(424,[129,33,115,48,98,81,64]),(480,[32,50,128,115,98,81,64])]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid15 : Known true known15 := extendKnown_ok (m:=15) valid3 low15 (by decide +kernel)

def g31d6 (i : Nat) : Nat := 0x11a20bf

def g31l6 : Packing := (1,0,3,0,0,0,0,g31d6)

def g31h6 (i : Nat) : Nat := 0x30be670208000065000016357504004755c084

def g31d5 (i : Nat) : Nat := 0x40828fd20fd10

def g31l5 : Packing := (2,1,3,0,0,3,0,g31d5)

def g31h5 (i : Nat) : Nat := 0x300

def g31d4 (i : Nat) : Nat := 0x5dd4520

def g31l4 : Packing := (1,2,3,0,0,0,0,g31d4)

def g31samples : Array (Bits × Bits) := #[(0x4cd435b1cff89bfcf3403d6ffb5e7b6fb6f0a252750d8f3e775f7a4b35bf17ffc1f1f68f49aff3f97ef5dcbffcecfb8b347fdad1b97ee9eab1fef35bbda93bdefe31d48e2e2a2deece0b774332650ab9592b7ca4c3cce37238ad15d16630b273,0x6412e45418036809b01888acb04128982824834415c30405900032d41009c80d02002180b020200430601201640641a1dc0065180e101002a04090026300c7840041c50020480001612a04d9391609200802d008345020001011525c6a12412),(0x73bc6673e6f7fb127e7edfbb35afbc3c7aeffeffb7b36ea15203b3fb0b23d71ae7293cfd7c6b76afff7f9f42ce524641ef74bc7775f5b7beeca9fab64d8d2f057df75fd7b06effadf147566865d776d67ddf9c9eb9cb59bcc3fa90c286464e7f,0x4806818a3a130032401c024400212c065450b14218830380207b40c01250613908c5d427709991c028a8485ce128038122240884600438f10480e460400470023480c0a07020209088601130006682403032d0b168a010b80406c2d009524869),(0xeffcdbd0ce5fec73cdbefbd7def1b1c3790e5bae99dff1cd23a5cdbe62c5eb058a465b7eeb5addf6c9bef153e11a35ff6fd5cffe7bafe6b6139b5cefe3db14c795e58371dbcbcdf57fd9ef3c55f2f3464a77dfd974753609f3f58c06d986cd9c,0x4b01000c04008000621253b644c50e809a00699020cd8131084993ead068806811a01c884244431950203000a8190020900540a0b5a4408737901010110004480543053884a8000640226cc4c080818cecc0800000c61443029290662058794),(0xfefbbd6efc554e65d6d32e9e9fc8c5f7fb2bc7bd6e78ffd4c9b6fe5fece47b85feefcd40df76eb99e3fb3fd3cb117c3cbbc927b8bed59f45ff184d509bdff7bf9d8ffb224ff7161ad1bfbf9e9d09ef7ea6dcdb5fcfb76f877dce7e6c59e90980,0x58028e420d9b06420152488082b0860302440920c440010ca45200404030002150200002090a92880845042a20140600940201002080830504028c00a6850d1a3023ca2055a006690040d9028207c2821022259824200c0a8056166995b04820),(0xb18f7a8e312b6eee7925dbddcc1fee96cd7fc4dd4f7ddebefdfa8c25bff986e3b4d8e33b16acabff13c446edb2bdfdc6fb8ffc188e9ad9615cc76daf377cf7ff5a7faa5f85f437c63e34eadbee7b7fedacedbfe7afdacfc62f3febbb2079b000,0xa03c4000a02001010084164514412920290832083a8244020024b0009ac3600405989c25c0540d2310a0a051892311c50039502e45183000409152a0594030840798200c00182012602d04806c600d6c895912670092f1752200e892284e92c0),(0,0),(0,0),(0,0),(0,0)]

def g31columns : List ColumnInfo := [(1,0,30,0,4),(16,0,15,0,4),(8,0,23,0,4),(4,0,27,0,4),(2,0,29,0,4)]

def g31autos : List (List Nat) := [[],[65,50],[16,66],[16,32,48,64],[32,67],[32,49,64,16],[48,33],[48,65,32,33],[64,16,33,50],[64,49]]

def g31levels : Nat → Packing
  | 6 => g31l6
  | 5 => g31l5
  | 4 => g31l4
  | _ => emptyPacking

def g31index : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 5 15 3 9 1 4 g31h6
  | 5 => lookupWord 1 3 1 9 1 4 g31h5
  | _ => fun _ => none

def g31 : Forest := ⟨31,6,fun j => g31samples[j]?.getD (0,0),g31columns,g31autos,g31levels,g31index⟩

set_option maxHeartbeats 0 in
theorem geomg31 : graphValid g31 (boundsBefore known15) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=1) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tablesg31 : checkedTables g31 6 := by
  apply Brief.schedule_ok [[],[],[],[],[(1,5,0,0)],[(2,6,0,0)],[(1,5,0,0)]] rfl
  simp only [Brief.scheduled,Brief.covered,Brief.total,cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals first | exact True.intro | decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low31 : Lower true (vars 31) (graphGoal 31) 7 := plain_low (hints:=8449) (by decide +kernel) (index_root (g:=g31) (i:=0) rfl rfl (before_sound known15 valid15) geomg31 tablesg31 (by decide +kernel))

def known31 := extendKnown known15 7 [(31,[]),(167,[115,67,100,83]),(313,[131,115,65,50,98,81]),(334,[131,115,100,50,33,16,80]),(355,[131,50,66,116,99,82]),(428,[130,50,116,49,32,97,80])]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid31 : Known true known31 := extendKnown_ok (m:=31) valid15 low31 (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low47 : Lower true (vars 47) (graphGoal 47) 5 := plain_low (hints:=8449) (by decide +kernel) (cut_root (prior:=boundsBefore known31) (before_sound known31 valid31) (8,0,39,0,4) (by decide +kernel) (by decide +kernel))

def known47 := extendKnown known31 5 [(47,[]),(61,[50,65]),(94,[101,50,33,16,64]),(157,[117,101,33,32,65,48]),(173,[113,97,82,32,65,48]),(181,[114,81,98,50,65]),(188,[114,83,48,33,97,64])]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid47 : Known true known47 := extendKnown_ok (m:=47) valid31 low47 (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low55 : Lower true (vars 55) (graphGoal 55) 5 := plain_low (hints:=257) (by decide +kernel) (cut_root (prior:=boundsBefore known47) (before_sound known47 valid47) (16,0,39,0,4) (by decide +kernel) (by decide +kernel))

def known55 := extendKnown known47 5 [(55,[]),(79,[101,50,33,16,64]),(376,[128,80,84,66,16,114,97,48])]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid55 : Known true known55 := extendKnown_ok (m:=55) valid47 low55 (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low63 : Lower true (vars 63) (graphGoal 63) 8 := plain_low (hints:=8449) (by decide +kernel) (cut_root (prior:=boundsBefore known55) (before_sound known55 valid55) (32,0,31,0,7) (by decide +kernel) (by decide +kernel))

def known63 := extendKnown known55 8 [(95,[101,66,16]),(159,[117,101,67,32]),(231,[83,82,114,99,66,16]),(335,[131,115,100,50,33,16,80]),(350,[132,116,84,48,33,96]),(359,[131,67,116,99,82,16]),(377,[128,81,67,112,97,32]),(462,[83,133,115,67,32,96]),(483,[83,80,132,115,96,32,16])]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid63 : Known true known63 := extendKnown_ok (m:=63) valid55 low63 (by decide +kernel)

def g111d6 (i : Nat) : Nat := 0x7213f

def g111l6 : Packing := (1,0,2,0,0,0,0,g111d6)

def g111h6 (i : Nat) : Nat := 0x8000

def g111d5 (i : Nat) : Nat := 0x17e51

def g111l5 : Packing := (1,1,2,0,0,0,0,g111d5)

def g111samples : Array (Bits × Bits) := #[(0x9da83de5fe85dcb1fb131acda7cb7fa6fdfff53ffdd1e39f470edae98ffa779fed3d49cfd7ff65f391fe43c4c2da557b3d0f9d8be4df9a25abffffe06fcbe9b6b53bd9766e67796e1eeaf292d828fb3adaf06cf9f65f62d506dc8c692839f653,0x99520888bc441a08808188400f9006aa38027780804108a42161480404a0859200848c260034430011281a00001040102808090028e048448151413038494402ef0282859485e014128040a031e08189c0242002180cb0f04d190d4828112652),(0x6f53eedf3e34f5ed54d6bf7e1fff0f7d43ff9f667beb1928ff77d9f5ed55ffb67fdcbbddf3e7bdfffefaea5d6eb4a6e7e6a7cf77d8cd6f9e6efafc7fdfdeb6fdcfbf3ddb8fe9ff16e7f6fde5b7df4e2b3f7ab38deae871aa3b7e53917e26487f,0x481021100a000100108101780404041002808480c08a0020002124a0342680014000000844000232a0144083100240441210022000b043800080a8100060894002450004058086320280100000c0800154100100300000a02a6201004224829),(0x74d5ebbdd9eb9a5fb6bd77dfeba4bccb17df28cb12ed7fee19f56f97fa519e4bf2d75c34e8c49b0766e7bdbaf577997b977e76cf6b3ecf79f39a2c5e50376d1f6d65bbd375353bfb16bf97bf67b9f1c7fb85b75ebbe5dd44c503731eb1c38f9c,0xb12000680454a1c0c087a9606d1536a406041301012650455d3020a52438021a8344900a60298a04c004231000f110120a802b50ac0008815607500a1111106904088181288361005301861081a1a010a20cc180541841449d09c60531818514),(0x1dd56f6145df333f162dd2d77f55f59b1cd7a7e5040f75cd4be0664bd92ebe4d0eb327fbca83265c648d75abbbad8eb391fb79d777e660573e7923c237a7079d28f5bf281f3d5dfdb599030bc8722dc56dad83fbabc5bed8c223200ec1fc0fc0,0x40dab5921b2b1c0c3c004217906840189039604c20d18490028e874801c42925001345400102344b015084adb40e8244603e402703f8f54a880000d1a2864a0608a71c78072494aea88479a4385c166604622654280736bb62f6391ac07c0ac0),(0,0),(0xf12e51fe9df15d5afdd0233cf761e695b8e9777faf7ce3fb672f367982ef85f5e529cf3eeeb847a76de6ddb3265a731cacb7a2abf493f3688135a3826951fc8a3ee7cdaeef723df5ec7cad13a8e4df56a8264f25fdbbc71d0482cce001fff020,0x62d3466409165346f5872bf3026700142488812448c6140860a0029fa5d70408079439078c0388e844721ae876284270536d4f51410100a66a4a8c20326809d10003048687a0b014d0c2b1cc8080210140282d542c00f0fb0c6f2b181eed020),(0xf7c326c3fabb7b0765ec93ba313dac9b402a6356d93b6b34b7389b77043e973c1898ab9d236f96cd5df8f8cd0cb436c774f0b8fedc8023ff072ee8d5e4afb6700fccc6798ab99e23e7c6a9e292ee6cbdcefb92e6f289f7fe3c2000ee7f040020,0x9064ad20c50183c09a1704001d148a08a19293a273a447c8f1ac0da09c0d828d8ad36b8968a6a59c05121bd78a4a9808b68cdd91a9f0e843e4317020e8a87202230b20b0a70636001ec20c820b6063c8421e718af411cff5fd599feffb040000),(0,0),(0,0)]

def g111columns : List ColumnInfo := [(1,32,78,0,4),(12,0,99,0,4),(96,0,15,0,4),(0,8,99,4,5)]

def g111autos : List (List Nat) := [[],[32,83]]

def g111levels : Nat → Packing
  | 6 => g111l6
  | 5 => g111l5
  | _ => emptyPacking

def g111index : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 3 1 6 1 1 g111h6
  | _ => fun _ => none

def g111 : Forest := ⟨111,6,fun j => g111samples[j]?.getD (0,0),g111columns,g111autos,g111levels,g111index⟩

set_option maxHeartbeats 0 in
theorem geomg111 : graphValid g111 (boundsBefore known63) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tablesg111 : checkedTables g111 6 := by
  apply Brief.schedule_ok [[],[],[],[],[],[(1,6,0,0)],[(1,6,0,0)]] rfl
  simp only [Brief.scheduled,Brief.covered,Brief.total,cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals first | exact True.intro | decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low111 : Lower true (vars 111) (graphGoal 111) 7 := plain_low (hints:=16785665) (by decide +kernel) (index_root (g:=g111) (i:=0) rfl rfl (before_sound known63 valid63) geomg111 tablesg111 (by decide +kernel))

def known111 := extendKnown known63 7 [(111,[]),(123,[101,66,16]),(187,[117,80,66,96,16]),(190,[114,83,48,33,97,64]),(215,[115,83,67]),(222,[101,117,50,33,16,64]),(238,[83,114,99,33,16,64]),(243,[82,98,115,66,16]),(311,[131,115,99,67,82,16]),(318,[128,112,96,49,64]),(343,[131,115,83,67,98]),(349,[128,80,117,32,16,98,65,48]),(365,[129,113,82,65,48]),(378,[129,33,97,81,16,114,49,64]),(413,[134,117,33,32,65,48]),(427,[98,134,114,66,81]),(437,[134,81,114,50,65]),(455,[83,133,115,67,32,96]),(476,[82,50,133,98,49,32,113,64]),(485,[80,81,129,114,50,65,96]),(490,[81,33,80,128,97,114,49,64]),(497,[98,99,81,131,114,65]),(504,[49,50,83,48,130,113,64])]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid111 : Known true known111 := extendKnown_ok (m:=111) valid63 low111 (by decide +kernel)

def g189d7 (i : Nat) : Nat := 0x163441bf

def g189l7 : Packing := (1,0,3,0,0,0,0,g189d7)

def g189h7 (i : Nat) : Nat := 0x42f9f28c08140000000020f801630c00d0

def g189d6 (i : Nat) : Nat := 0x420a3fa41fd10

def g189l6 : Packing := (2,1,3,0,0,3,0,g189d6)

def g189h6 (i : Nat) : Nat := 0x18000

def g189d5 (i : Nat) : Nat := 0xb7d8d20

def g189l5 : Packing := (1,2,3,0,0,0,0,g189d5)

def g189samples : Array (Bits × Bits) := #[(0xb1dc1ff7132a7ff6e7954acdad6bfbbb4172275f57d485efe917eeb71c7ff77e0f2710edeec09b154b6e1e5d7bf54df3f4dd5c7dd4938defdfccf59eee87375ef5552cb6bdff87f9e5f8848f37877351ffebb95fb54e1da64108012bd832f47c,0x68087423000a3a003112a000082c31440020146209e00a2443b08826a2c783c22a2018806d009402af4218903314000c10804096c64039005c40804a8011202bd030a10649200641113e224050005040170804503a1d85960021199906a42c),(0,0),(0xeb6f6506f1e2aa6dee226de156ddffe904e57beead59704513e2e966ffdb64a3f7b8db55bb1f1a9e751d7de33b4c6bc392f42ec374ecbbaf3654c836729be4baa8a1b0743f347b7afe536de5ff5b19289bf0a963347bac458a9750042f2dc84f,0x8c001201c00cc1400602117d41024270201114400481224201e24010180010022d208a08699a408210701c624230158998b14904166522504000040900a44c6294a080304188c2f28062010c468083210010d400081004c61e4544061425c84a),(0xf66bc486edbf6752992cfed2569e9459bf37bdf6868a4b581370516e15408dc4ead6b1da975dc462fef725ca8dda991ebd300aea78456370ee844f979859bc9f5deafd42e2387048ee48d79c7ef3f0ec585564e64ffb9958e417a60021ce0f8f,0x141086c23420024210c2e0290d88c82820ac202680cd018140488056065c915925900519600091c4b00c089b40a0022400aa272c09048ab84edc29000421199610c4d05046325013709168300783810a1650947c0cd1909e00a3a18e18a0685),(0x1be0dbb4733b3fdea539db5dc1e40d61ba397321deabaa5c9e79b42d6566bd396bf515996fe7f57983f51a71a1c9badeffcf76fe239904dffc789ed507f54ab9755fcbae7d5aee82615d191ef4348fdd8cad469fbbb1e7780400a62f50f10f70,0xf886400208099000c642c1096206000038a409a0950205800a30027081080008088082862810e023841034204100e14580a5518500089440510000452509ea42100302125980d25800a64140368043861e0852880700e27201f4c42600710950),(0x759515f9d7ee0bf78df1fe7ad5afa9eeb6e9dbe6bad8fb76e9e7bd41f896f6f2536247ecf382b95e96bd25e7fbf1effa33ed91b9f56ce6009f37fe8fd2fbfefc6ee8f4dccf1e8bf40aea3c197b6fe1aee129e4ecf84d2c2796909d080fbf080,0xe680c60358033181540c800939169140001cc0400dc000a449800201185038442c4008c00182424219509c4046080205b1a3722e08011b4068200a0191200c0590000b4630001261b08c0188068aa2ac082052898240c042684f5e8240f95000),(0,0),(0xfc3e2eb86c64e5fbbe7379bb3583650f2e89c5febf79f8f98fbf1cf7eff53fb3dbe9ffcbe6ffec89ecb8cf31f5e3fad6ef7bf308cfabf802587fcdf187b949b9272cda3b78452b96bae7ffe5cf4ddef209ee4bcee6cdfb3dbae059d52e010080,0x110000ac26800e3ea1d16e0284202c86df220182b02850109605b58242288018d2926115124094018005428c88860010424c8080e09a042f000c31240a4b3300091d04818606250c00111e2329000402254b002641093b3981b0a179ab000080),(0,0)]

def g189columns : List ColumnInfo := [(160,0,29,0,4),(24,0,165,0,4),(132,0,57,0,4),(33,0,156,0,4),(17,0,172,0,4),(12,0,177,0,4)]

def g189autos : List (List Nat) := [[],[115,84],[32,67,117],[32,83,116],[48,82],[48,82,112,66],[64,114,50,48,80],[64,114,83],[80,50,116],[80,50,66,32,114],[112,66,48,82],[112,66]]

def g189levels : Nat → Packing
  | 7 => g189l7
  | 6 => g189l6
  | 5 => g189l5
  | _ => emptyPacking

def g189index : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 9 13 2 9 1 4 g189h7
  | 6 => lookupWord 1 3 1 9 1 4 g189h6
  | _ => fun _ => none

def g189 : Forest := ⟨189,7,fun j => g189samples[j]?.getD (0,0),g189columns,g189autos,g189levels,g189index⟩

set_option maxHeartbeats 0 in
theorem geomg189 : graphValid g189 (boundsBefore known111) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=1) ?_⟩,listPieces_all (d:=2) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tablesg189 : checkedTables g189 7 := by
  apply Brief.schedule_ok [[],[],[],[],[],[(1,6,0,0)],[(2,7,0,0)],[(1,6,0,0)]] rfl
  simp only [Brief.scheduled,Brief.covered,Brief.total,cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals first | exact True.intro | decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low189 : Lower true (vars 189) (graphGoal 189) 8 := plain_low (hints:=536879876) (by decide +kernel) (index_root (g:=g189) (i:=0) rfl rfl (before_sound known111 valid111) geomg189 tablesg189 (by decide +kernel))

def known189 := extendKnown known111 8 [(189,[]),(303,[135,50,65]),(347,[130,50,98,82,115,33,65]),(486,[115,83,82,130,99,66,16])]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid189 : Known true known189 := extendKnown_ok (m:=189) valid111 low189 (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low127 : Lower true (vars 127) (graphGoal 127) 9 := plain_low (hints:=16785665) (by decide +kernel) (cut_root (prior:=boundsBefore known189) (before_sound known189 valid189) (32,0,95,0,8) (by decide +kernel) (by decide +kernel))

def known127 := extendKnown known189 9 [(127,[]),(223,[117,67,32]),(239,[116,83,32]),(478,[99,132,84,48,33,112]),(508,[48,84,100,49,129,112])]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid127 : Known true known127 := extendKnown_ok (m:=127) valid189 low127 (by decide +kernel)

def g191d10 (i : Nat) : Nat := 0x8201ff

def g191l10 : Packing := (1,0,5,0,0,0,0,g191d10)

def g191h10 (i : Nat) : Nat := 0x99090000b500000001a152f05d5c000e4006080015749fa60141c73802b0a68137976081bca199eaaa3d961388c0f3a0002328c00084a05000089c2a

def g191d9 (i : Nat) : Nat := 0x288616180c48a1166c008c818588a2e004e68c2c214019ce18588b2410102944c300431c508936018138408051218b0c0328614b0a030139610c0803944862a8614888704038c28424018278d600745a25b53e43cce27c5e0bc00ff483fe30ff4c3fd10ff54ffe10ff903fe20ff4c7fc20ff58ffd40

def g191l9 : Packing := (12,1,5,0,0,10,0,g191d9)

def g191h9 (i : Nat) : Nat := 0x140000000000000198cb0000a04e08a520001a51c20000531e80b64388d00078963d80a7524800343b41a670800007a7cc632d75239502d607286400000000060840000002a100028a67e35dbbd50001a6c315cd7a0d113ac27000121800052568158594ec000682af90000f6880000010b6fab800321ac31374a97c0018068243a2b09f06ef8c8000c984c7fad8000732e29d36fd3c9ba4660000003c50a43a2e72f0000037c5c484413000060966343d567081fd24000161fd8fb857db1616c2d70bc0001da504981c000a8cb68709baa54393350153817e93b2ee08a0b35c971e4812648c40cf0c890074a5b901b85c19b060f0f30f9c6d46f822909e468ae58b600010460007b00142a8dc0d2c800031c60005ad28d4a60000000000000046100000000000000005978000750c07fc419a5a33000612dc38451b04000033fe570000002d76000244c429f180a5d34b0ba1360001a731afd48a565b2f860060014b1d8111aaaac600056d800000000026c2da68678cd5b803ae00010d91906c6000000173ec82c4200058c80000000001b509c9847ce37e90001c466a9e954000000c99484d7ca82a800f93447182024f80000c48dc000596030083ad05a1c75006c10817410814060062c35820051841c00801071c96460c20000020c70c01c908b0c0000080000041016

def g191d8 (i : Nat) : Nat := (if i<1 then 0x50b30a062068860c1071620828188001141c88038918b140c61c40b1a0821c49040b10a18885a12900e2468610b144063043858908b143122d10c2a20e20596046182c82c608322160c8246088071094438590503146400c68a00c1a1022c6305831c01630640389281160c82460840710c140c6090090e404803892100e1864038618c162401c48c60b160180d111103182838b1239014302141c48b3a5181c5091708320507124c195160c316314389160c90448d187120c6110890e34514481802c80858c1c1041c48b281142c624708082122c8246892c61458c2b0610e2c48e44a0c1c5a2065c02c60d3011630900487244022858c10714310040020e2cc1c4884930e0c81c48b280ca8848b18a062002438c50b10c1620e2470c62616044871e70a1c08a2250e2c5421260c1d08b262102c626102022859800f12308301250228a0048b18c1621898487020210b4051306022161ce1858a1930e0c61c00d160ca0458a1c1121c1920890e0c8083a1122ca0500b0624a0a007244181c482424459c607122c82c087120cb00007164140c48060a1240e251001628c306c54c090413820f044901871630c3c38c2458d8309030a1a24597160142c9badb87b53b11aebaa9a75a41a0d9cb9a59559218df8b989385f82b7db79977373170b6e56a367d6496155e15ad5795535114eb4c549144f40d3d93a537f34b3252e32691fd1831330e30a106d02afdaf98f64f14ee0ebae78e52e2cd96d46d12cd0c8ec5ac26bc8ba2b60b10adcab6a82a5ca36a029969548f68b48808227e079075c7366bc65061c5e85985645224e04904403fe3923503002be2982561f818c14a1160d4092042001ff54930ffaa0a07fd71483feb1c21ff50120ffcc5207fd52503fe98221ff58e20ffac0987fd1058ffeb9a41ff58640ffa60907fd72443fe882a7ff50910ffee2907fd2058ffe98c41ff54131ffa20907fd21903feb1281ff48153ffa42a07fe72443fe90c41ffdcd20ffa65087fd32883feb0c61ff8ca10ffa43187fd2158ffeb9a21ff54931ffac098ffd62903feb1461ff58931ffac0a07fd204c7fa38a417f5c520bfae5107f920842ffb9281fddc520ff221105fd75902feb88417fdd110fba60b1fdd324c6feb94617f5ce10bfee0a9dfd7054efebac61fdc8610bfee2907f910482ffb9263fd48531bfee2b1fbf744c2ffbb2617f5c163bfaed185ff71502ffb92217f5c553bfae9105fd76902feb9c417f5cc20bfee2a9dff704c7dea14817f5ca10ff260905ff7258fee982637fdd531fea63087dd3054efeb92637f5c131bfae2b1dff724c2ffbb2817fdcd10ff261105fd718c2feb8c817fdcd20bfeeaa05ff7058efeb9a41fe48230bfae3107dd3258efeba4217fdd530bfee2987f5514c6feb94817f5c963bfeec98df771482eeb9c416fdd130 else 0x10410e24)

def g191l8 : Packing := (113,2,5,0,0,12,0,g191d8)

def g191h8 (i : Nat) : Nat := 0x38d5055793c3679268754bc6188000001bef920589c626a6500070140c8d5de5f1d7a21d0344d98ee800183ee488000001119701a189f7ac18d073c41c5a460f2f6dbb0d3e90a06b82f5bcc02928e3aa852e880000109c34616429775d57a00841de8968c753cd4f7779436ba625de899899071c11166c07285d4158b1c40cba3819701ff1ed4e0000001d75e386545f25c03c4e3ccfe7905e2217770000000a100005011f8991186d800000144100008f313025a433c0cd88dae660be94000121c0000002c88000000655b0af52342fd8c3fbe11d039049a5a1e7325180004d4e9a308f4f4000000ef1802b07e014cea170acb800000009b4c4008e61bc79a059a0f70fccb137f85b2554dc0000000f21e93d1260001258003490000000000283ab340000000b1c0000000003185023a5319608aa0001913478000000000000000046621400000000000005b0dc8e000000426e6c726f99d415a6c3045000127023e070c8d80b889403631ef964fdd2196b35879ca860c0656093c9b66e604e1a08c20003c8494d7228964094caf59a8139a149ac000c151050440002c01002420821110471482078810951470800420470000020001001c02830c50400010400800405400402040000c00080070800c100000d0040151000c0040141188000004000

def g191d7 (i : Nat) : Nat := 0x23042421610002c21610208008384100000005848830400208084004181081508808200a81105842c340108081882c400010401610060400004128800006508824200028421410000c0162410800007085060424a100000220d0042c200002c20410018408210b0d0840000384082c412109080006109020848e84200508408200000000601881c2121000008bf14a22c388670ba10c1480f009fabe87c6f79ecbd479ef09d6ba8736e39c4b7c6ded69a6b48666c998cb0c5febe972ae05b6b3964abc56eaa952aa0536a1940a7c4ee9892aa504969191ca2c44e8890ea083f67d8f89ec3be748e29b83666b8d49a432e628be9782e65b8b095429e5089e9302464588890c20e3e8728d8196318608bc15e248428800f61b83085c0ae148268480860b81081401e02802800df4815ca209fd879c9109fd82dc163df5215c620aff8654931ff38148230fe92054930df7715c5209fd82dd530b7f8558140bf7815c520bbf844c1209ff815c163df771501209ff815c1539fd81dc163fe92048630df920dc530ff210dc5209fd825c640f755154131bf78148131df7815ca10df7815ca40ddf714c163bf7815cd209fd8798a409ff815ca20fd5514c131df97244220bf9809c910dbf74549309ff805c5639fd81dd930ded20dc963cfd764c620df4815ca40bf9808ca10b7f85581319fd82dc530df9205c630ff210481319fd80dc5539fd81dd530bbd849c910bf58158e109ff805c963aff8654940ddf714c963df7715cd209fd80dd9319fd82dc563df551dc131ddd215ce20df7714c120fe92050910df5315ca10df783dc5209fd825c630ded52dc931dbd425d640df610dd9319ff815cd20bf78148163df5515c1319fd82dc540ddf764c1319fd878ca109fd81dcd209fd80dc5639ff815ca40dbd54dc940ff110dc520dbf7458130ded215ca30df5615d210bbf844c110ff081482309fd82dd1109fd82dd540df471dcd20df77144120bbf845cd20dbd425c640bf7814ca10ff3714c120bdf8350910bf78148153df7215d210bf78158131fe52048531bf78154131ded7248640cfd764ca209ff815c963bbf845cd10df583dc520edd6358130df4715cd20df771dcd20ddf714c153ff0714c120fd5314ca109f7815c5209f7815cd209bf845c1539ef825c5639bf845c1639bf845ce10fe120c861097f855da408fd86dd5319bf845cd209bf845c1319f7815ca409f581dc163

def g191l7 : Packing := (116,3,5,0,0,11,0,g191d7)

def g191h7 (i : Nat) : Nat := 0x30450ac641c0062400b2c00a0c8100000001c50000042a883a

def g191d6 (i : Nat) : Nat := 0xdf2b688de6543ca1408fb4c102b944193f85dd1604c23ef22c16eaa062fe1b7454930cdbc26e2982411f79161e6290336f0838ae69056de5183dc5208fb4c0e2b9a419b784dc5734823ef22c16ea9847de4582dd110

def g191l6 : Packing := (12,4,5,0,0,6,0,g191d6)

def g191samples : Array (Bits × Bits) := #[(0xbfd3579740f82be9fbed9f2bf55be3fafcb6662d6f7f3cf14bf08eabb46def1e662ae1c9f7512026ffb6ce8c845e43cb1e95bbd30ca37d5ffae27f269e3647fbee97e07ff865dd7312da8e80efa31334f8b77110a294fa2c140112476e217263,0x2080c4801a918000000788981094102182e064200041a20e01811088600a00000a0410200509a0288714001052345290240023261b0000084008020822302e042000004202000840001a8204e622010a10823154424006181028000900212202),(0xb37904ce7ff56953de81ac717d90a71034d3d5d4a6fc75cccee09986647d661c9fc7e2224bfadc359caaf0656b3911ffba9be216f65fa1c49dbf899874bee9c7f5c564fafbf649e0e6a550613dee46b171e50184200e13000163a237ccc4483f,0x865e2104050a72308a5004042641c980010283044b2040e124126c531835005500198c1aba02181140abc5678c0189468338d498806278908b5321e7c4c8810241a8c13849d59586812550c011dc22916965caaa243f59e4c1d3e726bcc44879),(0x7656b9ffaf7fbcd69696b5df89fd9fd9ae655747dd1dde16ff5d7744cf5357c78b75072e3bbcb52bd54454f9bc65746e7a9ed8397e009281987995e65ee4a7ee05d326f4f39716d75fcb8767821ad46b844808258e2a3253cf6ea13881040d8c,0x188100311060810400243a01002a004902001000008004128824000427886820c42250e000058040030408106142220830c2000001010662102c0c081004704100440000b0200040200287218002942c96181045804080031c00109841008504),(0x9e7ecfa1b663be289e4e66e85ebe769cf03a281c40aec59a531a89bdc2917cd75aa40958eacffcda90ffe7137ad9bff7c173ac63ed6d16faf510b9fc03b7f5f2d538ed592be83d129d6669d07e8c08ca07a98c101ac024d2c2804ca411f909a0,0x2020b0c60a9160431882c064a005031090c42e02006ae00c2440711a4040051813940a051c50163000124107860054800c0c2f44ea48411cc000b18200218c840512000a0e08838a406428c05eec0a4201a424385293645c4328c32710b10ae0),(0x48afe352529d9f71e7ba56c3df9455f86aec7ed231a4182f1e83909b5b57f4f8538abddc7c7bd3f1e1b9b703af0697bd7a206ddf91cebd2d1fe45a97aba9de0433ffdbc89b85911bb19554139111eda5cf49d49289dc948100804cc031fe5240,0x25d0110c02e0120e3281003064a88866903819d13801580523a06641510480140208540c08000c15820366000c9a90d0301d08104368a0114124404884a40038061e094010120253d8154130111e4b5ce49ca82ad2c98a38c923cd0654ed000),(0xbb71faf6e605e9fb69774f3f236affdec5b0f6fc6eeb31aaab9709ba59825f28b5e1b4c9a929ee60ce313e2861ba59e08d7b943cc731de5f7b3f26db622d793b8c1abc517578e53938e53ba84144b4c40e1226cad10169ac341018648a03a410,0x9053085ae00818282a703443c76b2b0c1000189e64880d00a862421010858634043845cc00044bd648405185014800014980040164a5632124140422c100414152debe81912c530410e509e8114094c4ae18468a9400a0a6cc00bdf6de028450),(0,0),(0x541bb2ba83ee7937935c70decb49594d47a4a4bbdac0cf1bb6dff7e75f8a6af2553074ec29c33f1ac9dfa1d5d1c59a7cfbcf815d0a96bfd0e7b6f0ad684c6c94849037d4150cbe2d31f8f01e2cfde810414683fb572913092a5d010800038410,0x440cb00009032480d08100bc3804041260f22640803472210689108b0060000019052801ae422029a0ab02480631d020022da000985a8898cbc3c1010c6808bc0020011c08418480cb1870162cbd68114126a930633d5f5823ff420120010200),(0,0)]

def g191columns : List ColumnInfo := [(160,0,31,0,7),(24,0,167,0,7),(2,0,189,0,8),(19,0,172,0,4),(0,16,166,9,6),(4,0,187,0,7),(1,0,190,0,7),(36,128,27,0,4),(136,0,55,0,5),(129,32,30,0,4),(9,16,166,0,4),(20,8,163,0,4),(14,0,177,0,4),(35,0,156,0,4),(56,0,135,0,4),(26,0,165,0,4),(134,0,57,0,4),(162,0,29,0,4),(152,0,39,0,4),(25,0,166,0,4),(168,0,23,0,4)]

def g191autos : List (List Nat) := [[],[115,84],[32,67,117],[32,83,116]]

def g191levels : Nat → Packing
  | 10 => g191l10
  | 9 => g191l9
  | 8 => g191l8
  | 7 => g191l7
  | 6 => g191l6
  | _ => emptyPacking

def g191index : Nat → Nat → Option (Nat × Nat)
  | 10 => lookupWord 16 41 5 10 4 2 g191h10
  | 9 => lookupWord 67 277 6 13 7 2 g191h9
  | 8 => lookupWord 100 251 6 13 7 2 g191h8
  | 7 => lookupWord 4 19 2 10 4 2 g191h7
  | _ => fun _ => none

def g191 : Forest := ⟨191,10,fun j => g191samples[j]?.getD (0,0),g191columns,g191autos,g191levels,g191index⟩

set_option maxHeartbeats 0 in
theorem geomg191 : graphValid g191 (boundsBefore known127) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=3) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tablesg191 : checkedTables g191 10 := by
  apply Brief.schedule_ok [[],[],[],[],[],[],[(12,7,0,2)],[(13,7,0,2),(36,8,0,3),(36,8,0,3),(31,8,0,3)],[(3,7,0,0),(36,8,0,3),(31,8,0,3),(36,9,0,3),(7,9,0,1)],[(12,8,0,2)],[(1,7,0,0)]] rfl
  simp only [Brief.scheduled,Brief.covered,Brief.total,cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals first | exact True.intro | decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low191 : Lower true (vars 191) (graphGoal 191) 11 := plain_low (hints:=536879361) (by decide +kernel) (index_root (g:=g191) (i:=0) rfl rfl (before_sound known127 valid127) geomg191 tablesg191 (by decide +kernel))

def known191 := extendKnown known127 11 [(191,[]),(319,[135,50,65]),(351,[133,117,101,33,48]),(367,[128,16,64,100,80,113,33,48]),(379,[130,50,81,115,98,65]),(445,[129,82,97,48]),(487,[115,83,82,130,99,66,16]),(494,[64,132,49,96])]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid191 : Known true known191 := extendKnown_ok (m:=191) valid127 low191 (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low251 : Lower true (vars 251) (graphGoal 251) 8 := plain_low (hints:=1358970881) (by decide +kernel) (cut_root (prior:=boundsBefore known191) (before_sound known191 valid191) (128,0,123,0,7) (by decide +kernel) (by decide +kernel))

def known251 := extendKnown known191 8 [(251,[])]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid251 : Known true known251 := extendKnown_ok (m:=251) valid191 low251 (by decide +kernel)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low255 : Lower true (vars 255) (graphGoal 255) 12 := plain_low (hints:=553656577) (by decide +kernel) (cut_root (prior:=boundsBefore known251) (before_sound known251 valid251) (64,0,191,0,11) (by decide +kernel) (by decide +kernel))

def known255 := extendKnown known251 12 [(255,[]),(479,[118,133,33,48]),(503,[115,82,98,131,66,16]),(507,[99,81,115,130,65]),(509,[82,129,48]),(510,[100,49,128])]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid255 : Known true known255 := extendKnown_ok (m:=255) valid251 low255 (by decide +kernel)

def g383d12 (i : Nat) : Nat := 0x1840804ff

def g383l12 : Packing := (1,0,6,0,0,0,0,g383d12)

def g383h12 (i : Nat) : Nat := 0x2e190000e44028954b00129713b90021c5c400a24a286e030000000000d800006790000005048cec0c584c000029410000109

def g383d11 (i : Nat) : Nat := 0x1c1800c080840a80c160880850c1604287044044070d0e04282102a03050f061043070d0a08508680361365e17803fe087fc30ffa61ff443ff187fe10

def g383l11 : Packing := (6,1,6,0,0,9,0,g383d11)

def g383h11 (i : Nat) : Nat := 0x605ec8c0000001117d3d8e632bfc434126a560a0c97cd1c2e0006879dce0130002029832241d31f89848e70800000000019dd990a81d83401050198b41ca520a2f40adbada290270002212000f0240555b3c62d0c010b44640b0000000000a02000000274e000193000140ac0e19590854ad62490de02102d21d6156142944000d8a4082dc48550007f7944400014100014220513068000058000991281875380f661504984eda4b2e787cc39625232a002653d245061c2fea2000000680400000024e94b1850b1ad217010100600b00017050301c050070e260404451400410

def g383d10 (i : Nat) : Nat := 0x2e1d818587821e221614a130f091146478584c0c3c2c10b0a7088561608c040207a04c442860211d1a16112300a10082e1c61311850b0a4746c2c1058458988a3028223838785a5041d141418442a102d2088a0a12225460ac2c10805040f40583c282820b0a1c4c45191c1c4824e230c8c09820a901e8c30705040d0e3618222878514342c181c14442810482548c140e0b08166420584040b0a30885c282a3030203e08a072c1610102428b860a11821e1464106058707110b382838984902d1c1d18284824e230c8c0e201c1670947074642040a0f0b4e183a3022286871d083210102c28c861e0f818409821c149061607c10ac2110440306e0e102e1e00585261c18170708242c1100c140a08406050d0ac1080438303848582821818242f042010c0f840a23821408711c2060407c3c0c10a0f503606183e08206e10587291c1814370b04281108e0d878209840b801412a07050418804020c561f04108080a20504121e003e160821ac3aa6695281e74a5d64a236e2ba1a60b1fbdea9dd5d21bcdaf9a258b17fd7296355a14ad3b92851910bcf88e74d40c2cb98aa49d08fc8086b456044c2f828421017c1280d4003ff5c530ffd73443ff5c130ffd73043ff1cc10ffd73843ffa0d10ffd718c3ff9c430ffd30443ff1ce10ffc83443ffcc110fff814c3ffa0530ffe718c3ff4c610ffd318c3ff9ce10ffe318c3ff60530ffd710c3ff1c430fff83443ffcc610ffd83443ff20530fff718c3efe1130ff9708c2ff60d10bfd818c2ff60c10bfd838c2ff60610bfd810c2ff61e30ff9704c2ffe0530bfd83842ffe0d10bde83042bf61830bed828c2fb60810bdd83042efe1130

def g383l10 : Packing := (47,2,6,0,0,12,0,g383d10)

def g383h10 (i : Nat) : Nat := 0x71198115833604b01a0000606e88fc000242d7c1fb0faad280000000907200000000000000000011a60000c095e07a03c80000000207200b0000f0374218000083d74340000000000010fe000191d800038c8000000000050001a19c0000000f0d80002417105f0001002bc08ec1b0001e12c0000000f0e7e92d81a6801000081e2997c07b60460002f86e047b093591c0b42863642440b4814a40900000001016701f80992cbb0308000c10b416439d943b147aae0000000140000000051cc437e4b4604d43368120000516302b9f1000004067d0c8043000061b56b100000c580000000783f104c0003fbb80009070d07382c4f54000000014a410460001715080ea8740833a5880002404721a41d7010e870e0a6000041e7802d68a0000000000000016605c32d9336823a9a000d7e20d86d416e10a400828f5440c813b83e60a220d8fa1581020e4099e8197842301210c9aa808357404e01fd304041e1023c6482e6b2cf063e21e71a6056370a003201825400056b139c293c35f0f8311d9031132ca772115827b06218a0203561cf86910f5a5f4b8b233b382b58ee49dec3300d7802d8c0502fd10109b0c0a907ee0a0fc274022d3a10d5060b108505d001d3c31732301838cca1790204071480aad97c1b8000509cd0a402a9482901e3171c30000064ac78e80004854e040ddec841106f32a0420d715820cb2810092535383b24a5005e83218280109ecf40006a47e0540003c1d6c17800c84f7001b077b0900001c268000e088000143b221e2f0000390d00040c17340800211f04000c3852005c082b04030102880201024c3d0e17000f0511410100573e04001200070500016400040b010407000d00010204010004000a010e07000000003720

def g383d9 (i : Nat) : Nat := (if i<1 then 0xb102c382e18141e0b0515081b05844813238441e0b28448e13e08641e68382b080b205c2c0a1814320a1f08220f1817080b05100a17058c081a0c8c160a1210200b0890220a14101e2a30128a0e230b820f0510240a048f81c10782c145e083b0a0a0214100fe082808592d490e4231f18e446c63231688a8c4ea2230fa871c33216b09e843c15606b0037f63ee9f46f8c7b63d0de34ef1768baa1d10e6871fb8a1c10ddf6dfb6a1afed5f6a4347d9fecd665b327d8fec6861fb0a1822bf15e8aee9710b685a8ac7d5fead655faa354c8a294fba75d35c98e4bba53926e920484a35d15c897437213905c7fc3ee1f14f1476139c1bd0da86b434a1964c846102f39740b4e5902b39540a6051927c934096049023390f883c3e31e60eb072a37e1af0d1c6602fe16a8a8c4d023f10f87fc3be1b60cb05d82be13608f84201be0b604b0190064000dfeb8b07186ff60573843f7f08b8a61bfc7360610bfecb902986ff606738437fb0fc1a21bff874c110bffcbb06885ffe5d304437fb0e98c217fd9720d10bffcba63085ff65f30442ffb2fc1a217fd97a0d10bfecbe63084ff66173443bf2e1b8c613fd981cc109fe4c2e6884ffe61730427fb30388613fc985c530ddfca307184ffe45878c27fb30b9821bed828c6309ffcbb06085fbe4983442efb2a40a61fd9315c130deec1a63085fe64073842dff2cb88613fd985c130dfb38b02187dee55708c27fb2fc0a61bf581e0530def41f06884ff66173842f7f28c0a61bf57160430bdeca502986f7e0f304427fb3039c21afd91618309fecc6e3185fee41318c27ff2ec1a21bee7360810ddfca307085fee41318437bb2ec18217df935c1309ffcbb07086ef247844c37bb07c1a2177d959c430bfcc8463186fb60a718c27fb3138c61bdd835cc10bfcc80e6084ffa61734427fd30b8a613ff9760630df6cbb05185bf65b318437dd22c1461fd8935c130df6c8b05186f725d830437dae6c10213ff985c630df6c10e6086fbdcd82042feb2398221bed825c630ddf48f08986efe47844c377f08c0a617f5911ce10fddc22e0986efe11704c35fb0cb8861bed9360a30bdeca0e2186efe11714c37f730b84616ff965c630df6c16e3186fda07814c35fb0d38861bdf9760c10bf7c9302986f760c834427fb3138861bf581205309fecc4e7084ff65d810c27ff30b9c217f990dc630dfcc1ae1186fd605318c27ff2ec08617bf944c110ddfc2702985fee41834427fb3198c21bdd83cc610ddfc2502985fe643318435fd22c3061bef9260d109fecc2e3185df65683442efb2b982217ef924c610def4bb06086fb609318c3fb662b82617ef924c6309ffcc2e2186fba5d828c3faa63c0a619fd875c6309fecbf06886f7e0d3044377f0840a61bbd91e11309fecc463184fbe498344277f28c1c213bf9460e30 else 0x730608110514260a15041e8407028a0f1182c7c30505c2240382841342a1060e054102240482c411050a0a840b04480b04881e0410241620582440905881e04103c0a0405828a0b05058605040102e0e284c12202828082509942609105c1c202038143058142c0a203c16110511080404828804050447470503c164e18381e3e083c14342010160a203c2c2c204416308810140f211412111844342e1090220f2010160a182416208810140f2010420a1c10081105900821050c160f101c1c0f182416202858160a202c142088284c6070646040703c60a058a0b040e0581450203c14305038407050118a0e2810160a19140a090890120a102c140411864a090882824442a10081c0b028c0a0c0202e0f28441409183c0a0b07101211090c141910470c0e0590162210441e20902c505020142c0a2c1042208290161c1014080e0b918e1a0b8c2304058e8219420281656283c1430785041fa17068a0f05188c060702c9c1038281e4e17040e0aa28101e70805c163040501430284c123e07081dc107828c13088a0c0508e101650ad60140b20281e202114121120281c2e1f041e0a211c162048442430503c404070287040d8441640f04c1e34202c143e081c140f2210080b05101211090f85c18e810140f303c282020641630785040f0a0a8a0f050c1e0)

def g383l9 : Packing := (136,3,6,0,0,13,0,g383d9)

def g383h9 (i : Nat) : Nat := 0xa16f054972c28000915083d009e0b000184b4aa00070df9a0000000103800000000040895c7d1f430452c83b41000000066c401a931403589000181590e60c4006e970739878c268f4319a8a1e8a227410f80515a000677800202f029915b907440e6c7f8b08b068a9c416408c84be1fb32f040001432000000000000000000001daa0990d58b4800e1d917e01640581811720991cb65f653999ed0240cf0c80400004d08a6610820084081054000400010000a42100804

def g383d8 (i : Nat) : Nat := 0xa10200000e0858408185082e10440a10000c840000161001e1030a10000000000504000000000141001e10108102819120810282002820c8400001e10283e0edf5ba3ccdeebb539ac5dcadb68acd529f4a9dcda4f2289c3a13047fbe9eaf070b71aed266b2186be57aa93696439b8be50258f05a28118781e00dafe5b845c530cefe1f944c110aef69c91e1130afb68f7360810cefe119720530cef5c79460e30cfb61f924c610adfe9587e0d10cef5c79460e10cdb655821cc10f745c5315c1308fdea581205308efe91985c1308fb689981cc10caf619941c4308fbe89985cd108bf69a985c530afa6829760a30cafe5b845c530ccfe119520530cdb655829c630cfa609901cc10cebe539260d10aebe8991e1130af66809760c10cbbe59825c6308fb68b9161e308efe91989ce108bfe999760430af36889760c10ceb651828c6308efe91985ce108fb6a582dc6308bfe9b985c4308bfe99985c630c9f655869c430cebe139260530ad76949760c108bf6a3965c430acf69491e11308f7ea58320d10cfa609908c630af9a869760a30add6967160430aeb6929760a30af96869760a308ef6a784a0530ceb651821cc108dfe9597e0530aebe919360a30ccfe57845c130cee611901cc108fb6a3924c630

def g383l8 : Packing := (53,4,6,0,0,9,0,g383d8)

def g383h8 (i : Nat) : Nat := 0x834601a000

def g383d7 (i : Nat) : Nat := 0xa295fdb2e3ca3070852bfb65c79460e30

def g383l7 : Packing := (2,5,6,0,0,3,0,g383d7)

def g383samples : Array (Bits × Bits) := #[(0x7bf3da45af3f8c085a5cb987177b99507674f4c937c6357ff7c7e09ce49beeecbf7777c878bea111faf6da326b91bcf4ee730cf4458d3f7279c9098db86383f541a14f4a486b2153ac6cc220d9a4c042882144400812c1a03824014a3e21f653,0x6c0c090884541000400081001004571001111584ccc2050082180001a00200048800100001140810814340242a00840000001e41a6804200410144118003835041a0c802027c003361601060690134460c209508104109022004008a24212652),(0xda7e816f3febb7859eb69321adfa95cb2d74d81a38e8c2993ff7c9dd4f4fdcfc37abafbfbba54cf8bb0babce157e577aab0a9e256f1eae7cb247b98d969c798b2d38f019ccd955a0208a2083da20800120c010a1d5456e25c86f4208c8c6481f,0x200340281060102045a2028208088a028404101004082010471440221a34022cc86840000420200840493000840180b1200280000b80480000922403c288328053019888301081491048f8080c08110c302d0c88414008862440588c44809),(0x52ade7ca8472a7a2b56b45b28960a5c8855d7bfc72374bde836b42ebf256bce2c89e0322188af5a96fcb796fb735d57e3a905ea1a25930bb344d14966b67f70482928ec6864892a7808c5443041003000306a901d5cd20440308a310f1078f9c,0xa3a4450a514a89fc8820001843cd690501c00eb41e050930160a86a871d844195d20280b969390c9c938d200449522e21481ab52f26044d05d2ac050b183d70482108ec6035cd2a7ca2c536061530706a304a029342b68660288a31871038514),(0xcf2b445e2c8f92ea37f69711935dc32d8ac9fba75f0b2f7fbdacff602b76c3137a977e4a5b3a7afe6df0f64bb3819165489d455d3f7e263153db4ef0e6c80a735fca4439b2e3869d91109444066714241006ab062288005b03d09cb601f80f80,0x101122848c00200004002802081012c00c02114a80101082802100010a0090020018000021040430120100132800000c02081029098d0105024030240068003b598a4030a023055011412c961ea430201c00594401409011095010a200b00a80),(0xfbaa4318baa57959542a280e640df39778b4d46b1f3c151bf3f0993bd0fe3df9e94e95428bc437eb34b11ff92c19ff03e6ba72ca35ff1343ff1f07fcbab67c86b44125c70c20a80cbc7ec00400020c06c00546400210005cf480fbe001fff020,0x8040d4706129c441b0475088a0e888071200a8201328086d4886b9f0058842e007632e164441220f2c88aa4885ca32b2c0c760840000bc8810be098871947c84a44125c50d00a80c8e1ec30880424881e00722b16ebe406cd4a0ef45014ed020),(0x7ef39cf81d5ebfdc6993b54fc7da086bed316d3dbd7f9d6ce832af685e8fd1cd19ce79faca95b97ac8e7c4c05d5e67a574ecf577efc3e7095e97adf781983c3ab81e2a648807c2c202060a2405bc40004ff800180a32b78004109b53fe000020,0x3b116c16a202824b0cc22038f088041884a8a1812009a5c2c8129c84ec854a2661c6038ac4b07a92e088c80c12a20362704402048320491046298482c58382ab81e02648903c2c012072c9614fe40a0d2916af00796b6a00c309b74da000000),(0x82936fa0d663c33f77e458ec25db297ecc3724c6a282d566f829f79a33da631af6febbbd2c61acfdfc6437c69f10522cfb1ae989294191c6906f60620fd19338998a1ec23330ce50600f619822183bd9200010a002102fddf75f600000000040,0x92e0cc00ec44880444e0840207441f201096061cea13905cbc41881041060826d5310928ed2f1538200888082860024204842842a113418046b620c484811338919a0e423320c650636e78101b5b3e708c0079280753abfc771d20a800000000),(0,0),(0xce927de0dc24ecd0970de7df73d2ffaa3a7fb3c39ffc6327e8d14647987af226336096189d5d227dd00d2c64c7fe7699f3e777dfda82d597d5b7da7ebf6fc4c4e66431b5758c1c33431509592059bbf857fc041ea02010020410640500000060,0x440c002011900401091151a01080401e02200080052040204210522410310308088004430210280280d20140100015010042050012008a48110844101106c4c406603181449c382f0c900368e000810f216e8403f82840020080440100000060)]

def g383columns : List ColumnInfo := [(32,0,351,0,11),(64,0,319,0,11),(4,0,379,0,11),(16,0,367,0,11),(49,0,334,0,7),(70,0,313,0,7),(256,0,127,0,9),(24,0,359,0,8),(28,0,355,0,7),(83,0,300,0,4),(276,8,99,0,4),(69,2,312,0,4),(260,0,123,0,7),(2,1,332,48,6),(57,0,326,0,4),(50,1,332,0,4),(65,0,318,0,7),(104,256,23,0,4),(39,0,344,0,4),(300,0,83,0,4),(29,0,354,0,4),(5,0,378,0,7),(321,32,30,0,4),(262,64,57,0,4),(352,0,31,0,7),(74,4,305,0,4),(305,0,78,0,4),(80,0,303,0,8),(290,64,29,0,4),(72,0,311,0,7),(328,0,55,0,5),(18,0,365,0,7),(273,32,78,0,4),(41,16,326,0,4),(26,4,353,0,4),(51,0,332,0,4),(36,0,347,0,8),(344,0,39,0,4)]

def g383autos : List (List Nat) := [[],[98,131,84],[16,66,101],[16,82,131,100],[48,129,82],[48,129,98,16,66,84],[128,49,100],[128,49,66,16,82,98]]

def g383levels : Nat → Packing
  | 12 => g383l12
  | 11 => g383l11
  | 10 => g383l10
  | 9 => g383l9
  | 8 => g383l8
  | 7 => g383l7
  | _ => emptyPacking

def g383index : Nat → Nat → Option (Nat × Nat)
  | 12 => lookupWord 8 37 4 10 3 3 g383h12
  | 11 => lookupWord 48 123 4 13 6 3 g383h11
  | 10 => lookupWord 79 299 8 15 8 3 g383h10
  | 9 => lookupWord 39 99 5 13 6 3 g383h9
  | 8 => lookupWord 1 5 1 8 1 3 g383h8
  | _ => fun _ => none

def g383 : Forest := ⟨383,12,fun j => g383samples[j]?.getD (0,0),g383columns,g383autos,g383levels,g383index⟩

set_option maxHeartbeats 0 in
theorem geomg383 : graphValid g383 (boundsBefore known255) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=3) ?_⟩,listPieces_all (d:=1) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tablesg383 : checkedTables g383 12 := by
  apply Brief.schedule_ok [[],[],[],[],[],[],[],[(2,8,0,0)],[(36,8,0,3),(8,8,0,1),(9,9,0,1)],[(3,8,0,0),(36,9,0,3),(36,9,0,3),(36,9,0,3),(8,9,0,1),(17,10,0,2)],[(6,8,0,1),(13,9,0,2),(28,10,0,3)],[(6,9,0,1)],[(1,8,0,0)]] rfl
  simp only [Brief.scheduled,Brief.covered,Brief.total,cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals first | exact True.intro | decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low383 : Lower true (vars 383) (graphGoal 383) 13 := plain_low (hints:=12901687553) (by decide +kernel) (index_root (g:=g383) (i:=0) rfl rfl (before_sound known255 valid255) geomg383 tablesg383 (by decide +kernel))
end PublicFloor
namespace PublicFloor
open PEqualNP.CircuitLowerBounds

theorem repr_neg {w a} (h : Repr true w a) : Repr true w (neg a) := by
  unfold Repr
  rwa [nrm_neg]

def isNot (g : Gate) : Bool := match g.op with
  | .not => true
  | _ => false

theorem reach_up {R u} {roots : List (Wire R)} {p bank} (h : Reach false roots p bank) : Reach u roots p bank := by
  have up {bank : List (Wire R)} {a} (h : Available false bank a) : Available u bank a :=
    h.imp id (Or.imp id (fun h => Bool.noConfusion h.1))
  induction h using Reach.ind with
  | start => exact Reach.start
  | two op h ha hb ih => exact Reach.two op ih (up ha) (up hb)

theorem lower_down {u roots T L} (h : Lower true roots T L) : Lower u roots T L := by
  cases u
  · exact fun p bank hr ha => h p bank (reach_up hr) (ha.imp id (Or.imp id (fun h => Bool.noConfusion h.1)))
  · exact h

theorem known_down {u es} (h : Known true es) : Known u es := fun e he => lower_down (h e he)

theorem slice_self {u} {raw : List Sig} {T : Sig} {L : Nat} (pT : proper T) (h : Lower u raw T L) :
    Slice u raw T one L := by
  refine ⟨id,raw,fun r => bit_one r,fun a ha => ?_,observe_proper pT,h⟩
  exact Or.inl (List.mem_map_of_mem ha)
end PublicFloor

namespace Family
abbrev W := BitVec 512

def gate (u v : Bool) (a b : W) : W :=
  if u then (if v then a ||| b else (~~~a) &&& b)
  else (if v then a &&& (~~~b) else a &&& b)
end Family

namespace Family
def boolGate (u v a b : Bool) : Bool :=
  if u then (if v then a || b else (!a) && b) else (if v then a && (!b) else a && b)

lemma gate_bit (u v : Bool) (a b : W) (j : Nat) :
    (gate u v a b).getLsbD j = boolGate u v (a.getLsbD j) (b.getLsbD j) := by
  by_cases hj : j<512
  · cases u <;> cases v <;> simp only [boolGate,gate,Bool.false_eq_true,ite_false,ite_true,
      BitVec.getLsbD_and,BitVec.getLsbD_or,BitVec.getLsbD_not,hj,decide_true,Bool.true_and]
  · have ge : 512 ≤ j := by omega
    rw [BitVec.getLsbD_of_ge _ _ ge,BitVec.getLsbD_of_ge a _ ge,BitVec.getLsbD_of_ge b _ ge]
    cases u <;> cases v <;> rfl
end Family

namespace PrimarySchedule
variable {V G : Type}

def ready (need : G → List V) (pool : V → Prop) (g : G) :=
  ∀ v ∈ need g, pool v

def add (v : V) (pool : V → Prop) := fun x => x=v ∨ pool x

def extend (out : G → V) (pool : V → Prop) (gs : List G) :=
  fun w => w ∈ gs.map out ∨ pool w

def executable (need : G → List V) (out : G → V) : (V → Prop) → List G → Prop
  | _, [] => True
  | S, g::gs => ready need S g ∧ executable need out (add (out g) S) gs

theorem weaken {need : G → List V} {out : G → V} {S T : V → Prop} {gs : List G}
    (ok : executable need out S gs) (inc : ∀ w, S w → T w) : executable need out T gs := by
  induction gs generalizing S T with
  | nil => trivial
  | cons g tail ih =>
    exact ⟨fun w hw => inc w (ok.1 w hw),ih ok.2 (fun w h => h.imp id (inc w))⟩

theorem residual {need : G → List V} {out : G → V} (select : G → Bool)
    {S : V → Prop} {gs : List G} (ok : executable need out S gs) {T : V → Prop}
    (sub : ∀ w, S w → T w) (haveOut : ∀ g ∈ gs, select g=true → T (out g)) :
    executable need out T (gs.filter (fun g => !(select g))) := by
  induction gs generalizing S T with
  | nil => trivial
  | cons g gs ih =>
    obtain ⟨use,tail⟩ := ok
    cases h : select g with
    | true =>
      have grow : ∀ w, add (out g) S w → T w := by
        intro w hw
        rcases hw with rfl | old
        · exact haveOut _ (List.mem_cons_self ..) h
        · exact sub _ old
      simpa [h] using ih tail grow (fun w hw => haveOut w (List.mem_cons_of_mem _ hw))
    | false =>
      have incl : ∀ w, add (out g) S w → add (out g) T w := fun w hw => hw.imp id (sub w)
      have tailOk := ih tail incl
        (fun w hw yes => Or.inr (haveOut w (List.mem_cons_of_mem _ hw) yes))
      have rg : ready need T g := fun w hw => sub _ (use w hw)
      simpa [h,executable] using And.intro rg tailOk

theorem prepend {need : G → List V} {out : G → V} {S : V → Prop} {front tail : List G}
    (use : ∀ g ∈ front, ready need S g) (ok : executable need out (extend out S front) tail) :
    executable need out S (front++tail) := by
  induction front generalizing S with
  | nil =>
    have eq : extend out S [] = S := by
      funext w
      apply propext
      simp [extend]
    rw [eq] at ok
    exact ok
  | cons g gs ih =>
    have eq : extend out S (g::gs) = extend out (add (out g) S) gs := by
      funext w
      apply propext
      simp [extend,add,or_assoc,or_comm]
    rw [eq] at ok
    refine ⟨use _ (List.mem_cons_self ..),ih (fun a ha w hw => ?_) ok⟩
    exact Or.inr (use a (List.mem_cons_of_mem _ ha) w hw)

theorem pairwise_of_all {r : G → G → Prop} {xs : List G}
    (h : ∀ a ∈ xs, ∀ b ∈ xs, r a b) : xs.Pairwise r := by
  induction xs with
  | nil => exact .nil
  | cons a xs ih =>
    exact .cons (fun b hb => h _ (List.mem_cons_self ..) _ (List.mem_cons_of_mem _ hb))
      (ih (fun i hi j hj => h _ (List.mem_cons_of_mem _ hi) _ (List.mem_cons_of_mem _ hj)))

theorem ordered_schedule (need : G → List V) (out : G → V) (S : V → Prop) (gs : List G)
    (score : G → Nat) (limit : Nat) (upper : ∀ g, score g ≤ limit)
    (last : ∀ g, ¬ready need S g → score g=limit) (ok : executable need out S gs) :
    ∃ order, order.Perm gs ∧ executable need out S order ∧
      order.Pairwise (fun x y => score x ≤ score y) := by
  classical
  let select := fun g : G => decide (ready need S g)
  let leq := fun a b : G => decide (score a ≤ score b)
  let early := gs.filter select
  let late := gs.filter fun a => !(select a)
  let sorted := early.mergeSort leq
  have sortPerm : sorted.Perm early := List.mergeSort_perm early leq
  have rest : executable need out (extend out S sorted) late :=
    residual select ok (fun _ h => Or.inr h) (fun a ha yes =>
      Or.inl (List.mem_map_of_mem (sortPerm.mem_iff.mpr (List.mem_filter.mpr ⟨ha,yes⟩))))
  have allow : ∀ a ∈ sorted, ready need S a := fun a h =>
    of_decide_eq_true (List.mem_filter.mp (sortPerm.mem_iff.mp h)).2
  have tailRank : ∀ a ∈ late, score a=limit := by
    intro a ha
    have denied := (List.mem_filter.mp ha).2
    apply last
    intro h
    simp [select,h] at denied
  have trans : ∀ a b c, leq a b → leq b c → leq a c := by
    intro a b c x y
    exact decide_eq_true (Nat.le_trans (of_decide_eq_true x) (of_decide_eq_true y))
  have total : ∀ a b, leq a b || leq b a := by
    intro a b
    rcases Nat.le_total (score a) (score b) with p | p <;> simp [leq,p]
  refine ⟨sorted++late,(sortPerm.append_right late).trans (List.filter_append_perm select gs),
    prepend allow rest,List.pairwise_append.mpr ⟨?_,?_,?_⟩⟩
  · simpa [sorted,leq] using List.pairwise_mergeSort trans total early
  · exact pairwise_of_all (fun a ha b hb => by rw [tailRank a ha,tailRank b hb] <;> exact Nat.le_refl _)
  · intro a _ b hb
    rw [tailRank b hb]
    exact upper a
end PrimarySchedule

namespace Order
abbrev W := BitVec 512

def place (a : W) : List W → List W
  | [] => [a]
  | x::xs => if a.toNat≤x.toNat then a::x::xs else x::place a xs

theorem place_perm (a : W) (ws : List W) : (place a ws).Perm (a::ws) := by
  induction ws with
  | nil => exact .refl _
  | cons x xs ih =>
    simp only [place]
    split
    · exact .refl _
    · exact (ih.cons x).trans (.swap a x xs)

def ordered : List W → List W
  | [] => []
  | x::xs => place x (ordered xs)

theorem permutation (ws : List W) : (ordered ws).Perm ws := by
  induction ws with
  | nil => exact .refl _
  | cons x xs ih => exact (place_perm x _).trans (ih.cons x)
end Order

namespace Load
abbrev W := BitVec 512

abbrev Choice := Nat × W × W

abbrev Board := Nat × List W × List Choice

abbrev Root := Nat × Nat × Nat × Nat × Nat × Nat × Nat

abbrev Link := Nat × Nat × Nat × Nat

def field (w shift width : Nat) := (w >>> shift) &&& ((1 <<< width)-1)

def opCode (v : Nat) := if v=1 then 3 else if v=3 then 1 else v

def gate (d : Nat) (a b : W) :=
  if d=0 then a &&& b else if d=1 then a ||| b else if d=2 then a &&& ~~~b else ~~~a &&& b

def successor (score : Choice → Nat) (before : Board) (act : Nat) : Board :=
  let (_,ws,history) := before
  let a := ws.getD (field act 0 4) 0
  let b := ws.getD (field act 4 4) 0
  let op := opCode (field act 8 2)
  let c := (op,a,b)
  let ka := act.testBit 10
  let kb := act.testBit 11
  let rest := ws.filter fun w => (ka || w != a) && (kb || w != b)
  let next := Order.ordered (gate op a b::rest)
  (score c,next,c::history)
end Load

namespace Trace
open PublicFloor
open PrimarySchedule

abbrev Step := Nat × Sig × Sig

def need (g : Step) : List Sig := [g.2.1,g.2.2]

def result (g : Step) : Sig := bin g.1 g.2.1 g.2.2

def good (u : Bool) (g : Step) :=
  allowed u g.1 ∧ proper g.2.1 ∧ proper g.2.2 ∧ g.2.1≠g.2.2

theorem instructions {u y k S} (h : Live u y k S) :
    ∃ gs : List Step, gs.length=k ∧ executable need result (fun x => x∈S) gs ∧
      (y∈S ∨ y∈gs.map result) ∧ ∀ g∈gs, good u g := by
  induction h using Live.ind with
  | stop hp => exact ⟨[],rfl,True.intro,Or.inl (Finset.mem_singleton_self _),by simp⟩
  | @binary k U a b d hd ha hb ne _ _ ih =>
    obtain ⟨gs,sz,ok,hit,leg⟩ := ih
    let g : Step := (d,a,b)
    have available : ∀ x ∈ insert (bin d a b) U,
        add (result g) (fun x => x∈insert a (insert b U)) x := by
      intro x hx
      rcases Finset.mem_insert.mp hx with eq | e
      · exact Or.inl eq
      · exact Or.inr (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem e))
    refine ⟨g::gs,by simp [sz],⟨?_,weaken ok available⟩,?_,?_⟩
    · intro x hx
      simp only [need,g,List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with rfl | rfl <;> simp
    · rcases hit with h | h
      · rcases Finset.mem_insert.mp h with eq | mem
        · exact Or.inr (List.mem_cons.mpr (Or.inl eq))
        · exact Or.inl (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem mem))
      · exact Or.inr (List.mem_cons_of_mem _ h)
    · intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact ⟨hd,ha,hb,ne⟩
      · exact leg _ hq

def Ranked (u : Bool) (y : Sig) (rank : Step → Nat) : Nat → Nat → Finset Sig → Prop
  | _,0,S => S={y} ∧ proper y
  | phase,k+1,S => ∃ (g : Step) (U : Finset Sig), good u g ∧ phase≤rank g ∧
      S=insert g.2.1 (insert g.2.2 U) ∧ result g∉S ∧ Ranked u y rank (rank g) k (insert (result g) U)

lemma earlier {u y rank lo hi k S} (p : lo≤hi) (h : Ranked u y rank hi k S) :
    Ranked u y rank lo k S := by
  cases k with
  | zero => exact h
  | succ k =>
    obtain ⟨g,U,legal,bound,eq,fresh,tail⟩ := h
    exact ⟨g,U,legal,p.trans bound,eq,fresh,tail⟩

lemma forget {u y rank phase k S} (h : Ranked u y rank phase k S) : Live u y k S := by
  induction k generalizing phase S with
  | zero => exact h
  | succ k ih =>
    obtain ⟨⟨d,a,b⟩,U,g,_,rfl,fresh,tail⟩ := h
    exact ⟨U,a,b,d,g.1,rfl,g.2.1,g.2.2.1,g.2.2.2,fresh,ih tail⟩

lemma extract {u y} (hy : proper y) (rank : Step → Nat) (gs : List Step) (phase : Nat)
    (pool : Sig → Prop) (ok : executable need result pool gs)
    (hit : pool y ∨ y∈gs.map result) (legal : ∀ g∈gs, good u g)
    (lower : ∀ g∈gs, phase≤rank g) (sorted : gs.Pairwise (fun a b => rank a≤rank b)) :
    ∃ k≤gs.length, ∃ S : Finset Sig, (∀ x∈S, pool x) ∧ Ranked u y rank phase k S := by
  classical
  induction gs generalizing pool phase with
  | nil =>
    have yes : pool y := hit.resolve_right (by simp)
    exact ⟨0,Nat.le_refl _,{y},fun w hw => Finset.mem_singleton.mp hw ▸ yes,rfl,hy⟩
  | cons g gs ih =>
    have h0 := ok.1
    have all := List.pairwise_cons.mp sorted
    have nextHit : add (result g) pool y ∨ y∈gs.map result := by
      rcases hit with old | fromTrace
      · exact Or.inl (Or.inr old)
      · rcases List.mem_cons.mp fromTrace with eq | later
        · exact Or.inl (Or.inl eq)
        · exact Or.inr later
    obtain ⟨k,cap,T,sub,tail⟩ := ih (rank g) (add (result g) pool) ok.2 nextHit
      (fun a ha => legal a (List.mem_cons_of_mem _ ha)) all.1 all.2
    have lowerG := lower g (List.mem_cons_self ..)
    by_cases keep : result g∈T ∧ ¬pool (result g)
    · let U := T.erase (result g)
      have old : ∀ x∈U, pool x := by
        intro x hx
        obtain ⟨ne,mem⟩ := Finset.mem_erase.mp hx
        exact (sub x mem).resolve_left ne
      have supply : ∀ x∈insert g.2.1 (insert g.2.2 U), pool x := by
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact h0 _ (List.mem_cons_self ..)
        · rcases Finset.mem_insert.mp hx with rfl | hm
          · exact h0 _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
          · exact old x hm
      refine ⟨k+1,Nat.succ_le_succ cap,_,supply,g,U,legal g (List.mem_cons_self ..),lowerG,
        rfl,fun mem => keep.2 (supply _ mem),?_⟩
      simpa only [U,Finset.insert_erase keep.1] using tail
    · refine ⟨k,cap.trans (Nat.le_succ _),T,?_,earlier lowerG tail⟩
      intro w hw
      rcases sub w hw with rfl | hp
      · exact Classical.byContradiction (fun bad => keep ⟨hw,bad⟩)
      · exact hp

theorem normalize {u y k S} (h : Live u y k S) (hy : proper y) (raw : Finset Sig) (start : S ⊆ raw)
    (rank : Step → Nat) (limit : Nat) (upper : ∀ g, rank g≤limit)
    (last : ∀ g, ¬ready need (fun w => w∈raw) g → rank g=limit) :
    ∃ m≤k, ∃ T ⊆ raw, Ranked u y rank 0 m T := by
  obtain ⟨gs,len,run,hit,legal⟩ := instructions h
  obtain ⟨order,perm,ok,sorted⟩ := ordered_schedule need result (fun w => w∈raw) gs rank limit upper last
    (weaken run (fun _ hw => start hw))
  have found : y∈raw ∨ y∈order.map result := hit.imp (fun e => start e) ((perm.map result).mem_iff.mpr)
  obtain ⟨m,cap,T,sub,tail⟩ := extract hy rank order 0 (fun w => w∈raw) ok found
    (fun a ha => legal a (perm.mem_iff.mp ha)) (fun _ _ => Nat.zero_le _) sorted
  exact ⟨m,by simpa only [perm.length_eq,len] using cap,T,fun _ hw => sub _ hw,tail⟩
end Trace

namespace RankedIndex
open PublicFloor

def hint (x : Sig) := (0x5000020040081630000070 >>> (4*(x.toNat % 23))) &&& 15

def number (x : Sig) := let i := hint x; if inputs[i]?=some x then i else 9

theorem listed : inputs.all (fun x => number x==inputs.idxOf x)=true := by decide +kernel

theorem number_ok (x : Sig) : number x=inputs.idxOf x := by
  by_cases mem : x∈inputs
  · exact beq_iff_eq.mp (List.all_eq_true.mp listed x mem)
  · have absent : inputs[hint x]?≠some x := fun eq => mem (List.mem_of_getElem? eq)
    rw [number,if_neg absent,List.idxOf_eq_length mem]
    rfl
end RankedIndex

namespace Inputs
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PublicFloor
open Trace

private lemma live_proper {u target k S} (h : Live u target k S) : ∀ a ∈ S, proper a := by
  induction h using Live.ind with
  | stop hp => simpa using hp
  | binary hd ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩

private lemma bit_zero (i) : bit i zero = false := by simp [bit,zero]

private lemma bit_one (i) : bit i one = true := by unfold bit one; rw [BitVec.getLsbD_allOnes]; simp

private lemma neg_laws : neg zero = one ∧ neg one = zero := by simp [neg,zero,one]

private lemma get_rep {u} (w : List Sig) (i : Nat) : Repr u (w.map (nrm u)) (w.getD i zero) := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact repr_const (Or.inl rfl)
  | some a => exact Or.inl (List.mem_map_of_mem (List.mem_of_getElem? h))

private lemma gate_rep (u : Bool) (w : List Sig) (g : Gate)
    (h : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (mono : u=false → isNot g=false) :
    Repr u (w.map (nrm u)) (gv w g) ∨ (isNot g=false ∧ witness u (w.map (nrm u)) (nrm u (gv w g))) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h
  obtain ⟨ho,hl⟩ := h
  have prim (d : Bool) : Repr u (w.map (nrm u)) ((l.map (fun i => w.getD i zero)).foldr (prime d) (if d then zero else one)) ∨
      witness u (w.map (nrm u)) (nrm u ((l.map (fun i => w.getD i zero)).foldr (prime d) (if d then zero else one))) := by
    have unit (v : Sig) : prime d v (if d then zero else one) = v := by
      apply bit_ext
      intro i
      cases d <;> simp [bit_prime,bit_zero,bit_one]
    cases l with
    | nil => exact Or.inl (repr_const (by cases d <;> simp))
    | cons i l =>
      cases l with
      | nil =>
        simp only [List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,unit]
        exact Or.inl (get_rep w i)
      | cons j l =>
        cases l with
        | cons a l => simp at hl
        | nil =>
          simp only [List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,unit]
          exact prime_rep d (get_rep w i) (get_rep w j)
  rcases ho with rfl | rfl | rfl
  · exact (prim false).imp id (fun h => ⟨rfl,h⟩)
  · exact (prim true).imp id (fun h => ⟨rfl,h⟩)
  · cases u
    · exact absurd (mono rfl) (by simp [isNot])
    left
    cases l with
    | nil => exact repr_const (Or.inr (by simp [gv,neg_laws]))
    | cons i l => exact repr_neg (get_rep w i)

private lemma pull_gate {u target} {w : List Sig} {z : Sig} {k S c} (h : Live u target k S)
    (hz : represented w z ∨ (c=1 ∧ witness u w z)) (sub : ∀ a ∈ S, a ∈ w++[z]) :
    ∃ k' S', k' ≤ k+c ∧ Live u target k' S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k,S,by omega,h,?_⟩
      intro a ha
      have hu : a ∈ w ∨ a = z := by simpa using sub a ha
      rcases hu with hu | rfl
      · exact hu
      · exact hw
    · have hp := live_proper h z hm
      rcases hz with hr | ⟨rfl,d,a,b,hd,ha,hb,pa,pb,hab,eq⟩
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U := S.erase (bin d a b)
        have ht : Live u target k (insert (bin d a b) U) := by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv
          obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf : bin d a b ∉ insert a (insert b U) := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          rcases Finset.mem_insert.mp u with eq | u
          · exact hw (eq.symm ▸ hb)
          · exact hw (hu _ u)
        exact ⟨_,_,Nat.le_refl _,Live.binary hd pa pb hab hf ht,by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k,S,by omega,h,?_⟩
    intro a ha
    have hn : a ≠ z := fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha

private lemma extract {u target} (gs : List Gate) (w : List Sig)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (mono : u=false → ∀ g ∈ gs, isNot g=false)
    (hp : proper target) (hout : target ∈ (execute gs w).map (nrm u)) :
    ∃ k S, k ≤ gs.countP (fun g => !isNot g) ∧ Live u target k S ∧ ∀ a ∈ S, a ∈ w.map (nrm u) := by
  induction gs generalizing w with
  | nil => exact ⟨0,{target},by simp,Live.stop hp,by simpa [execute] using hout⟩
  | cons g gs ih =>
    obtain ⟨k,S,hk,ht,hs⟩ := ih (w++[gv w g]) (fun a ha => legal a (by simp [ha]))
      (fun hu a ha => mono hu a (by simp [ha])) hout
    have rep := gate_rep u w g (legal g (by simp)) (fun hu => mono hu g (by simp))
    rw [List.map_append] at hs
    have rep' : represented (w.map (nrm u)) (nrm u (gv w g)) ∨
        ((if isNot g then 0 else 1)=1 ∧ witness u (w.map (nrm u)) (nrm u (gv w g))) :=
      rep.imp id (fun h => ⟨by simp [h.1],h.2⟩)
    obtain ⟨l,T,hl,hu,hT⟩ := pull_gate ht rep' hs
    refine ⟨l,T,?_,hu,hT⟩
    rw [List.countP_cons]
    cases hn : isNot g <;> simp [hn] at hl ⊢ <;> omega

def cap (u : Bool) : Nat := if u then 14 else 15

def top (u : Bool) : Nat := if u then 63 else 13

def monoTable : Nat := 0x2020002430002840002020002840002c50003060002c50002020000000001c10002430001c10002020002430002020002020002430001c10000000002020001c10002020002020002430002020002840002430002020000000002020002c50003060002c50002840002020001c10001c10002020000000002430002020002020002430002840002020002020002c50002430000000002840002c50003060002c50002430002020003060002020002840000000002840002c50003060002020002430002c50002020002c50002840000000002840002c50002020002020002840002430003060002c5000284000000

def signedTable : Nat := 0x18744d10540c0413c918744d0413c90824ca0c350b0824ca1c644d00000020848e14440c20848e1c644d14440c1c644d1c644d14440c20848e0000001c644d20848e1c644d1c644d14440c1c644d0413c910540c18744d00000018744d0824ca0c350b0824ca0413c91c644d20848e20848e1c644d00000014440c1c644d1c644d14440c0413c918744d18744d0824ca10540c0000000413c90824ca0c350b0824ca10540c18744d0c350b18744d0413c90000000413c90824ca0c350b18744d10540c0824ca18744d0824ca0413c90000000413c90824ca18744d18744d0413c910540c0c350b0824ca0413c9000000

def oldRank (u : Bool) (g : Step) : Nat :=
  if g.2.1 ∈ inputs ∧ g.2.2 ∈ inputs then
    let i := inputs.idxOf g.2.1
    let j := inputs.idxOf g.2.2
    let table := if u then signedTable else monoTable
    min (top u) ((table >>> (6*(36*i+4*j+g.1))) &&& 63)
  else top u

def rank (u : Bool) (g : Step) :=
  let i := RankedIndex.number g.2.1
  let j := RankedIndex.number g.2.2
  if i<9 ∧ j<9 then min (top u) (((if u then signedTable else monoTable) >>> (6*(36*i+4*j+g.1))) &&& 63)
  else top u

theorem rank_eq (u g) : rank u g=oldRank u g := by
  have inside (x : Sig) : inputs.idxOf x<9 ↔ x∈inputs := by
    rw [show (9 : Nat)=inputs.length by rfl,List.idxOf_lt_length_iff]
  simp only [rank,oldRank,RankedIndex.number_ok,inside]

theorem rank_upper (u g) : rank u g ≤ top u := by
  rw [rank_eq]
  unfold oldRank
  split
  · exact Nat.min_le_left _ _
  · exact Nat.le_refl _

theorem rank_last (u g) (h : ¬PrimarySchedule.ready need (fun w => w∈inputs.toFinset) g) :
    rank u g = top u := by
  have missing : ¬(g.2.1 ∈ inputs ∧ g.2.2 ∈ inputs) := by
    intro both
    apply h
    intro v hv
    simp only [need,List.mem_cons,List.not_mem_nil,or_false] at hv
    rcases hv with rfl | rfl
    · exact List.mem_toFinset.mpr both.1
    · exact List.mem_toFinset.mpr both.2
  simp only [rank_eq,oldRank,if_neg missing]

theorem initial (C : Circuit) (legal : FanInTwo C) (computes : circuitFun 9 C=edge)
    (small : C.size≤15) : ∃ u k S, k≤cap u ∧ Live u graph k S ∧ S⊆inputs.toFinset := by
  have goalEq : (execute C.gates inputs).getD C.output zero = graph := by
    apply bit_ext
    intro r
    exact (table_eval C legal C.output r).trans ((congrFun computes (sample r)).trans (edge_table r).symm)
  let gs := C.gates
  have len : gs.length≤15 := small
  have mode : ∃ u : Bool, (u=false → ∀ g∈gs, isNot g=false) ∧ gs.countP (fun g => !isNot g) ≤ cap u := by
    by_cases hn : ∀ g∈gs, isNot g=false
    · exact ⟨false,fun _ => hn,(List.countP_le_length (p:=fun g => !isNot g)).trans len⟩
    · refine ⟨true,by simp,?_⟩
      push Not at hn
      obtain ⟨g,hg,hx⟩ := hn
      have lt : gs.countP (fun g => !isNot g) < gs.length := by
        rcases Nat.lt_or_ge (gs.countP (fun g => !isNot g)) gs.length with h | h
        · exact h
        · have eq := List.countP_eq_length.mp (Nat.le_antisymm List.countP_le_length h) g hg
          simp only [Bool.not_eq_true'] at eq
          exact absurd eq hx
      change _ ≤ 14
      omega
  obtain ⟨u,mono,count⟩ := mode
  have out := get_rep (u:=u) (execute C.gates inputs) C.output
  rw [goalEq] at out
  unfold PEqualNP.Outside.L_meta_670_aux.PublicFloor.Repr at out
  rw [nrm_id (by decide +kernel : bit 0 graph=false)] at out
  have targetIn := out.resolve_right (fun hn => hn graph_proper)
  obtain ⟨k,S,hk,run,hs⟩ := extract gs _ legal mono graph_proper targetIn
  rw [nrm_map (by decide +kernel : inputs.all plainWord=true)] at hs
  exact ⟨u,k,S,hk.trans count,run,fun v hv => List.mem_toFinset.mpr (hs v hv)⟩

def witnesses := graphPairs 511 13438755073

theorem every_input {u k S} (run : Live u graph k S) (sub : S⊆inputs.toFinset) :
    S=inputs.toFinset := by
  apply Finset.Subset.antisymm sub
  intro a ha
  have all : witnesses.map Prod.fst=inputs := by decide +kernel
  have ok : checkEssential graph inputs witnesses=true := by decide +kernel
  rw [←all] at ha
  obtain ⟨r,s,hd,iso⟩ := essential_ok ok a ha
  exact raw_required run inputs a (fun v hv => List.mem_toFinset.mp (sub hv)) r s hd iso

end Inputs

namespace Min
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PublicFloor Trace Inputs

theorem minimum (C : Circuit) (legal : FanInTwo C) (computes : circuitFun 9 C=edge) (small : C.size≤15) :
    ∃ u k, k≤cap u ∧ Ranked u graph (rank u) 0 k inputs.toFinset ∧ Lower u inputs graph k := by
  classical
  obtain ⟨u,t,S,limit,run,sub⟩ := initial C legal computes small
  have yes : ∃ k, Live u graph k inputs.toFinset := ⟨t,every_input run sub ▸ run⟩
  let k := Nat.find yes
  have smallest : ∀ m, Live u graph m inputs.toFinset → k ≤ m := fun m hm => Nat.find_min' yes hm
  have low : Lower u inputs graph k := by
    intro p bank reach found
    have plain : plainWord graph=true := by decide +kernel
    have ins : inputs.all plainWord=true := by decide +kernel
    obtain ⟨m,T,le,tr,inside⟩ := reach_live graph_proper plain ins reach found
    have hs : T⊆inputs.toFinset := fun v hv => List.mem_toFinset.mpr (inside v hv)
    exact (smallest m (every_input tr hs ▸ tr)).trans le
  have first : Live u graph k inputs.toFinset := Nat.find_spec yes
  obtain ⟨m,le,T,inside,tr⟩ := normalize first graph_proper inputs.toFinset (Finset.Subset.refl _)
    (rank u) (top u) (rank_upper u) (rank_last u)
  have eq := every_input (forget tr) inside
  subst T
  have hit : m=k := Nat.le_antisymm le (smallest m (forget tr))
  subst m
  exact ⟨u,k,(smallest t (every_input run sub ▸ run)).trans limit,tr,low⟩
end Min

namespace Moves
open PublicFloor Trace

def ordered (ws : List Sig) := Order.ordered ws

theorem ordered_set (ws : List Sig) : (ordered ws).toFinset=ws.toFinset := by
  ext v
  exact List.mem_toFinset.trans ((Order.permutation ws).mem_iff.trans List.mem_toFinset.symm)

def keep (a b : Sig) (ka kb : Bool) (v : Sig) : Bool := (ka || v != a) && (kb || v != b)

def child (ws : List Sig) (g : Step) (ka kb : Bool) : List Sig :=
  ordered (result g :: ws.filter (keep g.2.1 g.2.2 ka kb))

theorem child_set {ws : List Sig} {g : Step} {U : Finset Sig}
    (start : ws.toFinset=insert g.2.1 (insert g.2.2 U)) :
    (child ws g (decide (g.2.1∈U)) (decide (g.2.2∈U))).toFinset = insert (result g) U := by
  rw [child,ordered_set,List.toFinset_cons]
  congr 1
  ext v
  simp only [List.mem_toFinset,List.mem_filter,keep,Bool.and_eq_true,Bool.or_eq_true,
    decide_eq_true_eq,bne_iff_ne]
  have hw : v∈ws ↔ v=g.2.1 ∨ v=g.2.2 ∨ v∈U := by
    rw [←List.mem_toFinset,start,Finset.mem_insert,Finset.mem_insert]
  rw [hw]
  by_cases a : v=g.2.1 <;> by_cases b : v=g.2.2 <;> simp_all

theorem take_step {u y rank phase k} (ws : List Sig) (run : Ranked u y rank phase (k+1) ws.toFinset) :
    ∃ (g : Step) (ka kb : Bool), good u g ∧ phase≤rank g ∧ g.2.1∈ws ∧ g.2.2∈ws ∧
      result g∉ws ∧ Ranked u y rank (rank g) k (child ws g ka kb).toFinset := by
  obtain ⟨g,U,leg,hi,start,fresh,tail⟩ := run
  refine ⟨g,decide (g.2.1∈U),decide (g.2.2∈U),leg,hi,?_,?_,?_,?_⟩
  · exact List.mem_toFinset.mp (start.symm ▸ Finset.mem_insert_self _ _)
  · exact List.mem_toFinset.mp (start.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  · exact fun h => fresh (List.mem_toFinset.mpr h)
  · simpa only [child_set start] using tail

def mapped (f : Sig → Sig) (g : Step) : Step := (g.1,f g.2.1,f g.2.2)

theorem transport {f : Sig → Sig} (inj : Function.Injective f) (same0 : f zero=zero)
    (same1 : f one=one) (op : ∀ g, f (result g)=result (mapped f g))
    {u y rank} (score : ∀ g, good u g → rank (mapped f g)=rank g)
    {k phase S} (run : Ranked u y rank phase k S) :
    Ranked u (f y) rank phase k (S.image f) := by
  have pp (w : Sig) (h : proper w) : proper (f w) :=
    ⟨fun eq => h.1 (inj (eq.trans same0.symm)),fun eq => h.2 (inj (eq.trans same1.symm))⟩
  induction k generalizing phase S with
  | zero =>
    obtain ⟨rfl,hp⟩ := run
    exact ⟨Finset.image_singleton _ _,pp _ hp⟩
  | succ k ih =>
    obtain ⟨g,U,leg,hi,rfl,fresh,tail⟩ := run
    have fresh' : f (result g) ∉ (insert g.2.1 (insert g.2.2 U)).image f := by
      rintro hx
      obtain ⟨a,ha,eq⟩ := Finset.mem_image.mp hx
      exact fresh (inj eq ▸ ha)
    have after := ih tail
    simp only [Finset.image_insert,op g] at fresh' after ⊢
    refine ⟨mapped f g,U.image f,⟨leg.1,pp _ leg.2.1,pp _ leg.2.2.1,fun eq => leg.2.2.2 (inj eq)⟩,?_,rfl,fresh',?_⟩
    · exact (score g leg).symm ▸ hi
    · simpa only [score g leg] using after
end Moves

namespace Project
open PublicFloor

def wires (raw : List Sig) (gs : List Choice) := gs.map choiceVal ++ raw

def feasible (u : Bool) (raw : List Sig) : List Choice → Prop
  | [] => True
  | g::gs => allowed u g.1 ∧ g.2.1∈wires raw gs ∧ g.2.2∈wires raw gs ∧ feasible u raw gs

def free (u : Bool) (raw : List Sig) (d : Sig) (g : Choice) :=
  availableB u d (g.2.1::g.2.2::raw) (choiceVal g)

def price (u : Bool) (raw : List Sig) (d : Sig) (gs : List Choice) :=
  gs.countP fun g => !(free u raw d g)

theorem attain {u d} {f : Row → Row} {raw roots : List Sig}
    (dom : ∀ r, bit (f r) d=true) (base : poolSupply u f (roots.map observe) raw) (gs : List Choice)
    (good : feasible u raw gs) :
    ∃ bank, Reach u (roots.map observe) (price u raw d gs) bank ∧ poolSupply u f bank (wires raw gs) := by
  induction gs with
  | nil => exact ⟨_,Reach.start,base⟩
  | cons g gs ih =>
    obtain ⟨bank,reach,supply⟩ := ih good.2.2.2
    by_cases skip : free u raw d g=true
    · refine ⟨bank,?_,?_⟩
      · simpa only [price,List.countP_cons,skip,Bool.not_true,Bool.false_eq_true,ite_false,Nat.add_zero] using reach
      · intro w hw
        change w ∈ choiceVal g::wires raw gs at hw
        rcases List.mem_cons.mp hw with rfl|old
        · apply availableB_sound dom _ skip
          intro a ha
          rcases List.mem_cons.mp ha with rfl|ha
          · exact supply _ good.2.1
          · rcases List.mem_cons.mp ha with rfl|original
            · exact supply _ good.2.2.1
            · exact supply _ (List.mem_append_right _ original)
        · exact supply _ old
    · obtain ⟨op,x,y,e,hx,hy,_,_⟩ := comb_prime good.1 (supply _ good.2.1) (supply _ good.2.2.1)
      refine ⟨combine op x y::bank,?_,?_⟩
      · have paid := Reach.two op reach hx hy
        simpa [price,List.countP_cons,show free u raw d g=false from Bool.eq_false_iff.mpr skip] using paid
      · intro w hw
        change w ∈ choiceVal g::wires raw gs at hw
        rcases List.mem_cons.mp hw with rfl|old
        · rw [choiceVal,obs_bin,restrict_comb,e]
          exact Or.inl (List.mem_cons_self ..)
        · exact available_cons _ (supply _ old)

theorem bound {u raw T d L} (slice : Slice u raw T d L) (gs : List Choice) (good : feasible u raw gs)
    {ws : List Sig} (supplied : ∀ w∈ws, w∈wires raw gs) (nd : ws.Nodup)
    {k : Nat} (run : Live u T k ws.toFinset) :
    L + ws.countP (isMaskedConstant d) ≤ k+price u raw d gs := by
  obtain ⟨f,roots,dom,base,nc,lo⟩ := slice
  obtain ⟨bank,hr,hs⟩ := attain dom base gs good
  have covered : supply u bank ((ws.map observe).map (restrictRows f)) := by
    intro v hv
    obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hm
    exact hs _ (supplied w hw)
  have h := projected_bound f (list_run run ws nd rfl) nc hr covered lo
  have c := count_constants dom ws
  omega
end Project

namespace Geometry
open PublicFloor

def covered47 := extendKnown [] 5 [(94,[64,65,66,67,101]),(151,[67,84,101,118]),(227,[16,66,99,116,117,118]),(369,[65,98,115,84,118,135]),(440,[64,97,114,67,84,117,134]),(460,[64,97,66,99,116,133,135])]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cover47 : Known true covered47 :=
  extendKnown_ok (m:=47) baseKnown low47 (by decide +kernel)

def covered63 := extendKnown covered47 8 [(63,[]),(95,[16,66,101]),(159,[32,67,101,118]),(175,[32,83,100,118]),(183,[99,84,118]),(231,[16,66,99,116,117,118]),(317,[32,97,82,83,100,118,135]),(350,[96,33,99,84,117,135]),(359,[16,82,99,116,118,135]),(366,[96,49,116,118,135]),(371,[98,115,84,135]),(377,[48,97,114,99,116,117,118,135]),(429,[80,97,116,134,135]),(430,[96,81,98,83,116,134]),(441,[16,97,114,116,101,134,135]),(444,[96,113,114,99,84,101,134]),(462,[96,98,67,116,133,135]),(492,[96,113,115,132,133,134])]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cover63 : Known true covered63 :=
  extendKnown_ok (m:=63) cover47 low63 (by decide +kernel)

def covered189 := extendKnown covered63 8 [(189,[]),(347,[65,66,115,84,101,118,135]),(486,[16,66,99,132,133,134,135])]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cover189 : Known true covered189 :=
  extendKnown_ok (m:=189) cover63 low189 (by decide +kernel)

def covered127 := extendKnown covered189 9 [(127,[]),(223,[64,65,66,67,117,118]),(247,[115,84]),(375,[98,115,84,135]),(381,[48,113,82,135]),(382,[112,49,66,115,84,101,135]),(415,[48,65,50,67,117,134]),(446,[112,81,114,83,100,134,135]),(478,[112,65,114,67,100,133,135]),(493,[80,113,50,132,135]),(499,[65,114,131,84,134,135]),(505,[64,113,130,131,132,133,135]),(508,[112,129,66,115,84])]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cover127 : Known true covered127 :=
  extendKnown_ok (m:=127) cover189 low127 (by decide +kernel)

def covered191 := extendKnown covered127 11 [(191,[]),(319,[65,50,135]),(351,[64,65,66,67,101,135]),(367,[80,81,66,100,117,118,135]),(379,[81,98,118,135]),(431,[48,65,50,83,100,134,135]),(445,[48,97,82,134]),(487,[16,66,99,132,133,134,135]),(494,[96,65,98,67,132,117,134])]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cover191 : Known true covered191 :=
  extendKnown_ok (m:=191) cover127 low191 (by decide +kernel)

def covered251 := extendKnown covered191 8 [(251,[]),(254,[32,67,117]),(471,[16,66,67,100,133,134,135]),(501,[16,33,50,131,100,133,118]),(506,[32,49,130,100])]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cover251 : Known true covered251 :=
  extendKnown_ok (m:=251) cover191 low251 (by decide +kernel)

def covered255 := extendKnown covered251 12 [(255,[]),(479,[64,65,66,67,133,134,135]),(503,[16,66,131,100,101,135]),(507,[81,130,118]),(509,[48,129,82]),(510,[128,65,130,67,100,117])]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cover255 : Known true covered255 :=
  extendKnown_ok (m:=255) cover251 low255 (by decide +kernel)

def covered383 := extendKnown covered255 13 [(383,[]),(447,[65,50,131,84,118,135]),(495,[80,81,82,83,116,133,118])]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem cover383 : Known true covered383 :=
  extendKnown_ok (m:=383) cover255 low383 (by decide +kernel)

def columns : List ColumnInfo := [(16,0,495,0,13),(64,0,447,0,13),(128,0,383,0,13),(1,0,510,0,12),(2,0,509,0,12),(4,0,507,0,12),(8,0,503,0,12),(32,0,479,0,12),(256,0,255,0,12),(17,0,494,0,11),(24,0,487,0,11),(66,0,445,0,11),(80,0,431,0,11),(132,0,379,0,11),(144,0,367,0,11),(160,0,351,0,11),(192,0,319,0,11),(320,0,191,0,11),(0,16,486,9,10),(0,64,189,258,10),(0,128,347,36,10),(1,16,486,8,9),(2,64,189,256,9),(3,0,508,0,9),(4,128,347,32,9),(6,0,505,0,9),(8,16,486,1,9),(12,0,499,0,9),(18,0,493,0,9),(32,128,347,4,9),(33,0,478,0,9),(65,0,446,0,9),(96,0,415,0,9),(129,0,382,0,9),(130,0,381,0,9),(136,0,375,0,9),(256,64,189,2,9),(264,0,247,0,9),(288,0,223,0,9),(384,0,127,0,9),(0,1,460,50,8),(0,2,440,69,8),(0,4,369,138,8),(0,8,227,276,8),(0,32,94,385,8),(0,256,151,104,8),(5,0,506,0,8),(9,0,486,0,8),(10,0,501,0,8),(36,0,347,0,8),(40,0,471,0,8),(257,0,254,0,8),(258,0,189,0,8),(260,0,251,0,8),(9,16,486,0,8),(19,0,492,0,8),(25,0,486,0,8),(36,128,347,0,8),(49,0,462,0,8),(67,0,444,0,8),(70,0,441,0,8),(81,0,430,0,8),(82,0,429,0,8),(134,0,377,0,8),(140,0,371,0,8),(145,0,366,0,8),(152,0,359,0,8),(161,0,350,0,8),(164,0,347,0,8),(194,0,317,0,8),(258,64,189,0,8),(280,0,231,0,8),(322,0,189,0,8),(328,0,183,0,8),(336,0,175,0,8),(352,0,159,0,8),(416,0,95,0,8),(448,0,63,0,8)]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem all_columns : columns.all (fun c => (varsX (rawMask 511 c) == vars 511) &&
    colCheck 511 c (boundsBefore covered383)) = true := by decide +kernel

theorem restriction (u : Bool) (c : ColumnInfo) (hc : c∈columns) :
    Slice u (vars 511) (graphGoal 511) (subcube c.1 c.2.1) c.2.2.2.2 := by
  obtain ⟨e,checked⟩ := Bool.and_eq_true_iff.mp (List.all_eq_true.mp all_columns c hc)
  have sound := col_sound (u:=u) (m:=511) c _ (before_sound covered383 (known_down cover383)) checked
  rwa [beq_iff_eq.mp e] at sound
end Geometry

namespace Mono
open PublicFloor Project

def subset (p q : Row) := (p.val &&& q.val)=p.val

def increasing (w : Wire Row) := ∀ p q, subset p q → w p=true → w q=true

def better (T mask : Sig) (old proxy : Wire Row) :=
  ∀ r, bit r mask=true → old r=bit r T → proxy r=bit r T

def represents (T mask : Sig) (w v : Wire Row) := increasing v ∧ better T mask w v

def spans (T dom mask : Sig) := ∀ r, bit r dom=true →
  ∃ q, bit q mask=true ∧ bit q T=bit r T ∧ (if bit r T then subset q r else subset r q)

theorem agree {T dom mask} (span : spans T dom mask) {v} (sim : represents T mask (observe T) v)
    (r : Row) (inDom : bit r dom=true) : v r=bit r T := by
  obtain ⟨q,used,tag,le⟩ := span r inDom
  have hit := (sim.2 q used rfl).trans tag
  cases e : bit r T with
  | false =>
    simp only [e,Bool.false_eq_true,ite_false] at le hit
    cases h : v r with
    | false => rfl
    | true => exact False.elim (Bool.noConfusion (hit.symm.trans (sim.1 r q le h)))
  | true =>
    simp only [e,ite_true] at le hit
    exact sim.1 q r le hit

theorem better_trans {T mask a b c} (ab : better T mask a b) (bc : better T mask b c) :
    better T mask a c := fun r hr hit => bc r hr (ab r hr hit)

theorem truth_order : ∀ t a b x y : Bool, (a=t → x=t) → (b=t → y=t) →
    (((a && b)=t → (x && y)=t) ∧ ((a || b)=t → (x || y)=t)) := by decide +kernel

theorem closed {T mask a b x y d} (hd : allowed false d)
    (ax : represents T mask a x) (by' : represents T mask b y) :
    represents T mask (comb d a b) (comb d x y) := by
  have op : d=0 ∨ d=1 := by rcases allowed_four hd with p|p|⟨h,_⟩|⟨h,_⟩ <;> simp_all
  rcases ax with ⟨ix,ax⟩
  rcases by' with ⟨iy,by'⟩
  rcases op with rfl|rfl
  all_goals constructor
  · intro p q le hp
    exact Bool.and_eq_true_iff.mpr ⟨ix p q le (Bool.and_eq_true_iff.mp hp).1,iy p q le (Bool.and_eq_true_iff.mp hp).2⟩
  · intro r hm hr
    specialize ax r hm
    specialize by' r hm
    change (a r && b r)=bit r T at hr
    change (x r && y r)=bit r T
    exact (truth_order _ _ _ _ _ ax by').1 hr
  · intro p q le hp
    rcases Bool.or_eq_true_iff.mp hp with h|h
    · exact Bool.or_eq_true_iff.mpr (Or.inl (ix p q le h))
    · exact Bool.or_eq_true_iff.mpr (Or.inr (iy p q le h))
  · intro r hm hr
    specialize ax r hm
    specialize by' r hm
    change (a r || b r)=bit r T at hr
    change (x r || y r)=bit r T
    exact (truth_order _ _ _ _ _ ax by').2 hr

theorem kept_rel {α β : Type} {rel : α → β → Prop} (k : Bool) {a b xs ys}
    (ab : rel a b) (tail : List.Forall₂ rel xs ys) :
    List.Forall₂ rel (kept k a xs) (kept k b ys) := by
  cases k
  · exact tail
  · exact .cons ab tail

theorem simulate {A B : Type} (rel : Wire A → Wire B → Prop)
    (combineOK : ∀ d, allowed false d → ∀ {a b x y}, rel a x → rel b y → rel (comb d a b) (comb d x y))
    {T k ws} (run : Run false T k ws) :
    ∀ vs, List.Forall₂ rel ws vs → ∃ z, rel T z ∧ Run false z k vs := by
  induction run using Run.ind with
  | stop =>
    intro vs hr
    cases hr with
    | cons head tail =>
      cases tail
      exact ⟨_,head,Run.stop⟩
  | perm p _ ih =>
    intro vs hr
    obtain ⟨l,map,eq⟩ := List.perm_comp_forall₂ p hr
    obtain ⟨z,hit,next⟩ := ih l map
    exact ⟨z,hit,Run.perm eq next⟩
  | @two k a b rest d hd ka kb _ ih =>
    intro vs hr
    cases hr with
    | cons ax rt =>
      cases rt with
      | cons by' last =>
        obtain ⟨z,hit,next⟩ := ih _ (.cons (combineOK d hd ax by') (kept_rel ka ax (kept_rel kb by' last)))
        exact ⟨z,hit,Run.two d hd ka kb next⟩

def dominatesB (T mask c w : Sig) :=
  (((c ^^^ T) &&& ~~~(w ^^^ T)) &&& mask) == zero

theorem dominatesB_ok {T mask c w} (h : dominatesB T mask c w=true) :
    better T mask (observe w) (observe c) := by
  intro r used same
  have test := congrArg (bit r) (beq_iff_eq.mp h)
  change bit r w=bit r T at same
  change bit r c=bit r T
  change bit r (((c ^^^ T) &&& ~~~(w ^^^ T)) &&& mask)=bit r zero at test
  simp only [bit,BitVec.getLsbD_and,BitVec.getLsbD_not,BitVec.getLsbD_xor,r.isLt,
    decide_true,Bool.true_and,zero,BitVec.getLsbD_zero] at test
  change mask.getLsbD r.val=true at used
  change w.getLsbD r.val=T.getLsbD r.val at same
  change c.getLsbD r.val=T.getLsbD r.val
  cases tc : T.getLsbD r.val <;> cases cc : c.getLsbD r.val <;> simp_all

def backed (T mask : Sig) (f : Row → Row) (bank : List (Wire Row)) (w : Sig) :=
  ∃ v, represents T mask (observe w) v ∧ Available false bank (restrictRows f v)

theorem constant_rep {T mask w : Sig} {b : Bool}
    (eq : ∀ r, bit r mask=true → bit r w=b) :
    represents T mask (observe w) (fun _ => b) := by
  refine ⟨fun _ _ _ h => h,?_⟩
  intro r hm hr
  exact (eq r hm).symm.trans hr

theorem masked_const {mask w} (h : isMaskedConstant mask w=true) :
    ∃ b : Bool, ∀ r, bit r mask=true → bit r w=b := by
  rcases Bool.or_eq_true_iff.mp h with eq|eq
  · refine ⟨false,fun r seen => ?_⟩
    have he := congrArg (bit r) (beq_iff_eq.mp eq)
    change bit r (masked mask w)=bit r zero at he
    rw [show bit r zero=false by simp [bit,zero]] at he
    simpa only [masked,bit,BitVec.getLsbD_and,show mask.getLsbD r.val=true from seen,
      Bool.and_true] using he
  · refine ⟨true,fun r seen => ?_⟩
    have he := congrArg (bit r) (beq_iff_eq.mp eq)
    change bit r (masked mask w)=bit r mask at he
    simpa only [masked,bit,BitVec.getLsbD_and,show mask.getLsbD r.val=true from seen,Bool.and_true] using he

theorem replacements {T mask f bank} (ws : List Sig) (cover : ∀ w∈ws, backed T mask f bank w) :
    ∃ vs, List.Forall₂ (represents T mask) (ws.map observe) vs ∧
      supply false bank (vs.map (restrictRows f)) ∧
      ws.countP (isMaskedConstant mask) ≤ mass (vs.map (restrictRows f)) := by
  induction ws with
  | nil => exact ⟨[],.nil,by simp [supply],Nat.zero_le _⟩
  | cons w ws ih =>
    obtain ⟨vs,rel,avail,le⟩ := ih (fun x hx => cover x (List.mem_cons_of_mem _ hx))
    have build (v : Wire Row) (represent : represents T mask (observe w) v)
        (a : Available false bank (restrictRows f v))
        (bound : (isMaskedConstant mask w).toNat ≤ cost (restrictRows f v)) :
        ∃ vs', List.Forall₂ (represents T mask) ((w::ws).map observe) vs' ∧
        supply false bank (vs'.map (restrictRows f)) ∧
        (w::ws).countP (isMaskedConstant mask) ≤ mass (vs'.map (restrictRows f)) := by
      refine ⟨v::vs,.cons represent rel,?_,?_⟩
      · intro t ht
        rcases List.mem_cons.mp ht with rfl|old
        · exact a
        · exact avail _ old
      · simp only [List.map_cons,mass_cons,List.countP_cons]
        cases tag : isMaskedConstant mask w <;> simp [tag] at bound ⊢ <;> omega
    cases h : isMaskedConstant mask w with
    | false =>
      obtain ⟨v,rep,cert⟩ := cover w (List.mem_cons_self ..)
      exact build v rep cert (by simp [h])
    | true =>
      obtain ⟨b,eq⟩ := masked_const h
      have con : Constant (restrictRows f (fun _ => b)) := ⟨b,rfl⟩
      exact build _ (constant_rep eq) (Or.inr (Or.inl con)) (by classical simp [h,cost,con])

theorem boundary_bound {T dom mask L} (span : spans T dom mask)
    (ws : List Sig) (nd : ws.Nodup) {k} (run : Live false T k ws.toFinset)
    {f : Row → Row} {roots bank : List (Wire Row)} {p}
    (inside : ∀ r, bit (f r) dom=true) (nc : ¬Constant (restrictRows f (observe T)))
    (lower : ∀ q bs, Reach false roots q bs → Available false bs (restrictRows f (observe T)) → L≤q)
    (paid : Reach false roots p bank) (cover : ∀ w∈ws, backed T mask f bank w) :
    L+ws.countP (isMaskedConstant mask) ≤ k+p := by
  obtain ⟨vs,rel,avail,le⟩ := replacements ws cover
  obtain ⟨out,hit,trace⟩ := simulate _ (fun _ hd _ _ _ _ => closed hd) (list_run run ws nd rfl) vs rel
  have target : restrictRows f out=restrictRows f (observe T) := by
    funext r
    exact agree span hit _ (inside r)
  have nc' : ¬Constant (restrictRows f out) := target.symm ▸ nc
  have low : ∀ q bs, Reach false roots q bs → Available false bs (restrictRows f out) → L≤q := target.symm ▸ lower
  have costBound := projected_bound f trace nc' paid avail low
  omega
end Mono

namespace Mono
open PublicFloor Project

def reused (T mask : Sig) (pool : List Sig) (g : Choice) :=
  (zero::one::pool).any fun w => dominatesB T mask w (choiceVal g)

def paidCount (T mask : Sig) (raw : List Sig) : List Choice → Nat
  | [] => 0
  | g::gs => paidCount T mask raw gs + (!(reused T mask (wires raw gs) g)).toNat

theorem backed_const {T mask f bank w} {b : Bool} (eq : observe w = fun _ => b) :
    backed T mask f bank w := by
  refine ⟨fun _ => b,constant_rep (fun r _ => congrFun eq r),Or.inr (Or.inl ⟨b,rfl⟩)⟩

theorem build {T mask : Sig} {f : Row → Row} {raw roots : List Sig}
    (mono : ∀ w ∈ raw, increasing (observe w)) (base : poolSupply false f (roots.map observe) raw)
    (gs : List Choice) (legal : feasible false raw gs) : ∃ bank,
    Reach false (roots.map observe) (paidCount T mask raw gs) bank ∧
      ∀ w ∈ wires raw gs, backed T mask f bank w := by
  induction gs with
  | nil => exact ⟨_,Reach.start,fun w hw => ⟨observe w,⟨mono w hw,fun _ _ e => e⟩,base w hw⟩⟩
  | cons g gs ih =>
    obtain ⟨bank,reach,sup⟩ := ih legal.2.2.2
    cases skip : reused T mask (wires raw gs) g with
    | true =>
      obtain ⟨w,mem,dom⟩ := List.any_eq_true.mp skip
      have sample : backed T mask f bank w := by
        rcases List.mem_cons.mp mem with rfl|mem
        · apply backed_const (b:=false)
          funext r
          simp [observe,bit,zero]
        · rcases List.mem_cons.mp mem with rfl|mem
          · apply backed_const (b:=true)
            funext r
            change (BitVec.allOnes 512).getLsbD r.val=true
            rw [BitVec.getLsbD_allOnes]
            simp
          · exact sup _ mem
      obtain ⟨v,⟨inc,beats⟩,known⟩ := sample
      refine ⟨bank,by simpa only [paidCount,skip,Bool.not_true,Bool.toNat_false,Nat.add_zero] using reach,?_⟩
      intro a ha
      change a∈choiceVal g::wires raw gs at ha
      rcases List.mem_cons.mp ha with rfl|ha
      · exact ⟨v,⟨inc,better_trans (dominatesB_ok dom) beats⟩,known⟩
      · exact sup a ha
    | false =>
      obtain ⟨x,xr,xa⟩ := sup _ legal.2.1
      obtain ⟨y,yr,ya⟩ := sup _ legal.2.2.1
      let z := comb g.1 x y
      have rz : represents T mask (observe (choiceVal g)) z := by
        rw [choiceVal,obs_bin]
        exact closed legal.1 xr yr
      have head : Reach false (roots.map observe) (paidCount T mask raw gs+1) (restrictRows f z::bank) := by
        have code : g.1=0 ∨ g.1=1 := by
          rcases allowed_four legal.1 with eq|eq|⟨h,_⟩|⟨h,_⟩ <;> simp_all
        change Reach false _ _ (restrictRows f (comb g.1 x y)::bank)
        rw [restrict_comb]
        rcases code with h|h
        · rw [h]
          exact Reach.two false reach xa ya
        · rw [h]
          exact Reach.two true reach xa ya
      refine ⟨_,by simpa only [paidCount,skip,Bool.not_false,Bool.toNat_true] using head,?_⟩
      intro w hw
      change w∈choiceVal g::wires raw gs at hw
      rcases List.mem_cons.mp hw with rfl|old
      · exact ⟨z,rz,Or.inl (List.mem_cons_self ..)⟩
      · obtain ⟨w',better,known⟩ := sup _ old
        exact ⟨w',better,available_cons _ known⟩

theorem projected {raw T dom L mask} (slice : Slice false raw T dom L) (span : spans T dom mask)
    (mono : ∀ w∈raw, increasing (observe w)) (gs : List Choice) (legal : feasible false raw gs)
    {k : Nat} {ws : List Sig} (supply : ∀ w∈ws, w∈wires raw gs) (nd : ws.Nodup) (run : Live false T k ws.toFinset) :
    L+ws.countP (isMaskedConstant mask) ≤ k+paidCount T mask raw gs := by
  obtain ⟨f,roots,inside,base,nc,lower⟩ := slice
  obtain ⟨bank,paid,back⟩ := build (T:=T) (mask:=mask) mono base gs legal
  exact boundary_bound span ws nd run inside nc lower paid (fun w hw => back w (supply w hw))

theorem increasing_inputs (w : Sig) (hw : w∈inputs) : increasing (observe w) := by
  rw [←input_list] at hw
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hw
  intro p q subset trueP
  change bit p (inputs.getD i.val zero)=true at trueP
  change bit q (inputs.getD i.val zero)=true
  rw [input_coords] at trueP ⊢
  have e := congrArg (fun n : Nat => n.testBit i.val) subset
  change (p.val &&& q.val).testBit i.val=p.val.testBit i.val at e
  simpa only [Nat.testBit_and,trueP,Bool.true_and] using e
end Mono

namespace Borders
abbrev W := BitVec 512

abbrev Entry := W × W

def chunks : Array Nat := #[0x40200001048,0x11000000024,0x100000410,0x200,0x100000120,0x1,0x6,0x0,0x14040201021048,0x100000610,0x100100120,0x40002,0x4040201021048,0x10010000000224,0x100140120,0x4040001001040,0x10010000000004,0x10100,0x100100100,0x40000,0x201021000,0x10010000000020,0x100000010,0x10200,0x10002,0x4040201020008,0x1010000000004,0x100000400,0x100000100,0x4000200020048,0x10000000000024,0x100100020,0x1021048,0x100024,0x410,0x100120,0x10010000000024,0x100040410,0x40000001040,0x11000000004,0x100,0x100000110,0x4,0x600000048,0x1000000024,0x2,0x100000020,0x10010201021000,0x100000210,0x41200001048,0x1010000000204,0x100040102,0x11000000224,0x100000124,0x1021448,0x100224,0x140120,0x14040201021248,0x14040201021068,0x100040610,0x4000001420000,0x10000000040000,0x1000000100000,0x10000,0x10010201021024,0x100010210,0x101020418,0x10204,0x40102,0x4000001400000,0x10010201021020,0x1001000,0x10010000000000,0x101020408,0x201020000,0x1010000000000,0x100000000,0x4000000420000,0x4000200020008,0x1000000000004,0x200001000,0x11000000020,0x1020418,0x1001040,0x100004,0x100100,0x14040001001040,0x610,0x100140100,0x10010000000220,0x100140020,0x100040010,0x40410,0x200022008,0x20,0x220,0x4040004000048,0x400000400,0x2000201040,0x10000000000020,0x10,0x1000100020,0x60001001800,0x10000000400,0x104144200000000,0x10010400000000,0x100120168,0x40012,0x4040001000000,0x4000000000040,0x10000000000004,0x100100000,0x200020000,0x1020008,0x400,0x20048,0x100020,0x100040400,0x4000000400000,0x1000,0x11000000000,0x400000040,0x1000000004,0x1020408,0x1040,0x14,0x110,0x10010001001000,0x1010201020000,0x100000200,0x41000001040,0x11200001000,0x1010000000200,0x100010102,0x1000000000006,0x100040002,0x100000114,0x100000024,0x1001440,0x100104,0x140100,0x10010201021200,0x100000014,0x14000200020068,0x100040012,0x41200001068,0x1121068,0x40610,0x1061448,0x14040201021268]

def selectors : Array Nat := #[0x100706050403020100,0x40070b070a07090708,0x800707050e07070d0c,0x1071305121102100f,0x20718050a17161514,0x4070b051c171b1a19,0x8070b051f18161e1d,0x20070b052317222120,0x100070707071725240c,0x11072a052928022726,0x180706052e2d162c2b,0x420718070a0730072f,0x500706070407090731,0x840707053307073219,0x900707053507073400,0xa00707053807073736,0xc00707070e07070739,0x14007070707073b073a,0x200007133f3e3f3e3d3c,0x80000707050741074007,0x100000544070743420707,0x200107133f3e3f3e3d45,0x80020707050741074607,0x3073f051211164847,0x100040544070743490707,0x60718051c174c4b4a,0x200807133f3e3f3e3d4d,0xc070b054c184c4f4e,0x12072d050403165150,0x100200544070743520707,0x210713055511225453,0x410713071207020756,0x60070b072307570720,0x81070705580707100f,0x820707050a07075914,0x880707055a07071e1d,0x81000707070741074007,0x10807070707185b1e1d,0x12007070707175c2120,0x1800707070707070d0c,0x200072d2d5f035e5e5d,0x4000713076107612a60,0x8000707646507646362,0x10000707072803676766,0x40000707074c074c6968,0x20000076b056a07070707,0x50713051c111b1a6c,0x90713056f3f166e6d,0xa0718051f18166370,0x24070b052817722a71,0x28070b057418642173,0x101070707071125100f,0x1020707070717161514,0x1040707070717751a19,0x200907133f3e3f3e3d76,0x130705052928167877,0x19072a051605167a79,0x1002405440707437b0707,0x31072a057e28227d7c,0x43073f07120729077f,0x460718071c07810780,0x51072a072907020782,0x52072d070407300783,0x86070705850707844a,0x8c070705870707864e,0x910707058807072726,0x980707058907072c2b,0xa10707058c07078b8a,0xa4070705440707437b,0xc20707070a0707078d,0x81020707070741074607,0x118070707072d8e2c2b,0x1420707070707410746,0x148070707070790078f,0x1500707070707090791,0x1600707070707930792,0x1a00707070707073794,0x1c00707070707070795,0x70b050a1702240c]

def readMask : Nat → Nat → Nat
  | 0,_ => 0
  | n+1,c => (chunks[c &&& 255]?.getD 0) ||| (readMask n (c>>>8) <<<64)

def entry (i : Nat) : Entry :=
  let c := selectors[i]?.getD 0
  (PublicFloor.subcube ((c>>>64) &&& 511) (c>>>73),BitVec.ofNat 512 (readMask 8 c))

def target : W := 0xfffffffffffffffffffffffffffafff8ffffffffffffffffffffffffffeaffc8fffffffffffefcfcfffffffffffaf8f8ffeefeeeffeefcccffeafaeaffeaf8c8

def mask (e : Entry) : W := e.2

def positions : Nat → Nat → List Nat
  | 0,_ => []
  | n+1,x => if x=0 then [] else let i := x.log2; i::positions n (x ^^^ (1<<<i))

def inside (old new : Nat) := (old &&& new)==old

def spansB (e : Entry) : Bool :=
  let m := mask e
  let rows := positions 64 m.toNat
  (List.range 512).all fun r => !(e.1.getLsbD r) || rows.any fun q =>
    (decide (q<512) && m.getLsbD q) && (target.getLsbD q == target.getLsbD r) &&
      (if target.getLsbD r then inside q r else inside r q)

theorem witness {e} (ok : spansB e=true) (r : Fin 512) (hr : e.1.getLsbD r.val=true) :
    ∃ q : Fin 512, (mask e).getLsbD q.val=true ∧ target.getLsbD q.val=target.getLsbD r.val ∧
      (if target.getLsbD r.val then (q.val &&& r.val)=q.val else (r.val &&& q.val)=r.val) := by
  have row := List.all_eq_true.mp ok r.val (List.mem_range.mpr r.isLt)
  simp only [hr,Bool.not_true,Bool.false_or,List.any_eq_true] at row
  obtain ⟨q,_,tests⟩ := row
  simp only [Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq] at tests
  obtain ⟨⟨⟨n,hm⟩,same⟩,order⟩ := tests
  refine ⟨⟨q,n⟩,hm,same,?_⟩
  cases label : target.getLsbD r.val <;> simpa only [label,ite_false,ite_true,Bool.false_eq_true,inside,beq_iff_eq] using order

def part0 := (List.range' 0 6).map entry

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem good0 : part0.all spansB=true := by decide +kernel

def part1 := (List.range' 6 6).map entry

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem good1 : part1.all spansB=true := by decide +kernel

def part2 := (List.range' 12 6).map entry

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem good2 : part2.all spansB=true := by decide +kernel

def part3 := (List.range' 18 6).map entry

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem good3 : part3.all spansB=true := by decide +kernel

def part4 := (List.range' 24 6).map entry

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem good4 : part4.all spansB=true := by decide +kernel

def part5 := (List.range' 30 6).map entry

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem good5 : part5.all spansB=true := by decide +kernel

def part6 := (List.range' 36 6).map entry

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem good6 : part6.all spansB=true := by decide +kernel

def part7 := (List.range' 42 6).map entry

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem good7 : part7.all spansB=true := by decide +kernel

def part8 := (List.range' 48 6).map entry

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem good8 : part8.all spansB=true := by decide +kernel

def part9 := (List.range' 54 6).map entry

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem good9 : part9.all spansB=true := by decide +kernel

def part10 := (List.range' 60 6).map entry

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem good10 : part10.all spansB=true := by decide +kernel

def part11 := (List.range' 66 6).map entry

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem good11 : part11.all spansB=true := by decide +kernel

def part12 := (List.range' 72 6).map entry

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem good12 : part12.all spansB=true := by decide +kernel

def part13 := (List.range' 78 1).map entry

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem good13 : part13.all spansB=true := by decide +kernel

def regions : List Entry := part0 ++ part1 ++ part2 ++ part3 ++ part4 ++ part5 ++ part6 ++ part7 ++ part8 ++ part9 ++ part10 ++ part11 ++ part12 ++ part13

theorem all_checked : regions.all spansB=true := by
  simp only [regions,List.all_append,good0,good1,good2,good3,good4,good5,good6,good7,good8,good9,good10,good11,good12,good13,Bool.and_self]
end Borders

namespace Atlas
open PublicFloor Geometry

def col (i : Nat) : ColumnInfo := columns.getD i (0,0,0,0,0)

def region (i : Nat) : Borders.Entry := Borders.entry i

def domain (i : Nat) : Sig := (region i).1

def border (i : Nat) : Sig := Borders.mask (region i)

def lower (m i : Nat) := if i=78 then m else (col i).2.2.2.2

def aligns (i : Nat) :=
  Borders.regions.contains (region i) &&
  (if i=78 then domain i == one else columns.contains (col i) && domain i == subcube (col i).1 (col i).2.1)

set_option maxRecDepth 8000 in
set_option maxHeartbeats 0 in
theorem alignments : (List.range 79).all aligns=true := by decide +kernel

theorem aligned (i : Fin 79) : region i ∈ Borders.regions ∧
    (if i.val=78 then domain i=one else col i∈columns ∧ domain i=subcube (col i).1 (col i).2.1) := by
  have hit := List.all_eq_true.mp alignments i.val (List.mem_range.mpr i.isLt)
  obtain ⟨mem,rest⟩ := Bool.and_eq_true_iff.mp hit
  refine ⟨List.contains_iff_mem.mp mem,?_⟩
  by_cases h : i.val=78
  · rw [if_pos h] at rest ⊢
    exact beq_iff_eq.mp rest
  · rw [if_neg h] at rest ⊢
    simpa only [Bool.and_eq_true,List.contains_iff_mem,beq_iff_eq] using rest

theorem geometry {u m} (low : Lower u inputs graph m) (i : Fin 79) :
    Slice u inputs graph (domain i) (lower m i) ∧ Mono.spans graph (domain i) (border i) := by
  obtain ⟨mem,other⟩ := aligned i
  constructor
  · by_cases last : i.val=78
    · rw [if_pos last] at other
      rw [other,lower,if_pos last]
      exact slice_self graph_proper low
    · rw [if_neg last] at other
      rw [other.2,lower,if_neg last]
      have h := restriction u (col i) other.1
      have eq : vars 511=inputs := by decide +kernel
      have target : graphGoal 511=graph := by decide +kernel
      rwa [eq,target] at h
  · have hit := List.all_eq_true.mp Borders.all_checked _ mem
    have target : Borders.target=graph := by decide +kernel
    intro r hr
    obtain ⟨q,inMask,label,order⟩ := Borders.witness hit r hr
    rw [target] at label order
    exact ⟨q,inMask,label,order⟩
end Atlas

namespace Cuts
open PublicFloor Atlas Project

def feasibleB (u : Bool) (raw : List Sig) : List Choice → Bool
  | [] => true
  | g::gs => (allowedB u g.1 && (wires raw gs).contains g.2.1 && (wires raw gs).contains g.2.2) &&
      feasibleB u raw gs

theorem feasible_ok {u raw gs} (ok : feasibleB u raw gs=true) : feasible u raw gs := by
  induction gs with
  | nil => trivial
  | cons c gs ih =>
    simp only [feasibleB,Bool.and_eq_true,List.contains_iff_mem] at ok
    exact ⟨allowedB_ok ok.1.1.1,ok.1.1.2,ok.1.2,ih ok.2⟩

theorem feasible_yes {u raw gs} (ok : feasible u raw gs) : feasibleB u raw gs=true := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    have legal : allowedB u g.1=true := by
      simpa only [allowedB,allowed,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq] using ok.1
    simp only [feasibleB,Bool.and_eq_true,List.contains_iff_mem]
    exact ⟨⟨⟨legal,ok.2.1⟩,ok.2.2.1⟩,ih ok.2.2.2⟩

def certified (u : Bool) (s : Load.Board) :=
  let (_,ws,gs) := s
  feasibleB u inputs gs && decide ws.Nodup && ws.all (wires inputs gs).contains

theorem extend {u phase phase'} {ws : List Sig} {gs : List Choice} {g : Choice} {ka kb : Bool}
    (parent : certified u (phase,ws,gs)=true) (legal : allowed u g.1)
    (a : g.2.1∈ws) (b : g.2.2∈ws) (fresh : choiceVal g∉ws) :
    certified u (phase',Moves.child ws g ka kb,g::gs)=true := by
  simp only [certified,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true,List.contains_iff_mem] at parent ⊢
  obtain ⟨⟨earlier,nd⟩,has⟩ := parent
  have perm := Order.permutation (Trace.result g::ws.filter (Moves.keep g.2.1 g.2.2 ka kb))
  refine ⟨⟨feasible_yes ⟨legal,has _ a,has _ b,feasible_ok earlier⟩,?_⟩,?_⟩
  · apply perm.nodup_iff.mpr
    exact List.nodup_cons.mpr ⟨fun mem => fresh (List.mem_of_mem_filter mem),nd.filter _⟩
  · intro w hw
    rcases List.mem_cons.mp (perm.mem_iff.mp hw) with rfl|pre
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (has _ (List.mem_of_mem_filter pre))

def check (u : Bool) (cap : Nat) (s : Load.Board) (i : Fin 79) :=
  let (_,ws,gs) := s
  let price := if u then price true inputs (domain i) gs else Mono.paidCount graph (border i) inputs gs
  let mask := if u then domain i else border i
  if i.val=78 then decide (price < gs.length + ws.countP (isMaskedConstant mask))
  else decide (cap + price < lower 0 i + ws.countP (isMaskedConstant mask))

theorem exclude {u T cap s} (low : Lower u inputs graph T) (safe : certified u s=true)
    (i : Fin 79) (bad : check u cap s i=true) {k : Nat} (le : k≤cap) (exactSize : s.2.2.length+k=T) :
    ¬ Live u graph k s.2.1.toFinset := by
  rcases s with ⟨phase,ws,gs⟩
  intro run
  change gs.length+k=T at exactSize
  simp only [certified,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true,List.contains_iff_mem] at safe
  have good := feasible_ok safe.1.1
  obtain ⟨slice,span⟩ := geometry low i
  cases u with
  | false =>
    have bound := Mono.projected slice span Mono.increasing_inputs gs good safe.2 safe.1.2 run
    by_cases last : i.val=78
    · simp only [check,Bool.false_eq_true,ite_false,last,ite_true,decide_eq_true_eq] at bad
      simp only [lower,last,if_true] at bound
      omega
    · simp only [check,Bool.false_eq_true,ite_false,lower,last,if_false,decide_eq_true_eq] at bad bound
      omega
  | true =>
    have bound := Project.bound slice gs good safe.2 safe.1.2 run
    by_cases last : i.val=78
    · simp only [check,ite_true,last,decide_eq_true_eq] at bad
      simp only [lower,last,if_true] at bound
      omega
    · simp only [check,ite_true,lower,last,if_false,decide_eq_true_eq] at bad bound
      omega
end Cuts

namespace RootPins
open PublicFloor
open Geometry

def pairLost (u : Bool) (ws : List Sig) (p q : Row) : Bool :=
  bit p graph && !(bit q graph) && ws.all fun w =>
    if u then bit p w == bit q w else !(bit p w) || bit q w

theorem pairLost_sound {u ws p q} (h : pairLost u ws p q=true) (k : Nat) :
    Impossible u graph k ws.toFinset := by
  intro l _ run
  simp only [pairLost,Bool.and_eq_true,Bool.not_eq_true',List.all_eq_true] at h
  obtain ⟨⟨yes,no⟩,all⟩ := h
  cases u with
  | false =>
    obtain ⟨a,ha,atP,atQ⟩ := mono_row_difference run rfl yes no
    simpa [atP,atQ] using all a (List.mem_toFinset.mp ha)
  | true =>
    have diff : bit p graph ≠ bit q graph := by simp [yes,no]
    obtain ⟨a,ha,bad⟩ := live_row_difference run diff
    exact bad (beq_iff_eq.mp (all a (List.mem_toFinset.mp ha)))
end RootPins

namespace KW
open PublicFloor
open Family (gate boolGate gate_bit)

def legalLabels (y : Sig) (S : Finset Sig) (label : Nat → Nat → Sig) (polarity : Sig → Bool) :=
  ∀ p q, y.getLsbD p=true → y.getLsbD q=false →
    label p q∈S ∧ (label p q).getLsbD p=polarity (label p q) ∧
      (label p q).getLsbD q= !(polarity (label p q))

def rectangles (y : Sig) (label : Nat → Nat → Sig) :=
  ∀ p p' q q', y.getLsbD p=true → y.getLsbD p'=true → y.getLsbD q=false →
    y.getLsbD q'=false → label p q'=label p' q → label p q=label p q'

def hasLabels (signed : Bool) (y : Sig) (S : Finset Sig) :=
  ∃ label polarity, legalLabels y S label polarity ∧ rectangles y label ∧
    (signed=false → ∀ w, polarity w=true)

def left (u v r ap aq : Bool) :=
  let side := if r==(u && v) then ap else aq
  (side ^^ (u && !v)) == (u && v)

lemma selects : ∀ u v r ap bp aq bq : Bool, boolGate u v ap bp=r → boolGate u v aq bq= !r →
    (if left u v r ap aq then (ap=(r ^^ (u && !v)) ∧ aq= !(r ^^ (u && !v)))
    else (bp=(r ^^ (v && !u)) ∧ bq= !(r ^^ (v && !u)))) := by decide +kernel

def pivot (u v r : Bool) (a b : Sig) (p q : Nat) :=
  if left u v r (a.getLsbD p) (a.getLsbD q) then a else b

theorem split {signed y U a b u v} (aU : a∉U) (bU : b∉U) (ne : a≠b)
    (sameSign : signed=false → u=v) (c : hasLabels signed y (insert (gate u v a b) U)) :
    hasLabels signed y (insert a (insert b U)) := by
  obtain ⟨label,polarity,legal,rectangle,pure⟩ := c
  let z := gate u v a b
  let r := polarity z
  let lab := fun p q => if label p q=z then pivot u v r a b p q else label p q
  let pol := fun w => if w=a then r ^^ (u && !v) else if w=b then r ^^ (v && !u) else polarity w
  let origin := fun w : Sig => if w=a ∨ w=b then z else w
  have back (p q : Nat) (hp : y.getLsbD p=true) (hq : y.getLsbD q=false) :
      origin (lab p q)=label p q := by
    have mem := (legal p q hp hq).1
    change label p q ∈ insert z U at mem
    by_cases eq : label p q=z
    · simp only [lab,eq,ite_true,origin,pivot]
      split <;> simp
    · have old := (Finset.mem_insert.mp mem).resolve_left eq
      have no : ¬(label p q=a ∨ label p q=b) := by
        rintro (h|h)
        · exact aU (h ▸ old)
        · exact bU (h ▸ old)
      simp only [lab,if_neg eq,origin,if_neg no]
  refine ⟨lab,pol,?_,?_,?_⟩
  · intro p q hp hq
    obtain ⟨mem,pp,nn⟩ := legal p q hp hq
    change label p q ∈ insert z U at mem
    by_cases eq : label p q=z
    · rw [eq] at pp nn
      have pGate : boolGate u v (a.getLsbD p) (b.getLsbD p)=r := (gate_bit u v a b p).symm.trans pp
      have qGate : boolGate u v (a.getLsbD q) (b.getLsbD q)= !r := (gate_bit u v a b q).symm.trans nn
      have sel := selects _ _ _ _ _ _ _ pGate qGate
      cases pick : left u v r (a.getLsbD p) (a.getLsbD q) <;>
        simp only [lab,if_pos eq,pivot,pick,ite_true,Bool.false_eq_true,ite_false,pol,ne.symm] at sel ⊢
      · exact ⟨Finset.mem_insert_of_mem (Finset.mem_insert_self _ _),sel⟩
      · exact ⟨Finset.mem_insert_self _ _,sel⟩
    · have old := (Finset.mem_insert.mp mem).resolve_left eq
      have na : label p q ≠ a := fun h => aU (h ▸ old)
      have nb : label p q ≠ b := fun h => bU (h ▸ old)
      simp only [lab,if_neg eq,pol,if_neg na,if_neg nb]
      exact ⟨Finset.mem_insert_of_mem (Finset.mem_insert_of_mem old),pp,nn⟩
  · intro p p' q q' hp hp' hq hq' agree
    have same := congrArg origin agree
    change origin (lab p q')=origin (lab p' q) at same
    rw [back p q' hp hq',back p' q hp' hq] at same
    have center := rectangle p p' q q' hp hp' hq hq' same
    by_cases hit : label p q'=z
    · have diag := center.trans hit
      have other := same.symm.trans hit
      simp only [lab,if_pos hit,if_pos diag,if_pos other,pivot,left] at agree ⊢
      by_cases phase : (r==(u && v))=true
      · simp only [if_pos phase]
      · simp only [if_neg phase] at agree ⊢
        exact agree.symm
    · have miss : label p q≠z := fun h => hit (center.symm.trans h)
      simpa only [lab,if_neg hit,if_neg miss] using center
  · intro mono w
    have equal := sameSign mono
    subst v
    have off : (u && !u)=false := by cases u <;> rfl
    have high : r=true := pure mono z
    simp [pol,off,high,pure mono]

theorem labels_of_tight {u y k S} (run : Live u y k S) (width : k+1≤S.card) : hasLabels u y S := by
  induction k generalizing S with
  | zero =>
    obtain ⟨rfl,_⟩ := run
    exact ⟨fun _ _ => y,fun _ => true,fun _ _ hp hq => ⟨Finset.mem_singleton_self _,hp,hq⟩,
      fun _ _ _ _ _ _ _ _ _ => rfl,fun _ _ => rfl⟩
  | succ k ih =>
    obtain ⟨U,a,b,d,op,rfl,_,_,ne,fresh,tail⟩ := run
    have hz : bin d a b∉U := fun h => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
    have lim := live_size tail
    rw [Finset.card_insert_of_notMem hz] at lim
    have upper := Finset.card_insert_le a (insert b U)
    have lower_ := Finset.card_insert_le b U
    have aU : a∉U := by
      intro ha
      rw [Finset.insert_eq_of_mem (Finset.mem_insert_of_mem ha : a∈insert b U)] at width
      omega
    have bU : b∉U := by
      intro hb
      rw [Finset.insert_eq_of_mem hb] at width upper
      omega
    have later := ih tail (by rw [Finset.card_insert_of_notMem hz]; omega)
    rcases allowed_four op with rfl|rfl|⟨su,rfl⟩|⟨su,rfl⟩
    · exact split (u:=false) (v:=false) aU bU ne (fun _ => rfl) later
    · exact split (u:=true) (v:=true) aU bU ne (fun _ => rfl) later
    · exact split (u:=false) (v:=true) aU bU ne (by simp [su]) later
    · exact split (u:=true) (v:=false) aU bU ne (by simp [su]) later

def separates (u : Bool) (p q : Nat) (w : Sig) :=
  if u then w.getLsbD p != w.getLsbD q else w.getLsbD p && !w.getLsbD q

def forces (u : Bool) (y : Sig) (ws : List Sig) (p q : Nat) (x : Sig) :=
  y.getLsbD p && !y.getLsbD q && ws.all (fun w => !(separates u p q w) || w==x)

abbrev Hit := Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat

def test (u : Bool) (y : Sig) (ws : List Sig) (e : Hit) :=
  let (i,j,p,q,pa,qa,pb,qb) := e
  let a := ws.getD i zero
  let b := ws.getD j zero
  a != b && forces u y ws p qa a && forces u y ws pa q a &&
    forces u y ws p qb b && forces u y ws pb q b

theorem forced_label {u y p q x label polarity} {ws : List Sig} (good : legalLabels y ws.toFinset label polarity)
    (pure : u=false → ∀ w, polarity w=true) (cert : forces u y ws p q x=true) :
    y.getLsbD p=true ∧ y.getLsbD q=false ∧ label p q=x := by
  simp only [forces,Bool.and_eq_true,Bool.not_eq_true'] at cert
  obtain ⟨⟨hp,hq⟩,all_⟩ := cert
  obtain ⟨mem,pp,qq⟩ := good p q hp hq
  have differing : separates u p q (label p q)=true := by
    cases u with
    | false => simp only [separates,Bool.false_eq_true,ite_false,pp,qq,pure rfl]; rfl
    | true =>
      simp only [separates,ite_true,pp,qq,bne_iff_ne]
      cases polarity (label p q) <;> decide
  have only := List.all_eq_true.mp all_ (label p q) (List.mem_toFinset.mp mem)
  exact ⟨hp,hq,by simpa only [differing,Bool.not_true,Bool.false_or,beq_iff_eq] using only⟩

theorem tight {u y k ws} (width : k+1≤(ws : List Sig).toFinset.card) (e : Hit)
    (cert : test u y ws e=true) : ¬Live u y k ws.toFinset := by
  intro run
  obtain ⟨label,polarity,legal,rect,pure⟩ := labels_of_tight run width
  obtain ⟨i,j,p,q,pa,qa,pb,qb⟩ := e
  simp only [test,Bool.and_eq_true,bne_iff_ne] at cert
  obtain ⟨⟨⟨⟨ne,ar⟩,ac⟩,br⟩,bc⟩ := cert
  obtain ⟨p1,qa0,la⟩ := forced_label legal pure ar
  obtain ⟨pa1,q0,ra⟩ := forced_label legal pure ac
  obtain ⟨_,qb0,lb⟩ := forced_label legal pure br
  obtain ⟨pb1,_,rb⟩ := forced_label legal pure bc
  have ha := (rect p pa q qa p1 pa1 q0 qa0 (la.trans ra.symm)).trans la
  have hb := (rect p pb q qb p1 pb1 q0 qb0 (lb.trans rb.symm)).trans lb
  exact ne (ha.symm.trans hb)
end KW

namespace Orbit
open PublicFloor Trace Moves Inputs

def diagrams : List (List Nat) := [[],[118,130,81],[100,131,82,16],[116,80,100,128,48,32,16],[116,83,32],[100,116,81,128,49,32],[118,133,33,48],[82,129,48],[100,131,116,50,33,16,80],[116,50,129,80],[100,49,128],[116,100,49,32,81,128]]

def moves (p : Nat) := ((diagrams[p]?).getD []).map swapRows

def scoreOK (p : Nat) (u : Bool) :=
  inputs.all fun a => inputs.all fun b => (opsOf u).all fun d =>
    rank u (d,movedWord (moves p) a,movedWord (moves p) b) == rank u (d,a,b)

def valid (p : Nat) :=
  (autoOK graph (moves p) && ((inputs.map (movedWord (moves p))).toFinset == inputs.toFinset)) &&
  (scoreOK p false && scoreOK p true)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem valid0 : valid 0=true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem valid1 : valid 1=true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem valid2 : valid 2=true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem valid3 : valid 3=true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem valid4 : valid 4=true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem valid5 : valid 5=true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem valid6 : valid 6=true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem valid7 : valid 7=true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem valid8 : valid 8=true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem valid9 : valid 9=true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem valid10 : valid 10=true := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem valid11 : valid 11=true := by decide +kernel

set_option maxRecDepth 10000 in
theorem checked (p : Fin 12) : valid p=true := by
  fin_cases p
  · exact valid0
  · exact valid1
  · exact valid2
  · exact valid3
  · exact valid4
  · exact valid5
  · exact valid6
  · exact valid7
  · exact valid8
  · exact valid9
  · exact valid10
  · exact valid11

theorem rotate (p : Fin 12) {u k phase S} (run : Ranked u graph (rank u) phase k S) :
    Ranked u graph (rank u) phase k (S.image (movedWord (moves p))) := by
  let ms := moves p.val
  let f := movedWord ms
  have h := checked p
  change ((autoOK graph ms && ((inputs.map f).toFinset == inputs.toFinset)) &&
    (scoreOK p false && scoreOK p true)) = true at h
  simp only [Bool.and_eq_true,beq_iff_eq,autoOK] at h
  have rawEq : (inputs.map f).toFinset = inputs.toFinset := h.1.2
  have auto := h.1.1
  have onto : Function.Surjective (movedRow ms) := fun r => ⟨movedRow ms.reverse r,composed_id auto.2 r⟩
  have fn : f = rename (movedRow ms) := funext (moved_eq_rename ms)
  have inj : Function.Injective f := by rw [fn]; exact rename_inj (movedRow ms) onto
  have raw (a : Sig) : f a∈inputs ↔ a∈inputs := by
    constructor
    · intro hf
      have h' : f a∈(inputs.map f).toFinset := rawEq.symm ▸ List.mem_toFinset.mpr hf
      obtain ⟨b,hb,eq⟩ := List.mem_map.mp (List.mem_toFinset.mp h')
      exact inj eq ▸ hb
    · intro ha
      exact List.mem_toFinset.mp (rawEq ▸ List.mem_toFinset.mpr (List.mem_map_of_mem ha))
  have score : ∀ g, good u g → rank u (mapped f g)=rank u g := by
    rintro ⟨d,a,b⟩ leg
    by_cases both : a∈inputs ∧ b∈inputs
    · have validScore : scoreOK p u=true := by
        cases u with
        | false => exact h.2.1
        | true => exact h.2.2
      exact beq_iff_eq.mp (List.all_eq_true.mp (List.all_eq_true.mp
        (List.all_eq_true.mp validScore a both.1) b both.2) d (opsOf_mem leg.1))
    · have neither : ¬ (f a∈inputs ∧ f b∈inputs) := fun e => both ⟨(raw _).mp e.1,(raw _).mp e.2⟩
      change rank u (d,f a,f b)=rank u (d,a,b)
      simp only [rank_eq,oldRank]
      rw [if_neg neither,if_neg both]
  have z : f zero=zero := by rw [fn]; exact (rename_constants (movedRow ms)).1
  have o : f one=one := by rw [fn]; exact (rename_constants (movedRow ms)).2
  have operation : ∀ g, f (result g)=result (mapped f g) := by
    rintro ⟨d,a,b⟩
    simp only [mapped,result,fn,rename_bin]
  have moved := transport inj z o operation score run
  exact auto.1.1 ▸ moved
end Orbit

namespace Verification
open PublicFloor Trace
open Inputs (rank)
open Load (Board)

def closed (u : Bool) (m cap : Nat) (b : Board) : Prop :=
  ∀ k, k≤cap → b.2.2.length+k=m → ¬Ranked u graph (rank u) b.1 k b.2.1.toFinset

def next (u : Bool) (b : Board) (g : Step) (ka kb : Bool) : Board :=
  (rank u g,Moves.child b.2.1 g ka kb,g::b.2.2)

theorem node {u m cap} {b : Board} (miss : graph∉b.2.1)
    (step : ∀ (g : Step) (ka kb : Bool), good u g → b.1≤rank u g →
      g.2.1∈b.2.1 → g.2.2∈b.2.1 → result g∉b.2.1 → closed u m (cap-1) (next u b g ka kb)) :
    closed u m cap b := by
  intro k bound size run
  cases k with
  | zero =>
    obtain ⟨only,_⟩ := run
    exact miss (List.mem_toFinset.mp (only.symm ▸ Finset.mem_singleton_self _))
  | succ k =>
    obtain ⟨g,ka,kb,legal,above,a,b',fresh,tail⟩ := Moves.take_step _ run
    apply step g ka kb legal above a b' fresh k (by omega) _ tail
    change (g::b.2.2).length+k=m
    simp only [List.length_cons]
    omega

theorem cofactor {u m cap} {b : Board} (low : Lower u inputs graph m) (board : Cuts.certified u b=true)
    (i : Fin 79) (test : Cuts.check u cap b i=true) : closed u m cap b := by
  intro k le size run
  exact Cuts.exclude low board i test le size (forget run)

theorem lost {u m cap p q} {b : Board} (test : RootPins.pairLost u b.2.1 p q=true) : closed u m cap b := by
  intro k le _ run
  exact RootPins.pairLost_sound test cap k le (forget run)

theorem wide {u m cap} {b : Board} (overflow : cap+1<b.2.1.toFinset.card) : closed u m cap b := by
  intro k le _ run
  have h := PublicFloor.live_size (forget run)
  omega

theorem link {u m cap} {b d : Board} (hd : closed u m cap d) (p : Fin 12)
    (same : b.2.1.toFinset.image (movedWord (Orbit.moves p))=d.2.1.toFinset)
    (stage : b.1=d.1) (depth : b.2.2.length=d.2.2.length) : closed u m cap b := by
  intro k le size run
  have other := Orbit.rotate p run
  rw [same,stage] at other
  exact hd k le (depth ▸ size) other

theorem original
    (roots : ∀ u m, m≤Inputs.cap u → Lower u inputs graph m →
      closed u m (Inputs.cap u) (0,inputs,[])) :
    ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C →
      PEqualNP.MetaComplexity.circuitFun 9 C=edge → 16≤C.size := by
  intro C legal goal
  by_contra! small
  obtain ⟨u,m,le,run,low⟩ := Min.minimum C legal goal (by omega)
  exact roots u m le low m le (Nat.zero_add _) run
end Verification

namespace Conflict
open PublicFloor

def sep (p q : Row) (w : Sig) := bit p w=true ∧ bit q w=false

def forced (y : Sig) (S : Finset Sig) (p q : Row) (w : Sig) :=
  bit p y=true ∧ bit q y=false ∧ sep p q w ∧ ∀ t∈S, sep p q t → t=w

def crosses (y : Sig) (S : Finset Sig) (a b : Sig) :=
  ∃ p q pa qa pb qb, forced y S p qa a ∧ forced y S pa q a ∧ forced y S p qb b ∧ forced y S pb q b

def image (a b z w : Sig) := if w=a ∨ w=b then z else w

def clean (a b : Sig) (U : Finset Sig) (w : Sig) := (w=a ∨ w=b) → w∉U

theorem positive_op {d} (h : allowed false d) : d=0 ∨ d=1 := by
  rcases allowed_four h with rfl|rfl|⟨e,_⟩|⟨e,_⟩ <;> simp_all

theorem bit_and (p : Row) (x z) : bit p (bin 0 x z)=(bit p x && bit p z) := by
  simp [bit,bin,BitVec.getLsbD_and]

theorem bit_or (p : Row) (x z) : bit p (bin 1 x z)=(bit p x || bit p z) := by
  simp [bit,bin,BitVec.getLsbD_or]

theorem op_needs {d a b p q} (op : allowed false d) (hit : sep p q (bin d a b)) : sep p q a ∨ sep p q b := by
  obtain ⟨hp,hq⟩ := hit
  rcases positive_op op with rfl|rfl <;>
    cases ha : bit p a <;> cases hb : bit p b <;> cases na : bit q a <;> cases nb : bit q b <;> simp_all [sep,bit_and,bit_or]

theorem forced_image {y U a b d k p q w} (op : allowed false d)
    (run : Live false y k (insert (bin d a b) U)) (clear : clean a b U w)
    (f : forced y (insert a (insert b U)) p q w) :
    forced y (insert (bin d a b) U) p q (image a b (bin d a b) w) := by
  let z := bin d a b
  obtain ⟨hp,hq,hw,only⟩ := f
  have uniq : ∀ t∈insert z U, sep p q t → t=image a b z w := by
    intro t ht hsep
    rcases Finset.mem_insert.mp ht with rfl|inU
    · rcases op_needs op hsep with s|s
      · exact (if_pos (Or.inl (only a (by simp) s).symm)).symm
      · exact (if_pos (Or.inr (only b (by simp) s).symm)).symm
    · have eq := only t (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem inU)) hsep
      subst t
      exact (if_neg (fun operands => clear operands inU)).symm
  obtain ⟨t,ht,atP,atQ⟩ := mono_row_difference run rfl hp hq
  exact ⟨hp,hq,uniq t ht ⟨atP,atQ⟩ ▸ (show sep p q t from ⟨atP,atQ⟩),uniq⟩

theorem crosses_image {y U a b d k w v} (op : allowed false d)
    (run : Live false y k (insert (bin d a b) U)) (cw : clean a b U w) (cv : clean a b U v)
    (e : crosses y (insert a (insert b U)) w v) :
    crosses y (insert (bin d a b) U) (image a b (bin d a b) w) (image a b (bin d a b) v) := by
  obtain ⟨p,q,pa,qa,pb,qb,ar,ac,br,bc⟩ := e
  exact ⟨p,q,pa,qa,pb,qb,forced_image op run cw ar,forced_image op run cw ac,
    forced_image op run cv br,forced_image op run cv bc⟩

theorem operands_do_not_cross {y U a b d k} (op : allowed false d) (ne : a≠b)
    (run : Live false y k (insert (bin d a b) U)) (aU : a∉U)
    (e : crosses y (insert a (insert b U)) a b) : False := by
  obtain ⟨p,q,pa,qa,pb,qb,ar,ac,br,bc⟩ := e
  have clear : clean a b U a := fun _ => aU
  rcases positive_op op with rfl|rfl
  · have hp := (forced_image op run clear ac).2.2.1.1
    simp only [image,or_true,true_or,ite_true,bit_and] at hp
    exact ne (ac.2.2.2 b (by simp) ⟨(Bool.and_eq_true_iff.mp hp).2,bc.2.2.1.2⟩).symm
  · have hq := (forced_image op run clear ar).2.2.1.2
    simp only [image,or_true,true_or,ite_true,bit_or] at hq
    exact ne (ar.2.2.2 b (by simp) ⟨br.2.2.1.1,(Bool.or_eq_false_iff.mp hq).2⟩).symm

theorem crosses_symm {y S w v} (e : crosses y S w v) : crosses y S v w := by
  obtain ⟨p,q,pa,qa,pb,qb,a,b,c,d⟩ := e
  exact ⟨p,q,pb,qb,pa,qa,c,d,a,b⟩

theorem image_mem {a b z w : Sig} {U : Finset Sig} (hw : w∈insert a (insert b U)) :
    image a b z w ∈ insert z U := by
  by_cases operand : w=a ∨ w=b
  · simp [image,operand]
  · obtain ⟨ha,hb⟩ := not_or.mp operand
    rw [image,if_neg operand]
    exact Finset.mem_insert_of_mem ((Finset.mem_insert.mp ((Finset.mem_insert.mp hw).resolve_left ha)).resolve_left hb)

theorem distinct {y U a b d k w v} (op : allowed false d) (ab : a≠b)
    (fresh : bin d a b∉insert a (insert b U)) (run : Live false y k (insert (bin d a b) U))
    (mw : w∈insert a (insert b U)) (mv : v∈insert a (insert b U)) (ne : w≠v)
    (cw : clean a b U w) (cv : clean a b U v) (e : crosses y (insert a (insert b U)) w v) :
    image a b (bin d a b) w ≠ image a b (bin d a b) v := by
  intro eq
  by_cases x : w=a ∨ w=b <;> by_cases t : v=a ∨ v=b
  · rcases x with rfl|rfl <;> rcases t with rfl|rfl
    · exact ne rfl
    · exact operands_do_not_cross op ab run (cw (Or.inl rfl)) e
    · exact operands_do_not_cross op ab run (cv (Or.inl rfl)) (crosses_symm e)
    · exact ne rfl
  · simp only [image,if_pos x,if_neg t] at eq
    exact fresh (eq ▸ mv)
  · simp only [image,if_neg x,if_pos t] at eq
    exact fresh (eq ▸ mw)
  · simp only [image,if_neg x,if_neg t] at eq
    exact ne eq

theorem width {u y k S} (run : Live u y k S) : S.card≤k+1 := by
  induction run using Live.ind with
  | stop => simp
  | @binary k U a b d hd ha hb ab fresh tail ih =>
    have hz : bin d a b∉U := fun hm => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hz] at ih
    have sa := Finset.card_insert_le (a:=a) (s:=insert b U)
    have sb := Finset.card_insert_le (a:=b) (s:=U)
    omega

theorem parent_size {a b : Sig} (ab : a≠b) (U : Finset Sig) :
    (insert a (insert b U)).card + (decide (a∈U)).toNat + (decide (b∈U)).toNat = U.card+2 := by
  by_cases ha : a∈U <;> by_cases hb : b∈U <;>
    simp [ha,hb,ab,Finset.card_insert_of_notMem] <;> omega

def conflictFree (y : Sig) (S : Finset Sig) := ∀ w∈S, ∀ v∈S, w≠v → ¬crosses y S w v

theorem tight {y k S} (run : Live false y k S) (bound : k+1≤S.card) : conflictFree y S := by
  induction k generalizing S with
  | zero =>
    obtain ⟨rfl,_⟩ := run
    simp [conflictFree]
  | succ k ih =>
    obtain ⟨U,a,b,d,op,rfl,_,_,ab,fresh,tail⟩ := run
    have hz : bin d a b∉U := fun hm => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    have child := width tail
    rw [Finset.card_insert_of_notMem hz] at child
    have count := parent_size ab U
    have aU : a∉U := by intro h; simp only [h,decide_true,Bool.toNat_true] at count; omega
    have bU : b∉U := by intro h; simp only [h,decide_true,Bool.toNat_true] at count; omega
    simp only [aU,bU,decide_false,Bool.toNat_false,Nat.add_zero] at count
    have clear (w) : clean a b U w := by rintro (rfl|rfl) <;> assumption
    have smaller := ih tail (by rw [Finset.card_insert_of_notMem hz]; omega)
    intro w hw v hv ne e
    exact smaller _ (image_mem hw) _ (image_mem hv) (distinct op ab fresh tail hw hv ne (clear w) (clear v) e)
      (crosses_image op tail (clear w) (clear v) e)
end Conflict

namespace Conflict
open PublicFloor

def supported (y : Sig) (S : Finset Sig) (part : Sig → Bool) (p q : Row) :=
  bit p y=true ∧ bit q y=false ∧ ∀ t∈S, sep p q t → part t=true

def division (y : Sig) (S : Finset Sig) (part : Sig → Bool) :=
  (∀ w∈S, ∀ v∈S, w≠v → crosses y S w v → part w≠part v) ∧
  ∀ p q pa qa, supported y S part p qa → supported y S part pa q → ∃ t∈S, part t=true ∧ sep p q t

end Conflict

namespace Reuse
open PublicFloor Conflict

def support (y : Sig) (S : Finset Sig) (c : Sig → Nat) (i : Nat) (p q : Row) :=
  bit p y=true ∧ bit q y=false ∧ ∀ w∈S, sep p q w → c w=i

def coloring (y : Sig) (S : Finset Sig) (n : Nat) (c : Sig → Nat) :=
  (∀ w∈S, c w<n) ∧ (∀ w∈S, ∀ v∈S, w≠v → crosses y S w v → c w≠c v) ∧
    ∀ i p q pa qa, support y S c i p qa → support y S c i pa q → ∃ t∈S, c t ≤ i ∧ sep p q t

abbrev carried (a b : Sig) (U : Finset Sig) (w : Sig) := w∈U ∧ (w=a ∨ w=b)

def weight (a b : Sig) (U : Finset Sig) := (decide (a∈U)).toNat+(decide (b∈U)).toNat

def slot (a : Sig) (U : Finset Sig) (w : Sig) := if w=a then 0 else (decide (a∈U)).toNat

def paint (a b z : Sig) (U : Finset Sig) (c : Sig → Nat) (w : Sig) :=
  if carried a b U w then slot a U w else weight a b U+c (image a b z w)

theorem slot_lt {a b U w} (keep : carried a b U w) : slot a U w<weight a b U := by
  obtain ⟨mem,same|same⟩ := keep <;> subst w
  · simp only [slot,ite_true,weight,mem,decide_true,Bool.toNat_true]; omega
  · by_cases eq : b=a
    · subst b; simp [slot,weight,mem]
    · simp only [slot,eq,ite_false,weight,mem,decide_true,Bool.toNat_true]; omega

theorem slot_unique {a b U w v} (ab : a≠b) (left : carried a b U w) (right : carried a b U v)
    (eq : slot a U w=slot a U v) : w=v := by
  obtain ⟨hw,rfl|rfl⟩ := left <;> obtain ⟨hv,rfl|rfl⟩ := right
  all_goals first | rfl | simp [slot,Ne.symm ab,hw,hv] at eq

theorem small {a b z U c w} (h : carried a b U w) : paint a b z U c w<weight a b U := by
  rw [paint,if_pos h]
  exact slot_lt h

theorem big {a b z U c w} (h : ¬carried a b U w) : weight a b U≤paint a b z U c w := by
  rw [paint,if_neg h]; omega

theorem paint_le {a b z U c w} : paint a b z U c w≤weight a b U+c (image a b z w) := by
  by_cases keep : carried a b U w
  · have h := small (z:=z) (c:=c) keep; omega
  · rw [paint,if_neg keep]

theorem unshift {a b z U c w i} (large : weight a b U ≤ i) (eq : paint a b z U c w=i) :
    ¬carried a b U w ∧ c (image a b z w)=i-weight a b U := by
  by_cases keep : carried a b U w
  · have h := small (z:=z) (c:=c) keep; omega
  · rw [paint,if_neg keep] at eq
    exact ⟨keep,by omega⟩

theorem original {a b z U w} (mem : w∈U) (h : ¬carried a b U w) : image a b z w=w :=
  if_neg (fun isOp => h ⟨mem,isOp⟩)

theorem clear {a b U w} (h : ¬carried a b U w) : clean a b U w := fun op mem => h ⟨mem,op⟩

theorem support_next {y U a b d c i p q} (op : allowed false d) (large : weight a b U ≤ i)
    (old : support y (insert a (insert b U)) (paint a b (bin d a b) U c) i p q) :
    support y (insert (bin d a b) U) c (i-weight a b U) p q := by
  refine ⟨old.1,old.2.1,?_⟩
  intro w mem sepW
  rcases Finset.mem_insert.mp mem with rfl|inside
  · rcases op_needs op sepW with sa|sb
    · have next := (unshift large (old.2.2 a (by simp) sa)).2
      simpa only [image,eq_self,true_or,ite_true] using next
    · have next := (unshift large (old.2.2 b (by simp) sb)).2
      simpa only [image,eq_self,or_true,ite_true] using next
  · obtain ⟨absent,eq⟩ := unshift large (old.2.2 w (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem inside)) sepW)
    simpa only [original inside absent] using eq
end Reuse

namespace Reuse
open PublicFloor Conflict

theorem same_small {a b z U c w v i} (ab : a≠b) (below : i<weight a b U)
    (left : paint a b z U c w=i) (right : paint a b z U c v=i) : w=v := by
  have kw : carried a b U w := by
    by_contra h
    have h' := big (z:=z) (c:=c) h; omega
  have kv : carried a b U v := by
    by_contra h
    have h' := big (z:=z) (c:=c) h; omega
  rw [paint,if_pos kw] at left
  rw [paint,if_pos kv] at right
  exact slot_unique ab kw kv (left.trans right.symm)

theorem transfer {y U a b d k n c} (op : allowed false d) (aa : proper a) (bb : proper b) (ab : a≠b)
    (fresh : bin d a b∉insert a (insert b U)) (tail : Live false y k (insert (bin d a b) U))
    (child : coloring y (insert (bin d a b) U) n c) :
    coloring y (insert a (insert b U)) (weight a b U+n) (paint a b (bin d a b) U c) := by
  let z := bin d a b
  let color := paint a b z U c
  let amt := weight a b U
  refine ⟨?_,?_,?_⟩
  · intro w mem
    have h := child.1 _ (image_mem mem)
    exact lt_of_le_of_lt paint_le (Nat.add_lt_add_left h _)
  · intro w hw v hv ne cross eq
    by_cases low : color w<amt
    · exact ne (same_small ab low rfl eq.symm)
    · have hi : amt≤color w := Nat.le_of_not_gt low
      obtain ⟨cw,pw⟩ := unshift hi (rfl : color w=color w)
      obtain ⟨cv,pv⟩ := unshift hi eq.symm
      exact child.2.1 _ (image_mem hw) _ (image_mem hv) (distinct op ab fresh tail hw hv ne (clear cw) (clear cv) cross)
        (crosses_image op tail (clear cw) (clear cv) cross) (pw.trans pv.symm)
  · intro i p q pa qa top side
    by_cases low : i<amt
    · have parent := Live.binary op aa bb ab fresh tail
      obtain ⟨w,hw,wp,wqa⟩ := mono_row_difference parent rfl top.1 top.2.1
      obtain ⟨v,hv,vpa,vq⟩ := mono_row_difference parent rfl side.1 side.2.1
      have first := top.2.2 w hw ⟨wp,wqa⟩
      have last := side.2.2 v hv ⟨vpa,vq⟩
      obtain rfl := same_small ab low first last
      exact ⟨w,hw,Nat.le_of_eq first,wp,vq⟩
    · have high : amt ≤ i := Nat.le_of_not_gt low
      obtain ⟨t,mem,below,cross⟩ := child.2.2 _ _ _ _ _ (support_next op high top) (support_next op high side)
      rcases Finset.mem_insert.mp mem with rfl|inside
      · rcases op_needs op cross with sa|sb
        · refine ⟨a,by simp,?_,sa⟩
          have h := paint_le (a:=a) (b:=b) (z:=z) (U:=U) (c:=c) (w:=a)
          simp only [image,eq_self,true_or,ite_true] at h
          change color a ≤ i
          change color a≤amt+c z at h
          change c z ≤ i-amt at below
          omega
        · refine ⟨b,by simp,?_,sb⟩
          have h := paint_le (a:=a) (b:=b) (z:=z) (U:=U) (c:=c) (w:=b)
          simp only [image,eq_self,or_true,ite_true] at h
          change color b ≤ i
          change color b≤amt+c z at h
          change c z ≤ i-amt at below
          omega
      · refine ⟨t,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem inside),?_,cross⟩
        by_cases keep : carried a b U t
        · exact (Nat.le_of_lt (small keep)).trans high
        · rw [paint,if_neg keep,original inside keep]
          change amt+c t ≤ i
          change c t ≤ i-amt at below
          omega

theorem palette {y S k} (run : Live false y k S) : ∃ n c, coloring y S n c ∧ S.card+n≤k+2 := by
  induction run using Live.ind with
  | stop hp =>
    refine ⟨1,fun _ => 0,⟨by simp,by simp,?_⟩,by simp⟩
    intro i p q pa qa top side
    exact ⟨y,by simp,Nat.zero_le _,top.1,side.2.1⟩
  | @binary k U a b d op aa bb ab fresh tail ih =>
    obtain ⟨n,c,fit,bound⟩ := ih
    refine ⟨_,_,transfer op aa bb ab fresh tail fit,?_⟩
    have notIn : bin d a b∉U := fun mem => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem mem))
    rw [Finset.card_insert_of_notMem notIn] at bound
    have size := parent_size ab U
    unfold weight
    omega
end Reuse

namespace Reuse
open PublicFloor Conflict

theorem binary {y k S} (run : Live false y k S) (bound : k≤S.card) : ∃ part, division y S part := by
  obtain ⟨n,c,fit,budget⟩ := palette run
  refine ⟨fun w => c w==0,?_,?_⟩
  · intro w hw v hv ne cross eq
    have smallW := fit.1 w hw
    have smallV := fit.1 v hv
    have distinct_ := fit.2.1 w hw v hv ne cross
    by_cases zeroW : c w=0
    · have zeroV : c v=0 := beq_iff_eq.mp (eq.symm.trans (beq_iff_eq.mpr zeroW))
      exact distinct_ (zeroW.trans zeroV.symm)
    · have other : c v≠0 := by intro z; exact zeroW (beq_iff_eq.mp (eq.trans (beq_iff_eq.mpr z)))
      omega
  · intro p q pa qa first other
    have convert_ {p q : Row} (h : supported y S (fun w => c w==0) p q) : support y S c 0 p q :=
      ⟨h.1,h.2.1,fun w hw sw => beq_iff_eq.mp (h.2.2 w hw sw)⟩
    obtain ⟨w,hw,low,sepW⟩ := fit.2.2 _ _ _ _ _ (convert_ first) (convert_ other)
    exact ⟨w,hw,beq_iff_eq.mpr (by omega),sepW⟩
end Reuse

namespace PartitionBits
abbrev W := BitVec 512

abbrev M := BitVec 12

abbrev A := BitVec 4096

abbrev Slot := Fin 12

abbrev Row := Fin 512

def pack (f : Slot → Bool) : M := (BitVec.ofBoolListLE (List.ofFn f)).setWidth 12

theorem pack_ok (f : Slot → Bool) (i : Slot) : (pack f).getLsbD i.val=f i := by
  rw [pack,BitVec.getLsbD_setWidth,BitVec.getLsbD_ofBoolListLE]
  simp only [i.isLt,decide_true,Bool.true_and,List.getD_eq_getElem?_getD,List.getElem?_ofFn,
    dif_pos,Option.getD_some]

def rowBits (r : Row) : List W → Nat
  | [] => 0
  | x::xs => Nat.bit (x.getLsbD r.val) (rowBits r xs)

theorem row_bit (r : Row) (xs : List W) (i : Nat) :
    (rowBits r xs).testBit i=(xs.getD i 0).getLsbD r.val := by
  induction xs generalizing i with
  | nil => simp [rowBits]
  | cons x xs ih => cases i with
    | zero => simp only [rowBits,Nat.testBit_bit_zero,List.getD_cons_zero]
    | succ i => simpa only [rowBits,Nat.testBit_bit_succ,List.getD_cons_succ] using ih i

def profile (ws : List W) (r : Row) : M := BitVec.ofNat 12 (rowBits r ws)

theorem profile_at (ws : List W) (r : Row) (i : Slot) :
    (profile ws r).getLsbD i.val=(ws.getD i.val 0).getLsbD r.val := by
  simp only [profile,BitVec.getLsbD_ofNat,i.isLt,decide_true,Bool.true_and,row_bit]

def sep (p q : M) := p &&& ~~~q

theorem sep_ok (ws : List W) (p q : Row) (i : Slot) :
    (sep (profile ws p) (profile ws q)).getLsbD i.val =
      ((ws.getD i.val 0).getLsbD p.val && !(ws.getD i.val 0).getLsbD q.val) := by
  simp only [sep,profile_at,BitVec.getLsbD_and,BitVec.getLsbD_not,i.isLt,decide_true,Bool.true_and,pack_ok]

def union {n : Nat} (f : α → BitVec n) : List α → BitVec n
  | [] => 0
  | a::xs => f a ||| union f xs

theorem union_ok {n : Nat} (f : α → BitVec n) (xs : List α) (i : Nat) :
    (union f xs).getLsbD i=true ↔ ∃ x∈xs, (f x).getLsbD i=true := by
  induction xs with
  | nil => simp [union]
  | cons x xs ih => simp only [union,BitVec.getLsbD_or,Bool.or_eq_true_iff,ih,List.mem_cons,exists_eq_or_imp]

def lane (i : Slot) : A :=
  let half := 2^i.val
  BitVec.ofNat 4096 (((2^4096-1)/(2^half+1)) <<< half)

def laneTest (i : Slot) := (List.range 4096).all fun k => (lane i).getLsbD k == k.testBit i.val

theorem lane_ok_of {i : Slot} (h : laneTest i=true) (x : M) :
    (lane i).getLsbD x.toNat = x.getLsbD i.val := by
  exact beq_iff_eq.mp (List.all_eq_true.mp h x.toNat (List.mem_range.mpr x.isLt))

theorem zeroAt (m : A) (x : M) : (~~~m).getLsbD x.toNat= !(m.getLsbD x.toNat) := by
  simp only [BitVec.getLsbD_not,x.isLt,decide_true,Bool.true_and]

def allOn (r : M) (negative : Bool) :=
  ~~~(union (fun i : Slot => if r.getLsbD i.val then (if negative then lane i else ~~~(lane i)) else 0) (List.finRange 12))

theorem allOn_ok (r : M) (neg : Bool) (x : M) (lanes : ∀ i : Slot, laneTest i=true) :
    (allOn r neg).getLsbD x.toNat=true ↔ ∀ i : Slot, r.getLsbD i.val=true → x.getLsbD i.val= !neg := by
  rw [allOn,zeroAt,Bool.not_eq_true']
  simp only [Bool.eq_false_iff,ne_eq,union_ok]
  constructor
  · intro missing i used
    have rejected := fun (t : (if neg then lane i else ~~~(lane i)).getLsbD x.toNat=true) =>
      missing ⟨i,List.mem_finRange _,by simpa only [used,ite_true] using t⟩
    cases neg
    · change x.getLsbD i.val = true
      cases eq : x.getLsbD i.val with
      | true => rfl
      | false => exact False.elim (rejected (by simp only [Bool.false_eq_true,ite_false,zeroAt,lane_ok_of (lanes i),eq,Bool.not_false]))
    · change x.getLsbD i.val = false
      exact Bool.eq_false_iff.mpr (fun h => rejected (by simpa only [ite_true,lane_ok_of (lanes i)] using h))
  · rintro all ⟨i,_,test⟩
    cases used : r.getLsbD i.val with
    | false =>
      simp only [used,Bool.false_eq_true,ite_false] at test
      change (0#4096).getLsbD x.toNat=true at test
      simp only [BitVec.getLsbD_zero,Bool.false_eq_true] at test
    | true =>
      have eq := all i used
      cases neg <;> simp only [used,ite_true,Bool.false_eq_true,ite_false,zeroAt,lane_ok_of (lanes i),eq,
        Bool.not_false,Bool.not_true] at test
end PartitionBits

namespace PartitionBits
def pp : Array Nat := #[3,6,12,24,17,33,66,132,264,160,320,288]

def nn : Array Nat := #[42,50,69,104,116,138,201,208,261,276,385,402]

def pos (i : Slot) : Row := Fin.ofNat 512 (pp[i.val]?.getD 0)

def neg (i : Slot) : Row := Fin.ofNat 512 (nn[i.val]?.getD 0)

def nibble (h k : Nat) := Fin.ofNat 12 ((h >>> (4*k)) &&& 15)

def cornerMask (ps ns : Slot → M) (h : Nat) :=
  let p := ps (nibble h 0)
  let q := ns (nibble h 1)
  let pa := ps (nibble h 2)
  let qa := ns (nibble h 3)
  allOn (sep p qa ||| sep pa q) false &&& allOn (sep p q) true

theorem corner_at {x : M} {ps ns : Slot → M} {h : Nat} (lanes : ∀ i, laneTest i=true)
    (bad : (cornerMask ps ns h).getLsbD x.toNat=true) :
    (∀ i : Slot, (sep (ps (nibble h 0)) (ns (nibble h 3))).getLsbD i.val=true → x.getLsbD i.val=true) ∧
    (∀ i : Slot, (sep (ps (nibble h 2)) (ns (nibble h 1))).getLsbD i.val=true → x.getLsbD i.val=true) ∧
    (∀ i : Slot, (sep (ps (nibble h 0)) (ns (nibble h 1))).getLsbD i.val=true → x.getLsbD i.val=false) := by
  obtain ⟨yes,no⟩ := Bool.and_eq_true_iff.mp ((BitVec.getLsbD_and ..) ▸ bad)
  have top := (allOn_ok _ false x lanes).mp yes
  have bottom := (allOn_ok _ true x lanes).mp no
  refine ⟨fun i m => top i ?_,fun i m => top i ?_,bottom⟩
  · rw [BitVec.getLsbD_or,m,Bool.true_or]
  · rw [BitVec.getLsbD_or,m,Bool.or_true]
end PartitionBits

namespace PartitionProof
open PublicFloor Conflict
open PartitionBits (Slot M profile pack pack_ok)

abbrev pos := PartitionBits.pos

abbrev negRow := PartitionBits.neg

theorem tags : ∀ s : Slot, bit (pos s) graph=true ∧ bit (negRow s) graph=false := by decide +kernel

theorem slot {ws : List Sig} (len : ws.length≤12) {w} (mem : w∈ws) :
    ∃ i : Slot, ws.getD i.val 0=w := by
  obtain ⟨i,hi,h⟩ := List.getElem_of_mem mem
  exact ⟨⟨i,by omega⟩,by simpa only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi,Option.getD_some] using h⟩

theorem sep_at (ws : List Sig) (p q : Row) (i : Slot) :
    (PartitionBits.sep (profile ws p) (profile ws q)).getLsbD i.val=true ↔ sep p q (ws.getD i.val 0) := by
  rw [PartitionBits.sep_ok]
  simp only [sep,bit,Bool.and_eq_true_iff,Bool.not_eq_true']

theorem support {ws : List Sig} (len : ws.length≤12) {part : Sig → Bool} (p q : Slot)
    (marked : ∀ i : Slot, (PartitionBits.sep (profile ws (pos p)) (profile ws (negRow q))).getLsbD i.val=true →
      (pack (fun j : Slot => part (ws.getD j.val 0))).getLsbD i.val=true) :
    supported graph ws.toFinset part (pos p) (negRow q) := by
  refine ⟨(tags p).1,(tags q).2,?_⟩
  intro w hw diff
  obtain ⟨i,eq⟩ := slot len (List.mem_toFinset.mp hw)
  have res := marked i ((sep_at ..).mpr (eq.symm ▸ diff))
  simpa only [pack_ok,eq] using res
end PartitionProof

namespace PartitionBits
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem lane0 : laneTest 0=true := by decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem lane1 : laneTest 1=true := by decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem lane2 : laneTest 2=true := by decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem lane3 : laneTest 3=true := by decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem lane4 : laneTest 4=true := by decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem lane5 : laneTest 5=true := by decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem lane6 : laneTest 6=true := by decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem lane7 : laneTest 7=true := by decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem lane8 : laneTest 8=true := by decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem lane9 : laneTest 9=true := by decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem lane10 : laneTest 10=true := by decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem lane11 : laneTest 11=true := by decide +kernel

theorem checked_lanes (i : Slot) : laneTest i=true := by
  obtain ⟨j,bound⟩ := i
  have split : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 ∨ j=7 ∨ j=8 ∨ j=9 ∨ j=10 ∨ j=11 := by omega
  rcases split with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact lane0
  · exact lane1
  · exact lane2
  · exact lane3
  · exact lane4
  · exact lane5
  · exact lane6
  · exact lane7
  · exact lane8
  · exact lane9
  · exact lane10
  · exact lane11
end PartitionBits

namespace Quick
open Load

def mRaw : List (Nat × Nat) := [(0xffffff000000000fff,0x544544544544544544544544544544544544),(0xfff000000000000ffffff,0x823823823823823823823823823823823823),(0xfff000000000000ffffff000,0x314314314314314314314314314314314314),(0xfff000000000000ffffff000000,0x69069069069069069069069069069069069),(0xffffff000000000,0xa92a92a92a92a92a92a92a92a92a92a92a92),(0xfff000fff000000000fff000000000000000,0x1b01b01b01b01b01b01b01b01b01b01b01b),(0xfff000000000fff000000000000000000,0xdc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc0dc),(0xfff000fff000000000000000000000,0xce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0),(0xffffff000fff000000000000000000000000,0xf00f00f00f00f00f00f00f00f00f00f00f00)]

def sRaw : List (Nat × Nat) := [(0x4c10398cc00b1800001080000fc60004c4481d3200820001075b0003090d9a33c9400001c73fffe20001ffff600070003fff,0x4c10098c400b1a910010a91004c6a44444480d320082a841014b542100048a11c95510000112a222a88095116a8835441511),(0x210a52610c040200006430000b2180007c00061c3b30c0006249c00031632604c0fffff66a4c8000c0006400080007fffffff,0x210a52610804024086643408c9219023180002040b30d04362494821a0210200402208762a44c118d0462608c90464823608e),(0x1c01f2583c000181c00013c6000072081863c4010000038e7fffc98c38470f180008738f0001000078000ffff9fffc000,0x40052583c185181c18512c6061462080801440106140080130a498438470518c508508b18a1062858c50262893148c50),(0x600607e0080c000000600001c07ffff8070e07c003e00007c0f80000e0fc0780fe0000f83f00001ffff80000ffffe0000000,0x600002a0080c001a206001a4000a0698070a07c003e00c9340f8064820bc0280ae01a228370034860d2801a4c0d3606901a4),(0x380c7f80031f000001f800001ff800000380ff8007c000007ff000000ff0007ff000000ffc000001fffffffff000000000000,0x380c7f00031f005245f805249fb0149203805f0007c015124be00a890df00056e002a44d7c005491952576a4a15240a922a48),(0xf800003e0000001ffffffe000000003ff000007ffffff800000000fffff800000000ffffffffe000000000000000000000,0x3e0000066ae5006e000001b029900000553401b8000000d8fffb7000000066fffee80dc00360006c0036001b006c),(0x3ff0000003fffffffe0000000000000003fffffff8000000000000000ffffffffffffff000000000000000000000000000000,0xe50000003e9d48378000037000000dc03fffdfbf000019c000000ce0fdefdffbfdc3780000006e001b80037001b800dc0370),(0x3ffffffffc000000000000000000000003fffffffffffffffffffffff00000000000000000000000000000000000000000000,0x3ffffbffac00006380000638000018e00166f7febaacb9e07f7fecf030000000000338000000670019c00338019c00ce03380),(0x3ffffffffffffffffffffffffffffffffc0000000000000000000000000000000000000000000000000000000000000000000,0x31afffd5fc162b7c0151afc01fff5f007c00000000001e0000000f00000000000003c000000078001e0003c001e000f003c00)]
end Quick

namespace Near
open PublicFloor Load

abbrev Hint := Sum (Nat × Nat) KW.Hit

def test (u : Bool) (cap : Nat) (ws : List Sig) : Hint → Bool
  | .inl (p,q) => RootPins.pairLost u ws (Fin.ofNat 512 p) (Fin.ofNat 512 q)
  | .inr e => decide (cap+1≤ws.toFinset.card) && KW.test u graph ws e

theorem sound {u cap ws e} (pass : test u cap ws e=true) : Impossible u graph cap ws.toFinset := by
  rcases e with ⟨p,q⟩|e
  · exact RootPins.pairLost_sound pass cap
  · obtain ⟨width,ok⟩ := Bool.and_eq_true_iff.mp pass
    have card := of_decide_eq_true width
    intro k le
    exact KW.tight (by omega) e ok
end Near

namespace Node
open PublicFloor Trace Inputs Verification
open Load (Board)

abbrev Arc := Nat × Nat × Nat

abbrev Future := Nat → Option Board

def inverse : Array Nat := #[0,1,2,8,4,11,6,7,3,9,10,5]

def sameB (b d : Board) (p : Fin 12) :=
  (b.1==d.1 && b.2.2.length==d.2.2.length) &&
  Order.ordered (b.2.1.map (movedWord (Orbit.moves p))) == d.2.1

theorem same_ok {u m cap b d p} (hd : closed u m cap d) (hit : sameB b d p=true) :
    closed u m cap b := by
  obtain ⟨⟨phase,depth⟩,ws⟩ := (by simpa only [sameB,Bool.and_eq_true,beq_iff_eq] using hit :
    (b.1=d.1 ∧ b.2.2.length=d.2.2.length) ∧
    Order.ordered (b.2.1.map (movedWord (Orbit.moves p)))=d.2.1)
  apply link hd p _ phase depth
  ext w
  rw [List.mem_toFinset,←ws]
  rw [(Order.permutation _).mem_iff]
  simp only [Finset.mem_image,List.mem_toFinset,List.mem_map]

def packed (a b d ka kb : Nat) :=
  a + 16*b + 256*(Load.opCode d) + 1024*(ka+2*kb)

def key (ws : List Sig) (g : Step) (ka kb : Bool) :=
  let a := ws.idxOf g.2.1
  let b := ws.idxOf g.2.2
  (packed a b g.1 ka.toNat kb.toNat,packed b a (flipOp g.1) kb.toNat ka.toNat)

def aliasB (b : Board) (keys : Nat × Nat) (arcs : List Arc) (future : Future) :=
  arcs.any fun (action,target,perm) =>
    (action==keys.1 || action==keys.2) &&
    (future target).any (fun d => sameB b d (Fin.ofNat 12 (inverse[perm]?.getD 0)))

theorem alias_ok {u m cap b keys arcs future}
    (hd : ∀ i d, future i=some d → closed u m cap d) (hit : aliasB b keys arcs future=true) : closed u m cap b := by
  obtain ⟨⟨act,ix,p⟩,_,ok⟩ := List.any_eq_true.mp hit
  obtain ⟨_,ok⟩ := Bool.and_eq_true_iff.mp ok
  cases eq : future ix with
  | none => simp [eq] at ok
  | some d =>
    simp only [eq,Option.any_some] at ok
    apply same_ok _ ok
    exact hd ix d eq

def trivialB (cap : Nat) (b : Board) :=
  b.2.1.contains zero || decide (cap+1<b.2.1.length)

theorem trivial_ok {u m cap b} (safe : Cuts.certified u b=true)
    (hit : trivialB cap b=true) : closed u m cap b := by
  rcases Bool.or_eq_true_iff.mp hit with has|card
  · intro k _ _ run
    exact (PublicFloor.live_proper (forget run) zero
      (List.mem_toFinset.mpr (List.contains_iff_mem.mp has))).1 rfl
  · obtain ⟨phase,ws,gs⟩ := b
    simp only [Cuts.certified,Bool.and_eq_true,decide_eq_true_eq] at safe
    apply wide
    rw [List.toFinset_card_of_nodup safe.1.2]
    exact of_decide_eq_true card

def four (f : Bool → Bool → Bool) :=
  (f false false && f false true) && (f true false && f true true)

theorem four_ok {f} (h : four f=true) (ka kb : Bool) : f ka kb=true := by
  simp only [four,Bool.and_eq_true] at h
  cases ka <;> cases kb <;> tauto

def pairB (u : Bool) (b : Board) (pq : Option (Nat × Nat)) :=
  pq.any fun (p,q) => RootPins.pairLost u b.2.1 (Fin.ofNat 512 p) (Fin.ofNat 512 q)

end Node

namespace Table
open Load

def seek (parent : Nat → Nat) (needle : Nat) : Nat → Nat → Nat → Nat
  | 0,lo,_ => lo
  | n+1,lo,hi =>
    if lo<hi then
      let mid := (lo+hi)/2
      if parent mid < needle then seek parent needle n (mid+1) hi
      else seek parent needle n lo mid
    else lo

def window (get : Nat → Link) (p lo hi : Nat) :=
  let search := seek (fun i => (get i).1) p ((hi-lo).log2+2) lo hi
  let stop := seek (fun i => (get i).1) (p+1) ((hi-lo).log2+2) search hi
  (List.range' search (stop-search)).map fun i => (get i).2
end Table

namespace Substitute
open PublicFloor Project Atlas Mono
open Load (Board)

def covers (mask : Sig) (alt : List Choice) (ws : List Sig) :=
  ws.all (fun w => (zero::one::wires inputs alt).any fun v => dominatesB graph mask v w)

def check (cap : Nat) (b : Board) (i : Fin 79) (alt : List Choice) :=
  let mask := border i
  let price := paidCount graph mask inputs alt
  let const := b.2.1.countP (isMaskedConstant mask)
  let cut := if i.val=78 then decide (price < b.2.2.length+const) else decide (cap+price < lower 0 i+const)
  (cut && Cuts.feasibleB false inputs alt) && covers mask alt b.2.1

theorem sound {m cap} {b : Board} {i : Fin 79} {alt : List Choice}
    (low : Lower false inputs graph m) (nd : b.2.1.Nodup)
    (hit : check cap b i alt=true) : Verification.closed false m cap b := by
  intro k le depth ranked
  obtain ⟨⟨cut,feas⟩,dominating⟩ := (by simpa only [check,Bool.and_eq_true] using hit :
    ((if i.val=78 then decide (paidCount graph (border i) inputs alt < b.2.2.length+b.2.1.countP (isMaskedConstant (border i)))
      else decide (cap+paidCount graph (border i) inputs alt < lower 0 i+b.2.1.countP (isMaskedConstant (border i))))=true ∧
      Cuts.feasibleB false inputs alt=true) ∧ covers (border i) alt b.2.1=true)
  obtain ⟨slice,span⟩ := geometry low i
  obtain ⟨f,roots,inside,base,nc,floor⟩ := slice
  obtain ⟨bank,paid,supply⟩ := build (T:=graph) (mask:=border i) increasing_inputs base alt (Cuts.feasible_ok feas)
  have old : ∀ w∈b.2.1, backed graph (border i) f bank w := by
    intro w hw
    obtain ⟨v,hv,beats⟩ := List.any_eq_true.mp (List.all_eq_true.mp dominating w hw)
    have proxy : backed graph (border i) f bank v := by
      rcases List.mem_cons.mp hv with rfl|hv
      · apply backed_const (b:=false)
        funext r
        simp [observe,bit,zero]
      · rcases List.mem_cons.mp hv with rfl|hv
        · apply backed_const (b:=true)
          funext r
          change (BitVec.allOnes 512).getLsbD r.val=true
          rw [BitVec.getLsbD_allOnes]
          simp
        · exact supply v hv
    obtain ⟨z,⟨inc,better⟩,known⟩ := proxy
    exact ⟨z,⟨inc,better_trans (dominatesB_ok beats) better⟩,known⟩
  have h := boundary_bound span b.2.1 nd (Trace.forget ranked) inside nc floor paid old
  by_cases last : i.val=78
  · rw [if_pos last] at cut
    have x := of_decide_eq_true cut
    simp only [lower,if_pos last] at h
    omega
  · rw [if_neg last] at cut
    have x := of_decide_eq_true cut
    simp only [lower,if_neg last] at h x
    omega
end Substitute

namespace ShortProgram
open PublicFloor Verification

def decode : Nat → Nat → List Choice
  | 0,_ => []
  | n+1,c => if c<512 then [] else
    let prev := decode n (c/512)
    let pool := inputs ++ (prev.reverse.map choiceVal)
    let g : Choice := ((c/256)%2,pool.getD (c % 16) zero,pool.getD ((c/16)%16) zero)
    g::prev
end ShortProgram

namespace Orientation
open PublicFloor Trace Inputs Verification
open Load (Board)

def swapped (g : Step) : Step := (flipOp g.1,g.2.2,g.2.1)

theorem primary : ∀ u : Bool, inputs.all (fun a => inputs.all (fun b =>
    (opsOf u).all (fun d => rank u (d,a,b)==rank u (swapped (d,a,b)))))=true := by decide +kernel

theorem grade {u g} (leg : good u g) : rank u g=rank u (swapped g) := by
  obtain ⟨d,a,b⟩ := g
  by_cases h : a∈inputs ∧ b∈inputs
  · exact beq_iff_eq.mp (List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp (primary u) a h.1) b h.2) d (opsOf_mem leg.1))
  · have other : ¬(b∈inputs ∧ a∈inputs) := fun t => h ⟨t.2,t.1⟩
    simp only [rank_eq,oldRank,swapped,h,other,if_false]

theorem good_swap {u g} (leg : good u g) : good u (swapped g) :=
  ⟨(flip_flip leg.1).1,leg.2.2.1,leg.2.1,Ne.symm leg.2.2.2⟩

theorem signal {u g} (leg : good u g) : result g=result (swapped g) := bin_flip leg.1 _ _

theorem children (ws : List Sig) {u g} (leg : good u g) (ka kb : Bool) :
    Moves.child ws g ka kb=Moves.child ws (swapped g) kb ka := by
  have same : Moves.keep g.2.1 g.2.2 ka kb=Moves.keep g.2.2 g.2.1 kb ka := by
    funext w
    exact Bool.and_comm _ _
  simp only [Moves.child,signal leg,same,swapped]

theorem turn {u m cap b g ka kb} (leg : good u g)
    (bounded : closed u m cap (next u b (swapped g) kb ka)) : closed u m cap (next u b g ka kb) := by
  intro k fit history run
  apply bounded k fit history
  change Ranked u graph (rank u) (rank u (swapped g)) k (Moves.child b.2.1 (swapped g) kb ka).toFinset
  rw [←grade leg,←children b.2.1 leg ka kb]
  exact run

theorem sorted {u m cap} {b : Board} (miss : graph∉b.2.1)
    (step : ∀ (g : Step) (ka kb : Bool), good u g → b.1≤rank u g →
      g.2.1∈b.2.1 → g.2.2∈b.2.1 → g.2.1.toNat<g.2.2.toNat →
      result g∉b.2.1 → closed u m (cap-1) (next u b g ka kb)) : closed u m cap b := by
  apply node miss
  intro g ka kb leg order a c fresh
  by_cases lt : g.2.1.toNat<g.2.2.toNat
  · exact step g ka kb leg order a c lt fresh
  · have ne : g.2.1.toNat≠g.2.2.toNat := fun eq => leg.2.2.2 (BitVec.eq_of_toNat_eq eq)
    apply turn leg
    apply step (swapped g) kb ka (good_swap leg) (grade leg ▸ order) c a (by change g.2.2.toNat<g.2.1.toNat; omega)
    exact (signal leg) ▸ fresh
end Orientation

namespace Grid
abbrev W := BitVec 512
end Grid

namespace Grid
def retained (a b : W) (ka kb : Bool) (v : W) := (ka || v != a) && (kb || v != b)

theorem retained_count {ws : List W} (p : W → Bool) (nd : ws.Nodup)
    {a b : W} (hab : a≠b) (ha : a∈ws) (hb : b∈ws) (ka kb : Bool) :
    (ws.filter (retained a b ka kb)).countP p + (!ka && p a).toNat + (!kb && p b).toNat = ws.countP p := by
  have first := List.perm_cons_erase ha
  have second := List.perm_cons_erase ((List.mem_erase_of_ne hab.symm).mpr hb : b∈ws.erase a)
  let tail := (ws.erase a).erase b
  have perm : ws.Perm (a::b::tail) := first.trans (second.cons a)
  have sorted := perm.nodup_iff.mp nd
  obtain ⟨nota,sorted⟩ := List.nodup_cons.mp sorted
  obtain ⟨notb,_⟩ := List.nodup_cons.mp sorted
  have only : tail.filter (retained a b ka kb)=tail := by
    apply List.filter_eq_self.mpr
    intro w hw
    have x : w≠a := by rintro rfl; exact nota (List.mem_cons_of_mem _ hw)
    have y : w≠b := by rintro rfl; exact notb hw
    simp [retained,x,y]
  rw [(perm.filter _).countP_eq p,perm.countP_eq p]
  cases ka <;> cases kb <;> cases pa : p a <;> cases pb : p b <;>
    simp [List.filter_cons,retained,hab,Ne.symm hab,only,pa,pb,List.countP_cons] <;> omega
end Grid

namespace Rates
open PublicFloor Project Atlas Verification
open Load (Board)

abbrev Account := Fin 79 × Sig × Nat × Nat

abbrev Charge := Sig × Nat × Nat

def account (u : Bool) (cap : Nat) (b : Board) (i : Fin 79) : Account :=
  let mask := if u then domain i else border i
  let before := if u then price true inputs mask b.2.2 else Mono.paidCount graph mask inputs b.2.2
  let lhs := if i.val=78 then before else cap+before
  let rhs := if i.val=78 then b.2.2.length+1 else lower 0 i
  (i,mask,lhs,rhs)

def charge (u : Bool) (bank : List Sig) (g : Choice) (v : Account) : Charge :=
  let (i,mask,lhs,rhs) := v
  let reuse := if u then free true inputs mask g else Mono.reused graph mask bank g
  (mask,lhs+(!reuse).toNat,rhs)

def violation (ws : List Sig) (q : Charge) :=
  decide (q.2.1 < q.2.2 + ws.countP (isMaskedConstant q.1))

theorem price_cons (u raw d g gs) : price u raw d (g::gs)=price u raw d gs+(!(free u raw d g)).toNat := by
  cases eq : free u raw d g <;> simp [price,List.countP_cons,eq]

theorem agrees (u cap b g ka kb i) :
    violation (next u b g ka kb).2.1 (charge u (wires inputs b.2.2) g (account u cap b i)) =
    Cuts.check u cap (next u b g ka kb) i := by
  cases u <;> by_cases last : i.val=78 <;>
    simp [next,violation,charge,account,Cuts.check,price_cons,Mono.paidCount,last,Nat.add_assoc]
end Rates

namespace Allowances
open PublicFloor Verification Rates Project
open Load (Board)

abbrev Column := Account × Nat

abbrev Test := Nat × Nat × Bool × Bool

def row (u : Bool) (cap : Nat) (b : Board) (i : Fin 79) : Column :=
  let ac := account u cap b i
  (ac,b.2.1.countP (isMaskedConstant ac.2.1))

def rate (u : Bool) (gs : List Sig) (g : Choice) (x : Column) : Test :=
  let (mask,lhs,rhs) := charge u gs g x.1
  let p := isMaskedConstant mask
  (lhs,rhs+x.2+(p (choiceVal g)).toNat,p g.2.1,p g.2.2)

def beyond (ka kb : Bool) (v : Test) :=
  decide (v.1+(!ka && v.2.2.1).toNat+(!kb && v.2.2.2).toNat<v.2.1)

theorem counted (xs : List Sig) (g : Choice) (ka kb : Bool) (p : Sig → Bool) :
    (Moves.child xs g ka kb).countP p =
      (xs.filter (Grid.retained g.2.1 g.2.2 ka kb)).countP p + (p (choiceVal g)).toNat := by
  rw [Moves.child,Moves.ordered,(Order.permutation _).countP_eq,List.countP_cons]
  cases h : p (choiceVal g)
  · change _+(if p (choiceVal g) then 1 else 0)=_+_
    rw [h]; rfl
  · change _+(if p (choiceVal g) then 1 else 0)=_+_
    rw [h]; rfl

theorem soundAt {u cap} {b : Board} {g : Choice} {ka kb i} (nd : b.2.1.Nodup)
    (ne : g.2.1≠g.2.2) (ha : g.2.1∈b.2.1) (hb : g.2.2∈b.2.1)
    (test : beyond ka kb (rate u (wires inputs b.2.2) g (row u cap b i))=true) :
    Cuts.check u cap (next u b g ka kb) i=true := by
  rw [←agrees u cap b g ka kb i]
  let ac := account u cap b i
  let c := charge u (wires inputs b.2.2) g ac
  let p := isMaskedConstant ac.2.1
  have pass : c.2.1+(!ka && p g.2.1).toNat+(!kb && p g.2.2).toNat<
      c.2.2+b.2.1.countP p+(p (choiceVal g)).toNat := of_decide_eq_true test
  change decide (c.2.1<c.2.2+(Moves.child b.2.1 g ka kb).countP p)=true
  apply decide_eq_true
  rw [counted]
  have ct := Grid.retained_count p nd ne ha hb ka kb
  omega

def bank (u cap b pal) := (78::pal).map (row u cap b)

def costs (u : Bool) (gs : List Sig) (g : Choice) (rs : List Column) := rs.map (rate u gs g)

theorem exclude {u m cap} {b : Board} {g ka kb pal} (low : Lower u inputs graph m)
    (nd : b.2.1.Nodup) (ne : g.2.1≠g.2.2) (ha : g.2.1∈b.2.1) (hb : g.2.2∈b.2.1)
    (safe : Cuts.certified u (next u b g ka kb)=true)
    (test : (costs u (wires inputs b.2.2) g (bank u cap b pal)).any (beyond ka kb)=true) :
    closed u m cap (next u b g ka kb) := by
  obtain ⟨_,m1,bad⟩ := List.any_eq_true.mp test
  obtain ⟨_,m2,rfl⟩ := List.mem_map.mp m1
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp m2
  exact cofactor low safe i (soundAt nd ne ha hb bad)
end Allowances

namespace Fast
open PublicFloor Trace Inputs Verification Node Project
open Load (Board)

def wideB (cap n : Nat) (ka kb : Bool) := decide (cap+1+(!ka).toNat+(!kb).toNat<n+1)

theorem wide_ok {u m cap} {b : Board} {g ka kb} (nd : b.2.1.Nodup)
    (leg : good u g) (a : g.2.1∈b.2.1) (c : g.2.2∈b.2.1)
    (safe : Cuts.certified u (next u b g ka kb)=true) (hit : wideB cap b.2.1.length ka kb=true) :
    closed u m cap (next u b g ka kb) := by
  have cost := Grid.retained_count (fun _ => true) nd leg.2.2.2 a c ka kb
  have child := Allowances.counted b.2.1 g ka kb (fun _ => true)
  simp only [List.countP_true,Bool.and_true,Bool.toNat_true] at cost child
  have excess : cap+1+(!ka).toNat+(!kb).toNat<b.2.1.length+1 := of_decide_eq_true hit
  have good : (next u b g ka kb).2.1.Nodup :=
    of_decide_eq_true (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp safe).1).2
  apply wide
  rw [List.toFinset_card_of_nodup good]
  change cap+1<(Moves.child b.2.1 g ka kb).length
  omega

abbrev Receipts := List Near.Hint

def given (u : Bool) (cap : Nat) (b : Board) (notes : Receipts) := notes.any (Near.test u cap b.2.1)

theorem given_ok {u m cap b notes} (hit : given u cap b notes=true) : closed u m cap b := by
  obtain ⟨v,_,valid⟩ := List.any_eq_true.mp hit
  intro k le _ run
  exact Near.sound valid k le (forget run)
end Fast

namespace Separator
open PublicFloor Trace Verification
open Load (Board)

def columns (u neg : Bool) (i : Nat) : Bits :=
  let t := ((if u then Quick.sRaw else Quick.mRaw).getD i (0,0))
  let w := if neg then t.2 else t.1
  let n := if u then 402 else 144
  BitVec.ofNat 768 (if w.testBit 0 then w ||| ((1<<<768)-(1<<<n)) else w)

abbrev positive (u : Bool) := asRow (columns u false)

abbrev negative (u : Bool) := asRow (columns u true)

theorem samples (u : Bool) : properPairs graph (positive u) (negative u) := by
  have eq : chartGoal 511=graph := by decide +kernel
  rw [←eq]
  apply chart_pairs <;> cases u <;> decide +kernel

def mark (u : Bool) (bank : List Decor) (w : Sig) : Decor :=
  (w,match bank.find? (fun a => a.1==w) with
     | some a => a.2
     | none => pairSig (positive u) (negative u) w)

theorem mark_ok {u bank} (fit : ∀ a∈bank, faithful (positive u) (negative u) a) (w : Sig) :
    faithful (positive u) (negative u) (mark u bank w) := by
  unfold faithful mark
  split
  next a eq =>
    have same : a.1=w := beq_iff_eq.mp (List.find?_some (p:=fun (x : Decor) => x.1==w) eq)
    simpa only [faithful,same] using fit _ (List.mem_of_find?_eq_some eq)
  next => rfl

def bank (u : Bool) : List Choice → List Decor
  | [] => rawDecor 511 (columns u false) (columns u true)
  | g::gs =>
    let old := bank u gs
    dbin g.1 (mark u old g.2.1) (mark u old g.2.2)::old

theorem bank_ok (u : Bool) (gs : List Choice) : ∀ a∈bank u gs, faithful (positive u) (negative u) a := by
  induction gs with
  | nil => exact raw_faithful 511 _ _
  | cons g gs ih =>
    intro a mem
    rcases List.mem_cons.mp mem with rfl|inBank
    · exact faithful_bin g.1 (mark_ok ih _) (mark_ok ih _)
    · exact ih _ inBank

def marked (u : Bool) (b : Board) := b.2.1.map (mark u (bank u b.2.2))

theorem words (u : Bool) (b : Board) : (marked u b).map Prod.fst=b.2.1 := by
  simp [marked,mark,List.map_map,Function.comp_def]

theorem marked_ok (u : Bool) (b : Board) : ∀ a∈marked u b, faithful (positive u) (negative u) a := by
  intro a mem
  obtain ⟨w,_,rfl⟩ := List.mem_map.mp mem
  exact mark_ok (bank_ok u b.2.2) w

theorem children {ws : List Decor} {a b : Decor} (nd : (ws.map Prod.fst).Nodup) (ha : a∈ws) (hb : b∈ws)
    (d : Nat) (ka kb : Bool) :
    (moveFront ws d a b ka kb).toFinset =
      (Moves.child (ws.map Prod.fst) (d,a.1,b.1) ka kb).toFinset := by
  rw [Moves.child,Moves.ordered_set]
  ext w
  simp only [moveFront,List.mem_toFinset,List.mem_cons,kept_value nd ha hb,List.mem_filter,Moves.keep,
    Bool.and_eq_true,Bool.or_eq_true,bne_iff_ne,result,dbin]
  tauto

def misses (u : Bool) (cov : Cov) (a b z : Signals) (ka kb : Bool) :=
  (restCov cov (column (!u) a) (column (!u) b) ka kb ||| column (!u) z) != BitVec.allOnes 768

theorem impossible {u ws d} {a b : Decor} {ka kb} (nd : (ws.map Prod.fst).Nodup)
    (ha : a∈ws) (hb : b∈ws) (ne : a≠b) (fit : ∀ x∈ws, faithful (positive u) (negative u) x)
    (test : misses u (coverage (!u) ws) a.2 b.2 (dbin d a b).2 ka kb=true) (k : Nat) :
    ¬Live u graph k (Moves.child (ws.map Prod.fst) (d,a.1,b.1) ka kb).toFinset := by
  rw [←children nd ha hb]
  intro run
  have sep := cover_required run (pair_sep (samples u))
  let rest := delTwo ws a b ka kb
  have fr := cov_word (!u) rest (fun x hx => fit x ((keep_sub ws a b ka kb).subset hx))
  have kept : (coverage (!u) rest).1 = restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb :=
    cover_two (!u) a b ha hb ne ka kb
  have output := faithful_bin d (fit _ ha) (fit _ hb)
  change (dbin d a b).2=pairSig (positive u) (negative u) (dbin d a b).1 at output
  change column (!u) (pairSig (positive u) (negative u) (dbin d a b).1) |||
    covered (!u) (pairSig (positive u) (negative u)) (rest.map Prod.fst) = _ at sep
  rw [←output,←fr,kept,BitVec.or_comm] at sep
  exact (bne_iff_ne.mp test) sep
end Separator

namespace Packed
open PublicFloor Trace Inputs Verification Project Node
open Load (Board)

abbrev Pair := Decor × Decor
abbrev WideFee := Nat × Nat × Nat × Nat × Nat

def pairs (u : Bool) (d : Nat) (b : Board) (xs : List Decor) :=
  xs.flatMap fun a => xs.filterMap fun c =>
    let g : Step := (d,a.1,c.1)
    if a.1.toNat<c.1.toNat ∧ b.1≤rank u g ∧ result g∉b.2.1 then some (a,c) else none

def embed (x : Sig) : Bits := BitVec.ofNat 768 x.toNat
def cleanFlags (r full x : Nat) := fullMarks r (full ^^^ x)

def constFlags (r full mask x : Nat) :=
  let y := mask &&& x
  cleanFlags r full y ||| cleanFlags r full (mask ^^^ y)

def quota (r threshold a b c d : Nat) :=
  if threshold=0 then r else if threshold=1 then a ||| b ||| c ||| d
  else if threshold=2 then (a &&& b) ||| (c &&& d) ||| ((a ||| b) &&& (c ||| d))
  else if threshold=3 then ((a &&& b) &&& (c ||| d)) ||| ((a ||| b) &&& (c &&& d))
  else if threshold=4 then a &&& b &&& c &&& d else 0

def monoFree (r full : Nat) (mask : Sig) (zError : Nat) (ws : List Sig) :=
  ws.foldl (fun flags v =>
    flags ||| cleanFlags r full ((((v ^^^ graph) &&& mask).toNat*r) &&& zError)) 0

def signedFree (r full mask a b z : Nat) :=
  let eq := fun v => constFlags r full mask (z ^^^ v)
  (zero::inputs).foldl (fun flags w => flags ||| eq (w.toNat*r)) (eq a ||| eq b)

def fee (u : Bool) (r full a b z zError : Nat) (ws : List Sig) (col : Allowances.Column) : WideFee :=
  let (_,mask,base,floor) := col.1
  let domain := mask.toNat*r
  let reuse := if u then signedFree r full domain a b z else monoFree r full mask zError ws
  (base+4-(floor+col.2),reuse,constFlags r full domain z,constFlags r full domain a,constFlags r full domain b)

def denied (r : Nat) (ka kb : Bool) (f : WideFee) :=
  let (t,free,c,a,b) := f
  quota r t free c (if ka then r else r ^^^ a) (if kb then r else r ^^^ b)

def wordOp (d a b : Nat) :=
  if d=0 then a &&& b else if d=1 then a ||| b else if d=2 then a ^^^ (a &&& b) else b ^^^ (a &&& b)

def operation (u : Bool) (cap d : Nat) (b : Board) (regs : List Allowances.Column) (cov : Cov)
    (xs : List Decor) (arcs : List Arc) (future : Future) (notes : Fast.Receipts) :=
  let ps := pairs u d b xs
  let r := units ps.length
  let full := r*((1<<<768)-1)
  let a := combineLanes (fun p : Pair => embed p.1.1) ps
  let c := combineLanes (fun p : Pair => embed p.2.1) ps
  let z := wordOp d a c
  let err := z ^^^ ((~~~graph).toNat*r)
  let ws := zero::one::wires inputs b.2.2
  let fees := regs.map (fee u r full a c z err ws)
  let aa := packedSig (fun p : Pair => p.1.2) ps
  let cc := packedSig (fun p : Pair => p.2.2) ps
  let az := packedColumn (!u) aa
  let cz := packedColumn (!u) cc
  let out := packedColumn (!u) (packedOp d aa cc)
  let pc : PackedCov := (cov.1.toNat*r,cov.2.1.toNat*r,cov.2.2.toNat*r)
  four fun ka kb =>
    if Fast.wideB (cap-1) b.2.1.length ka kb then true else
    let pass := fullMarks r (takePacked pc az cz ka kb ||| out)
    let ban := fees.foldl (fun mask f => mask ||| denied r ka kb f) 0
    onMarks (fun p : Pair =>
      let g : Step := (d,p.1.1,p.2.1)
      let after := next u b g ka kb
      aliasB after (key b.2.1 g ka kb) arcs future || (after.2.1.contains zero || Fast.given u (cap-1) after notes))
      (pass ^^^ (pass &&& ban)) ps

def validate (u : Bool) (cap : Nat) (b : Board) (pal : List (Fin 79))
    (arcs : List Arc) (future : Future) (notes : Fast.Receipts) :=
  let xs := Separator.marked u b
  let cov := coverage (!u) xs
  let regs := (Allowances.bank u (cap-1) b pal).filter
    fun v => decide (v.1.2.2.1 < v.1.2.2.2+v.2+1)
  (Cuts.certified u b && !(b.2.1.contains graph)) &&
    (opsOf u).all (fun d => operation u cap d b regs cov xs arcs future notes)

end Packed

namespace Packed
open PublicFloor

theorem broadcast {α : Type} (v : Bits) (xs : List α) :
    combineLanes (fun _ : α => v) xs = v.toNat*units xs.length := by
  induction xs with
  | nil => simp [combineLanes,units]
  | cons a xs ih =>
    simp only [combineLanes,List.length_cons,units,lanePlace,ih]
    ring

theorem embed_nat (v : Sig) : (embed v).toNat=v.toNat := by
  exact Nat.mod_eq_of_lt (lt_of_lt_of_le v.isLt (by decide +kernel))

theorem embed_at (v : Sig) (i : Nat) : (embed v).getLsbD i=v.getLsbD i := by
  change (embed v).toNat.testBit i=v.toNat.testBit i
  rw [embed_nat]

theorem embed_and (v w : Sig) : embed (v &&& w)=embed v &&& embed w := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [embed_at,BitVec.getLsbD_and]

theorem embed_or (v w : Sig) : embed (v ||| w)=embed v ||| embed w := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [embed_at,BitVec.getLsbD_or]

theorem embed_xor (v w : Sig) : embed (v ^^^ w)=embed v ^^^ embed w := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [embed_at,BitVec.getLsbD_xor]

theorem remove_bits {n : Nat} (x y : BitVec n) : x ^^^ (x &&& y)=x &&& ~~~y := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_xor,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases x.getLsbD i <;> cases y.getLsbD i <;> rfl

abbrev packedWords {α : Type} (f : α → Sig) (xs : List α) :=
  combineLanes (fun x => embed (f x)) xs

theorem same_words {α : Type} (v : Sig) (xs : List α) :
    packedWords (fun _ : α => v) xs=v.toNat*units xs.length := (broadcast _ _).trans (by rw [embed_nat])

theorem words_and {α : Type} (a b : α → Sig) (xs : List α) :
    packedWords a xs &&& packedWords b xs=packedWords (fun x => a x &&& b x) xs := by
  simp only [packedWords,lanes_and,embed_and]

theorem words_or {α : Type} (a b : α → Sig) (xs : List α) :
    packedWords a xs ||| packedWords b xs=packedWords (fun x => a x ||| b x) xs := by
  simp only [packedWords,lanes_or,embed_or]

theorem words_xor {α : Type} (a b : α → Sig) (xs : List α) :
    packedWords a xs ^^^ packedWords b xs=packedWords (fun x => a x ^^^ b x) xs := by
  simp only [packedWords,lanes_xor,embed_xor]

theorem operation_words {α : Type} (a b : α → Sig) (d : Nat) (xs : List α) :
    wordOp d (packedWords a xs) (packedWords b xs)=packedWords (fun x => bin d (a x) (b x)) xs := by
  by_cases h0 : d=0
  · simp only [wordOp,bin,h0,ite_true,words_and]
  by_cases h1 : d=1
  · subst d; simp only [wordOp,bin,show ¬(1 : Nat)=0 by decide,ite_true,ite_false,words_or]
  by_cases h2 : d=2
  · subst d; simp only [wordOp,bin,show ¬(2 : Nat)=0 by decide,show ¬(2 : Nat)=1 by decide,
      ite_true,ite_false,words_xor,words_and,remove_bits]
  · simp only [wordOp,bin,h0,h1,h2,ite_false,words_and,words_xor]
    congr 1
    funext x
    rw [BitVec.and_comm (a x),remove_bits,BitVec.and_comm]

def reflects {α : Type} (xs : List α) (w : Nat) (f : α → Bool) :=
  ∀ (i : Nat) (hi : i<xs.length), w.testBit (769*i)=f xs[i]

theorem ones_xor (v : Bits) :
    (BitVec.allOnes 768 ^^^ v == BitVec.allOnes 768)=(v==0) := by
  by_cases eq : v=0
  · simp [eq]
  · have ne : BitVec.allOnes 768 ^^^ v≠BitVec.allOnes 768 := by
      intro same
      apply eq
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      have b := congrArg (fun w : Bits => w.getLsbD i) same
      simp only [BitVec.getLsbD_xor,BitVec.getLsbD_allOnes,hi,decide_true,BitVec.getLsbD_zero] at b ⊢
      cases val : v.getLsbD i <;> simp_all
    exact (beq_eq_false_iff_ne.mpr ne).trans (beq_eq_false_iff_ne.mpr eq).symm

set_option maxRecDepth 6000 in
theorem reflect_clean {α : Type} (xs : List α) (f : α → Bits) :
    reflects xs (cleanFlags (units xs.length) (units xs.length*((1<<<768)-1)) (combineLanes f xs))
      (fun a => f a==0) := by
  intro i hi
  have eq : units xs.length*((1<<<768)-1)=combineLanes (fun _ : α => BitVec.allOnes 768) xs := by
    rw [broadcast,Nat.mul_comm]; rfl
  rw [cleanFlags,eq,lanes_xor,mark_at _ _ _ hi,ones_xor]

theorem embed_zero_test (v : Sig) : ((embed v)==(0 : Bits))=(v==zero) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq]
  constructor
  · intro h
    apply BitVec.eq_of_toNat_eq
    calc v.toNat = (embed v).toNat := (embed_nat v).symm
         _ = (0 : Bits).toNat := congrArg (fun w : Bits => w.toNat) h
         _ = zero.toNat := by decide +kernel
  · rintro rfl
    decide +kernel

set_option maxRecDepth 6000 in
theorem reflect_word_zero {α : Type} (xs : List α) (f : α → Sig) :
    reflects xs (cleanFlags (units xs.length) (units xs.length*((1<<<768)-1)) (packedWords f xs))
      (fun a => f a==zero) := by
  intro i hi
  exact (reflect_clean xs (fun a => embed (f a)) i hi).trans (embed_zero_test _)

theorem quota_at {r t a b c d i : Nat} (unit : r.testBit i=true) :
    (quota r t a b c d).testBit i=decide (t ≤
      (a.testBit i).toNat+(b.testBit i).toNat+(c.testBit i).toNat+(d.testBit i).toNat) := by
  have split_ : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ 4<t := by omega
  by_cases high : 4<t
  · have large : ∀ j≤4, t≠j := by omega
    simp only [quota,large 0 (by decide),large 1 (by decide),large 2 (by decide),large 3 (by decide),
      large 4 (by decide),ite_false,Nat.zero_testBit]
    have lim (x : Bool) : x.toNat≤1 := by cases x <;> decide
    symm
    apply decide_eq_false
    have ha := lim (a.testBit i)
    have hb := lim (b.testBit i)
    have hc := lim (c.testBit i)
    have hd := lim (d.testBit i)
    omega
  rcases split_ with rfl|rfl|rfl|rfl|rfl|no
  all_goals try contradiction
  all_goals cases h1 : a.testBit i <;> cases h2 : b.testBit i <;>
    cases h3 : c.testBit i <;> cases h4 : d.testBit i <;>
    simp_all [quota,Nat.testBit_and,Nat.testBit_or] <;> omega
end Packed

namespace Packed
open PublicFloor Project

theorem xor_zero_test (a b : Sig) : ((a ^^^ b)==zero)=(b==a) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq]
  exact BitVec.xor_eq_zero_iff.trans eq_comm

theorem reflect_const {α : Type} (xs : List α) (m : Sig) (z : α → Sig) :
    reflects xs (constFlags (units xs.length) (units xs.length*((1<<<768)-1))
      (m.toNat*units xs.length) (packedWords z xs)) (fun p => isMaskedConstant m (z p)) := by
  intro i hi
  simp only [constFlags,← same_words m xs,words_and,words_xor,Nat.testBit_or,
    reflect_word_zero xs _ i hi,xor_zero_test,isMaskedConstant,masked]
  rw [BitVec.and_comm m (z xs[i])]

theorem fold_flags {α : Type} (g : α → Nat) (ws : List α) (start i : Nat) :
    (ws.foldl (fun w a => w ||| g a) start).testBit i =
      (start.testBit i || ws.any (fun a => (g a).testBit i)) := by
  induction ws generalizing start with
  | nil => simp
  | cons a ws ih => simp only [List.foldl_cons,List.any_cons,ih,Nat.testBit_or,Bool.or_assoc]

theorem mono_equation (w z m : Sig) :
    (((w ^^^ graph) &&& m) &&& (z ^^^ ~~~graph)) =
      (((w ^^^ graph) &&& ~~~(z ^^^ graph)) &&& m) := by
  have flip : z ^^^ ~~~graph= ~~~(z ^^^ graph) := BitVec.not_xor_right.symm
  rw [flip,BitVec.and_assoc,BitVec.and_comm m,←BitVec.and_assoc]

theorem reflect_mono {α : Type} (xs : List α) (m : Sig) (z : α → Sig) (ws : List Sig) :
    reflects xs (monoFree (units xs.length) (units xs.length*((1<<<768)-1)) m
      (packedWords z xs ^^^ ((~~~graph).toNat * units xs.length)) ws)
      (fun p => ws.any (fun w => Mono.dominatesB graph m w (z p))) := by
  intro i hi
  rw [monoFree,fold_flags,Nat.zero_testBit,Bool.false_or]
  apply congrArg (List.any ws)
  funext w
  rw [←same_words ((w ^^^ graph) &&& m) xs,←same_words (~~~graph) xs,words_xor,words_and,
    reflect_word_zero xs _ i hi]
  dsimp only
  rw [mono_equation]
  rfl

theorem masked_xor (m x y : Sig) : masked m (x ^^^ y)=masked m x ^^^ masked m y := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [masked,BitVec.getLsbD_and,BitVec.getLsbD_xor]
  cases m.getLsbD i <;> cases x.getLsbD i <;> cases y.getLsbD i <;> rfl

def signedEq (m z w : Sig) := masked m w==masked m z || masked m w==masked m (neg z)

theorem xor_target (x y m : Sig) : ((x ^^^ y)==m)=(y==(m ^^^ x)) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq]
  constructor
  · intro e
    rw [←e,BitVec.xor_comm x y,BitVec.xor_assoc,BitVec.xor_self,BitVec.xor_zero]
  · intro e
    rw [e,BitVec.xor_comm m x,←BitVec.xor_assoc,BitVec.xor_self,BitVec.zero_xor]

theorem const_equiv (m z w : Sig) : isMaskedConstant m (z ^^^ w)=signedEq m z w := by
  rw [isMaskedConstant,masked_xor,xor_zero_test,xor_target,signedEq,masked_comp]

theorem any_disj {α : Type} (ws : List α) (p q : α → Bool) :
    ws.any (fun w => p w || q w)=(ws.any p || ws.any q) := by
  induction ws with
  | nil => rfl
  | cons a ws ih => simp only [List.any_cons,ih]; ac_rfl

theorem signed_zero (m z : Sig) :
    signedEq m z zero=(masked m z==zero || masked m z==m) := by
  unfold signedEq
  have empty_ : masked m zero=zero := by simp [masked,zero]
  rw [empty_,masked_comp,Bool.beq_comm (a:=zero) (b:=masked m z),
    Bool.beq_comm (a:=zero) (b:=m ^^^ masked m z),xor_zero_test]

theorem signed_available (m z a b : Sig) (ws : List Sig) :
    ((signedEq m z a || signedEq m z b) ||
      (zero::ws).any (signedEq m z)) = availableB true m (a::b::ws) z := by
  simp only [availableB,List.any_cons,signed_zero,List.any_map,Function.comp_def,Bool.true_and]
  unfold signedEq
  rw [any_disj]
  ac_rfl

theorem reflect_signed {α : Type} (xs : List α) (m : Sig) (a b z : α → Sig) :
    reflects xs (signedFree (units xs.length) (units xs.length*((1<<<768)-1))
      (m.toNat*units xs.length) (packedWords a xs) (packedWords b xs) (packedWords z xs))
      (fun p => availableB true m (a p::b p::inputs) (z p)) := by
  intro i hi
  rw [signedFree,fold_flags,Nat.testBit_or]
  dsimp only
  rw [words_xor,words_xor,reflect_const xs _ _ i hi,reflect_const xs _ _ i hi]
  dsimp only
  rw [const_equiv,const_equiv,←signed_available]
  apply congrArg (fun v : Bool => (signedEq m (z xs[i]) (a xs[i]) || signedEq m (z xs[i]) (b xs[i])) || v)
  apply congrArg (List.any (zero::inputs))
  funext w
  rw [←same_words w xs,words_xor,reflect_const xs _ _ i hi]
  exact const_equiv _ _ _

theorem fee_reflects {α : Type} (xs : List α) (a b : α → Sig) (d : Nat) (u ka kb : Bool)
    (pool : List Sig) (c : Allowances.Column) :
    let r := units xs.length
    let z := fun p => bin d (a p) (b p)
    let f := fee u r (r*((1<<<768)-1)) (packedWords a xs) (packedWords b xs) (packedWords z xs)
      (packedWords z xs ^^^ ((~~~graph).toNat*r)) (zero::one::pool) c
    reflects xs (denied r ka kb f)
      (fun p => Allowances.beyond ka kb (Allowances.rate u pool (d,a p,b p) c)) := by
  obtain ⟨⟨_,m,base,floor⟩,cnt⟩ := c
  dsimp only
  intro i hi
  let z := fun p => bin d (a p) (b p)
  have zflag := reflect_const xs m z i hi
  have aflag := reflect_const xs m a i hi
  have bflag := reflect_const xs m b i hi
  have mono := reflect_mono xs m z (zero::one::pool) i hi
  have signed := reflect_signed xs m a b z i hi
  dsimp only [z] at zflag signed mono
  have un := unit_bit xs.length i hi
  have arithmetic (v x y zz : Bool) :
      decide (base+4-(floor+cnt) ≤ v.toNat+zz.toNat+
        (if ka then true else !x).toNat+(if kb then true else !y).toNat) =
      decide (base+(!v).toNat+(!ka && x).toNat+(!kb && y).toNat<floor+cnt+zz.toNat) := by
    apply decide_eq_decide.mpr
    cases ka <;> cases kb <;> cases v <;> cases x <;> cases y <;> cases zz <;>
      simp only [Bool.toNat_false,Bool.toNat_true,Bool.not_true,Bool.not_false,
        Bool.false_and,Bool.true_and,Bool.false_eq_true,ite_false,ite_true] <;> omega
  dsimp only [fee,denied]
  rw [quota_at un]
  simp only [apply_ite (fun n : Nat => n.testBit (769*i)),Nat.testBit_xor,
    un,zflag,aflag,bflag,signed,mono,Bool.true_xor]
  exact arithmetic (if u then availableB true m (a xs[i]::b xs[i]::inputs) (z xs[i])
    else (zero::one::pool).any (fun w => Mono.dominatesB graph m w (z xs[i])))
    (isMaskedConstant m (a xs[i])) (isMaskedConstant m (b xs[i])) (isMaskedConstant m (z xs[i]))
end Packed

namespace Packed
open PublicFloor Trace Inputs Verification Project Node
open Load (Board)

theorem mem_gate {u d} {b : Board} {xs : List Decor} {a c : Decor} (ha : a∈xs) (hc : c∈xs)
    (lt : a.1.toNat<c.1.toNat) (stage : b.1≤rank u (d,a.1,c.1))
    (fresh : result (d,a.1,c.1)∉b.2.1) : (a,c)∈pairs u d b xs := by
  apply List.mem_flatMap.mpr
  refine ⟨a,ha,List.mem_filterMap.mpr ⟨c,hc,?_⟩⟩
  simp [lt,stage,fresh]

abbrev signalA (p : Pair) := p.1.1

abbrev signalB (p : Pair) := p.2.1

abbrev resultAt (d : Nat) (p : Pair) := bin d p.1.1 p.2.1

abbrev gateAt (d : Nat) (p : Pair) : Step := (d,p.1.1,p.2.1)

def screen (xs : List Pair) (cov : Cov) (u : Bool) (d : Nat) (ka kb : Bool) :=
  let r := units xs.length
  let a := packedSig (fun p : Pair => p.1.2) xs
  let b := packedSig (fun p : Pair => p.2.2) xs
  let cv : PackedCov := (cov.1.toNat*r,cov.2.1.toNat*r,cov.2.2.toNat*r)
  fullMarks r (takePacked cv (packedColumn (!u) a) (packedColumn (!u) b) ka kb |||
    packedColumn (!u) (packedOp d a b))

theorem screen_spec (xs : List Pair) (cov : Cov) (u : Bool) (d : Nat) (ka kb : Bool) :
    reflects xs (screen xs cov u d ka kb) (fun p =>
      (restCov cov (column (!u) p.1.2) (column (!u) p.2.2) ka kb |||
        column (!u) (dbin d p.1 p.2).2)==BitVec.allOnes 768) := by
  have eq : (cov.1.toNat*units xs.length,cov.2.1.toNat*units xs.length,cov.2.2.toNat*units xs.length)
      = packedCov (fun _ : Pair => cov) xs := by
    simp only [packedCov,broadcast]
  intro i hi
  simp only [screen,eq,packed_op (fun p : Pair => p.1) (fun p : Pair => p.2),
    packed_column,takePacked_ok,lanes_or,mark_at _ _ _ hi]

def maskFees (xs : List Pair) (u : Bool) (d : Nat) (ka kb : Bool)
    (pool : List Sig) (cols : List Allowances.Column) :=
  let r := units xs.length
  let a := packedWords signalA xs
  let b := packedWords signalB xs
  let z := wordOp d a b
  let err := z ^^^ ((~~~graph).toNat*r)
  let fees := cols.map (fee u r (r*((1<<<768)-1)) a b z err (zero::one::pool))
  fees.foldl (fun flags f => flags ||| denied r ka kb f) 0

theorem fees_spec (xs : List Pair) (u : Bool) (d : Nat) (ka kb : Bool)
    (pool : List Sig) (cols : List Allowances.Column) :
    reflects xs (maskFees xs u d ka kb pool cols) (fun p =>
      (Allowances.costs u pool (gateAt d p) cols).any (Allowances.beyond ka kb)) := by
  intro i hi
  rw [maskFees,operation_words,fold_flags,Nat.zero_testBit,Bool.false_or]
  simp only [Allowances.costs,List.any_map,Function.comp_def]
  apply congrArg (List.any cols)
  funext c
  exact fee_reflects xs signalA signalB d u ka kb pool c i hi

def rows (u : Bool) (cap : Nat) (b : Board) (pal : List (Fin 79)) :=
  (Allowances.bank u cap b pal).filter fun c => decide (c.1.2.2.1<c.1.2.2.2+c.2+1)

def fallback (u : Bool) (cap d : Nat) (b : Board) (arcs : List Arc)
    (future : Future) (notes : Fast.Receipts) (ka kb : Bool) (p : Pair) :=
  let g := gateAt d p
  let after := next u b g ka kb
  aliasB after (key b.2.1 g ka kb) arcs future ||
    (after.2.1.contains zero || Fast.given u cap after notes)

theorem verified {u m cap b pal arcs future notes} (low : Lower u inputs graph m)
    (later : ∀ j d, future j=some d → closed u m (cap-1) d)
    (hit : validate u cap b pal arcs future notes=true) : closed u m cap b := by
  obtain ⟨first,all_⟩ := Bool.and_eq_true_iff.mp hit
  obtain ⟨safe,miss⟩ := Bool.and_eq_true_iff.mp first
  have nd : b.2.1.Nodup := of_decide_eq_true (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp safe).1).2
  apply Orientation.sorted (fun h => by simp only [List.contains_iff_mem.mpr h,Bool.not_true,Bool.false_eq_true] at miss)
  rintro ⟨d,a,c⟩ ka kb leg stage ina inc lt fresh
  let xs := Separator.marked u b
  let x := Separator.mark u (Separator.bank u b.2.2) a
  let y := Separator.mark u (Separator.bank u b.2.2) c
  have hx : x∈xs := List.mem_map_of_mem ina
  have hy : y∈xs := List.mem_map_of_mem inc
  let ps := pairs u d b xs
  obtain ⟨i,hi,at_⟩ := List.mem_iff_getElem.mp (mem_gate hx hy lt stage fresh : (x,y)∈ps)
  have child := Cuts.extend (ka:=ka) (kb:=kb) (phase':=rank u (d,a,c)) safe leg.1 ina inc fresh
  have gate := List.all_eq_true.mp all_ d (opsOf_mem leg.1)
  let cv := coverage (!u) xs
  let cols := rows u (cap-1) b pal
  let pool := wires inputs b.2.2
  let pass := screen ps cv u d ka kb
  let ban := maskFees ps u d ka kb pool cols
  change four (fun ka kb => if Fast.wideB (cap-1) b.2.1.length ka kb then true else
    let s := screen ps cv u d ka kb
    let v := maskFees ps u d ka kb pool cols
    onMarks (fallback u (cap-1) d b arcs future notes ka kb) (s ^^^ (s &&& v)) ps)=true at gate
  have ok := four_ok gate ka kb
  change (if Fast.wideB (cap-1) b.2.1.length ka kb then true else
    onMarks (fallback u (cap-1) d b arcs future notes ka kb) (pass ^^^ (pass &&& ban)) ps)=true at ok
  by_cases wide_ : Fast.wideB (cap-1) b.2.1.length ka kb=true
  · exact Fast.wide_ok nd leg ina inc child wide_
  rw [if_neg wide_] at ok
  have screen_ := screen_spec ps cv u d ka kb i hi
  rw [at_] at screen_
  by_cases eligible : pass.testBit (769*i)=true
  · by_cases cut : ban.testBit (769*i)=true
    · have price := fees_spec ps u d ka kb pool cols i hi
      rw [at_] at price
      have test := List.any_eq_true.mp (price.symm.trans cut)
      obtain ⟨_,entry,over⟩ := test
      obtain ⟨col,mem,rfl⟩ := List.mem_map.mp entry
      apply Allowances.exclude (pal:=pal) low nd leg.2.2.2 ina inc child
      exact List.any_eq_true.mpr ⟨_,List.mem_map_of_mem (List.mem_of_mem_filter mem),over⟩
    · have on_ : (pass ^^^ (pass &&& ban)).testBit (769*i)=true := by
        simp [Nat.testBit_xor,Nat.testBit_and,eligible,Bool.eq_false_iff.mpr cut]
      have bk := PublicFloor.marked_ok _ _ ps i hi on_ ok
      rw [at_] at bk
      rcases Bool.or_eq_true_iff.mp bk with link|other
      · exact alias_ok later link
      · rcases Bool.or_eq_true_iff.mp other with zero_|hint
        · exact trivial_ok child (Bool.or_eq_true_iff.mpr (Or.inl zero_))
        · exact Fast.given_ok hint
  · have cross_ : Separator.misses u cv x.2 y.2 (dbin d x y).2 ka kb=true := by
      unfold Separator.misses
      apply bne_iff_ne.mpr
      exact fun eq => eligible (screen_.trans (beq_iff_eq.mpr eq))
    have ne : x≠y := fun e => leg.2.2.2 (congrArg Prod.fst e)
    intro k _ _ run
    have cut := Separator.impossible ((Separator.words u b).symm ▸ nd)
      hx hy ne (Separator.marked_ok u b) cross_ k
    rw [Separator.words] at cut
    exact cut (forget run)
end Packed

namespace ColorAxes
open PublicFloor
open PartitionBits (Slot A)
open Load (Board)

def collapse (v jump : Nat) :=
  let two := v ||| (v >>> jump)
  let four := two ||| (two >>> (2*jump))
  let eight := four ||| (four >>> (4*jump))
  eight ||| (four >>> (8*jump))

def rowMarks := ((1<<<144)-1)/4095

def axes (unique : Bits) (a : Decor) :=
  let t := (unique &&& column true a.2).toNat &&& ((1<<<144)-1)
  (collapse t 1 &&& rowMarks,collapse t 12 &&& 4095)

def collisions (ws : List Sig) (records : Array (Nat × Nat)) :=
  let slots := (List.finRange 12).take ws.length
  let active := slots.filter fun i => let p := records[i.val]?.getD (0,0); p.1!=0 && p.2!=0
  PartitionBits.union (fun i : Slot =>
    let x := records[i.val]?.getD (0,0)
    PartitionBits.union (fun j : Slot =>
      let y := records[j.val]?.getD (0,0)
      if (i.val<j.val ∧ j.val<ws.length ∧ ws.getD i.val 0≠ws.getD j.val 0) ∧
          (x.1 &&& y.1)≠0 ∧ (x.2 &&& y.2)≠0 then
        ~~~(PartitionBits.lane i ^^^ PartitionBits.lane j) else 0) (slots.drop (i.val+1))) active

def rejects (b : Board) (hs : List Nat) :=
  let xs := Separator.marked false b
  let unique := (coverage true xs).2.1
  let records := (xs.map (axes unique)).toArray
  let ps := fun i => PartitionBits.profile b.2.1 (PartitionBits.pos i)
  let ns := fun i => PartitionBits.profile b.2.1 (PartitionBits.neg i)
  decide (b.2.1.length≤12) &&
    (collisions b.2.1 records ||| PartitionBits.union (PartitionBits.cornerMask ps ns) hs)==BitVec.allOnes 4096
end ColorAxes

namespace ColorAxes
open PublicFloor
open PartitionBits (Slot)

theorem shifted {t k jump : Nat} (hit : (collapse t jump).testBit k=true) :
    ∃ a : Slot, t.testBit (k+jump*a.val)=true := by
  simp only [collapse,Nat.testBit_or,Nat.testBit_shiftRight,Bool.or_eq_true_iff] at hit
  rcases hit with (((h|h)|(h|h))|((h|h)|(h|h)))|((h|h)|(h|h))
  · refine ⟨0,?_⟩
    change t.testBit (k+jump*0)=true
    convert h using 1 <;> congr 1 <;> ring
  · refine ⟨1,?_⟩
    change t.testBit (k+jump*1)=true
    convert h using 1 <;> congr 1 <;> ring
  · refine ⟨2,?_⟩
    change t.testBit (k+jump*2)=true
    convert h using 1 <;> congr 1 <;> ring
  · refine ⟨3,?_⟩
    change t.testBit (k+jump*3)=true
    convert h using 1 <;> congr 1 <;> ring
  · refine ⟨4,?_⟩
    change t.testBit (k+jump*4)=true
    convert h using 1 <;> congr 1 <;> ring
  · refine ⟨5,?_⟩
    change t.testBit (k+jump*5)=true
    convert h using 1 <;> congr 1 <;> ring
  · refine ⟨6,?_⟩
    change t.testBit (k+jump*6)=true
    convert h using 1 <;> congr 1 <;> ring
  · refine ⟨7,?_⟩
    change t.testBit (k+jump*7)=true
    convert h using 1 <;> congr 1 <;> ring
  · refine ⟨8,?_⟩
    change t.testBit (k+jump*8)=true
    convert h using 1 <;> congr 1 <;> ring
  · refine ⟨9,?_⟩
    change t.testBit (k+jump*9)=true
    convert h using 1 <;> congr 1 <;> ring
  · refine ⟨10,?_⟩
    change t.testBit (k+jump*10)=true
    convert h using 1 <;> congr 1 <;> ring
  · refine ⟨11,?_⟩
    change t.testBit (k+jump*11)=true
    convert h using 1 <;> congr 1 <;> ring

theorem bit_bound {v k n : Nat} (lim : v<2^n) (yes : v.testBit k=true) : k<n := by
  by_contra! large
  have small : v<2^k := lt_of_lt_of_le lim (Nat.pow_le_pow_right (by decide) large)
  rw [Nat.testBit_lt_two_pow small] at yes
  contradiction

theorem common_bit {a b : Nat} (ne : a &&& b ≠ 0) :
    ∃ k, a.testBit k=true ∧ b.testBit k=true := by
  have seen := Nat.testBit_log2 ne
  exact ⟨_,Bool.and_eq_true_iff.mp (by simpa only [Nat.testBit_and] using seen)⟩

theorem row_index {k : Nat} (seen : rowMarks.testBit k=true) : ∃ i : Slot, k=12*i.val := by
  have small := bit_bound (by decide +kernel : rowMarks<2^144) seen
  have table : ∀ t : Fin 144, rowMarks.testBit t.val=true → t.val=12*(t.val/12) := by decide +kernel
  exact ⟨⟨k/12,by omega⟩,table ⟨k,small⟩ seen⟩

def light (a : Decor) (k : Nat) := (column true a.2).getLsbD k

def lit (u : Bits) (a : Decor) (p q : Slot) :=
  u.getLsbD (12*p.val+q.val)=true ∧ light a (12*p.val+q.val)=true

theorem lit_of_hit {u : Bits} {a : Decor} {p q : Slot}
    (ok : ((u &&& column true a.2).toNat &&& ((1<<<144)-1)).testBit (12*p.val+q.val)=true) : lit u a p q := by
  have yes := (Bool.and_eq_true_iff.mp ((Nat.testBit_and ..) ▸ ok)).1
  change (u &&& column true a.2).getLsbD (12*p.val+q.val)=true at yes
  exact Bool.and_eq_true_iff.mp ((BitVec.getLsbD_and ..) ▸ yes)

theorem row_overlap {u : Bits} {a b : Decor} (hit : (axes u a).1 &&& (axes u b).1 ≠ 0) :
    ∃ p qa qb : Slot, lit u a p qa ∧ lit u b p qb := by
  obtain ⟨k,ha,hb⟩ := common_bit hit
  simp only [axes,Nat.testBit_and,Bool.and_eq_true] at ha hb
  obtain ⟨p,rfl⟩ := row_index ha.2
  obtain ⟨qa,aa⟩ := shifted ha.1
  obtain ⟨qb,bb⟩ := shifted hb.1
  exact ⟨p,qa,qb,lit_of_hit (by simpa only [Nat.one_mul] using aa),
    lit_of_hit (by simpa only [Nat.one_mul] using bb)⟩

theorem col_overlap {u : Bits} {a b : Decor} (hit : (axes u a).2 &&& (axes u b).2 ≠ 0) :
    ∃ q pa pb : Slot, lit u a pa q ∧ lit u b pb q := by
  obtain ⟨k,ha,hb⟩ := common_bit hit
  simp only [axes,Nat.testBit_and,Bool.and_eq_true] at ha hb
  have small := bit_bound (by decide +kernel : 4095<2^12) ha.2
  obtain ⟨pa,aa⟩ := shifted ha.1
  obtain ⟨pb,bb⟩ := shifted hb.1
  exact ⟨⟨k,small⟩,pa,pb,lit_of_hit (by simpa only [Nat.add_comm k] using aa),
    lit_of_hit (by simpa only [Nat.add_comm k] using bb)⟩
end ColorAxes

namespace ColorAxes
open PublicFloor Conflict
open Load (Board)
open PartitionBits (Slot)

def cell (p q : Slot) : Fin 768 := ⟨12*p.val+q.val,by have := p.isLt; have := q.isLt; omega⟩

set_option maxRecDepth 12000 in
theorem chart : ∀ p q : Slot, Separator.positive false (cell p q)=PartitionBits.pos p ∧
    Separator.negative false (cell p q)=PartitionBits.neg q := by decide +kernel

theorem first_lit {a : Decor} {xs : List Decor} {k : Nat} (mem : a∈xs)
    (yes : light a k=true) : (coverage true xs).1.getLsbD k=true := by
  induction xs with
  | nil => simp at mem
  | cons w xs ih =>
    change (column true w.2 ||| (coverage true xs).1).getLsbD k=true
    rw [BitVec.getLsbD_or,Bool.or_eq_true_iff]
    rcases List.mem_cons.mp mem with rfl|mem
    · exact Or.inl yes
    · exact Or.inr (ih mem)

theorem only_lit (xs : List Decor) (k : Fin 768) (one : (coverage true xs).2.1.getLsbD k.val=true) :
    ∀ a∈xs, ∀ b∈xs, light a k.val=true → light b k.val=true → a=b := by
  induction xs with
  | nil => simp
  | cons w xs ih =>
    change ((column true w.2 &&& ~~~(coverage true xs).1) |||
      ((coverage true xs).2.1 &&& ~~~column true w.2)).getLsbD k.val=true at one
    simp only [BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,k.isLt,decide_true,
      Bool.true_and,Bool.or_eq_true_iff,Bool.and_eq_true_iff,Bool.not_eq_true'] at one
    rcases one with ⟨_,none_⟩|⟨once,skip⟩
    · have head (a) (mem : a∈w::xs) (yes : light a k.val=true) : a=w :=
        (List.mem_cons.mp mem).resolve_right (fun rest => by rw [first_lit rest yes] at none_; contradiction)
      exact fun a ha b hb pa pb => (head a ha pa).trans (head b hb pb).symm
    · have tail (a) (mem : a∈w::xs) (yes : light a k.val=true) : a∈xs :=
        (List.mem_cons.mp mem).resolve_left (fun eq => by subst a; exact Bool.noConfusion (yes.symm.trans skip))
      exact fun a ha b hb pa pb => ih once a (tail a ha pa) b (tail b hb pb) pa pb

theorem light_sep {b : Board} {a : Decor} (mem : a∈Separator.marked false b) (p q : Slot) :
    light a (cell p q).val=true ↔ sep (PartitionBits.pos p) (PartitionBits.neg q) a.1 := by
  have good := Separator.marked_ok false b a mem
  change a.2=pairSig _ _ a.1 at good
  simp only [light,good,column,ite_true,pairSig,BitVec.getLsbD_and,BitVec.getLsbD_not,(cell p q).isLt,
    decide_true,Bool.true_and,ofRows_bit,(chart p q).1,(chart p q).2,Bool.and_eq_true_iff,
    Bool.not_eq_true',sep]

theorem forced_at {b : Board} {a : Decor} (mem : a∈Separator.marked false b) {p q : Slot}
    (pass : lit (coverage true (Separator.marked false b)).2.1 a p q) :
    forced graph b.2.1.toFinset (PartitionBits.pos p) (PartitionBits.neg q) a.1 := by
  obtain ⟨unique,yes⟩ := pass
  refine ⟨(PartitionProof.tags p).1,(PartitionProof.tags q).2,(light_sep mem p q).mp yes,?_⟩
  intro w hw separated
  rw [←Separator.words false b] at hw
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hw)
  have eq := only_lit _ (cell p q) unique v hv a mem ((light_sep hv p q).mpr separated) yes
  exact congrArg Prod.fst eq

theorem color_crosses {b : Board} {a c : Decor} (ha : a∈Separator.marked false b)
    (hc : c∈Separator.marked false b)
    (row : (axes (coverage true (Separator.marked false b)).2.1 a).1 &&&
      (axes (coverage true (Separator.marked false b)).2.1 c).1 ≠ 0)
    (col : (axes (coverage true (Separator.marked false b)).2.1 a).2 &&&
      (axes (coverage true (Separator.marked false b)).2.1 c).2 ≠ 0) :
    crosses graph b.2.1.toFinset a.1 c.1 := by
  obtain ⟨p,qa,qb,ar,br⟩ := row_overlap row
  obtain ⟨q,pa,pb,ac,bc⟩ := col_overlap col
  exact ⟨_,_,_,_,_,_,forced_at ha ar,forced_at ha ac,forced_at hc br,forced_at hc bc⟩
end ColorAxes

namespace ColorAxes
open PublicFloor Conflict
open Load (Board)
open PartitionBits (Slot M)

theorem records_at {xs : List Decor} {i : Nat} (hi : i<xs.length) (u : Bits) :
    (xs.map (axes u)).toArray[i]?.getD (0,0)=axes u xs[i] := by
  simp only [List.getElem?_toArray,List.getElem?_map,List.getElem?_eq_getElem hi,Option.map_some,
    Option.getD_some]

theorem signal_at {b : Board} {i : Nat} (hi : i<(Separator.marked false b).length) :
    (Separator.marked false b)[i].1=b.2.1.getD i 0 := by
  rw [←Separator.words false b,List.getD_eq_getElem?_getD,List.getElem?_map,
    List.getElem?_eq_getElem hi,Option.map_some,Option.getD_some]

def records (b : Board) :=
  let xs := Separator.marked false b
  (xs.map (axes (coverage true xs).2.1)).toArray

theorem crossing_at {b : Board} {assignment : M}
    (hit : (collisions b.2.1 (records b)).getLsbD assignment.toNat=true) :
    ∃ i j : Slot, (i.val<j.val ∧ j.val<b.2.1.length ∧ b.2.1.getD i.val 0≠b.2.1.getD j.val 0) ∧
      crosses graph b.2.1.toFinset (b.2.1.getD i.val 0) (b.2.1.getD j.val 0) ∧
      assignment.getLsbD i.val=assignment.getLsbD j.val := by
  obtain ⟨i,_,found⟩ := (PartitionBits.union_ok _ _ _).mp hit
  obtain ⟨j,_,bits⟩ := (PartitionBits.union_ok _ _ _).mp found
  dsimp only at bits
  split at bits
  next ok =>
    obtain ⟨sizes,row,col⟩ := ok
    let xs := Separator.marked false b
    have len : xs.length=b.2.1.length := by simpa only [List.length_map] using congrArg List.length (Separator.words false b)
    have hi : i.val<xs.length := by rw [len]; exact Nat.lt_trans sizes.1 sizes.2.1
    have hj : j.val<xs.length := by rw [len]; exact sizes.2.1
    have ri : (records b)[i.val]?.getD (0,0)=axes (coverage true xs).2.1 xs[i.val] := records_at hi _
    have rj : (records b)[j.val]?.getD (0,0)=axes (coverage true xs).2.1 xs[j.val] := records_at hj _
    rw [ri,rj] at row col
    have cr := color_crosses (b:=b) (List.getElem_mem hi) (List.getElem_mem hj) row col
    have si : xs[i.val].1=b.2.1.getD i.val 0 := signal_at hi
    have sj : xs[j.val].1=b.2.1.getD j.val 0 := signal_at hj
    rw [si,sj] at cr
    refine ⟨i,j,sizes,cr,?_⟩
    rw [PartitionBits.zeroAt,BitVec.getLsbD_xor,PartitionBits.lane_ok_of (PartitionBits.checked_lanes i),
      PartitionBits.lane_ok_of (PartitionBits.checked_lanes j)] at bits
    cases xi : assignment.getLsbD i.val <;> cases xj : assignment.getLsbD j.val <;> simp_all only
      [Bool.xor_self,Bool.false_xor,Bool.true_xor,Bool.not_true,Bool.not_false,Bool.false_eq_true]
  next => simp at bits

theorem cut {b : Board} {k hints} (bound : k≤b.2.1.toFinset.card) (pass : rejects b hints=true) :
    ¬Live false graph k b.2.1.toFinset := by
  intro run
  obtain ⟨part,h⟩ := Reuse.binary run bound
  obtain ⟨width,all_⟩ := Bool.and_eq_true_iff.mp pass
  have len : b.2.1.length≤12 := of_decide_eq_true width
  let ws := b.2.1
  let x := PartitionBits.pack (fun i : Slot => part (ws.getD i.val 0))
  let corners := PartitionBits.union (PartitionBits.cornerMask (fun i => PartitionBits.profile ws (PartitionBits.pos i))
      (fun i => PartitionBits.profile ws (PartitionBits.neg i))) hints
  have bad : (collisions ws (records b) ||| corners).getLsbD x.toNat=true := by
    change collisions ws (records b) ||| corners == BitVec.allOnes 4096 at all_
    rw [beq_iff_eq.mp all_,BitVec.getLsbD_allOnes]
    exact decide_eq_true x.isLt
  rw [BitVec.getLsbD_or,Bool.or_eq_true_iff] at bad
  rcases bad with pair|corner
  · obtain ⟨i,j,⟨ij,jw,ne⟩,cr,cols⟩ := crossing_at pair
    have mem (s : Slot) (small : s.val<ws.length) : ws.getD s.val 0∈ws.toFinset :=
      List.mem_toFinset.mpr (by simpa only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem small,
        Option.getD_some] using List.getElem_mem small)
    exact h.1 _ (mem i (Nat.lt_trans ij jw)) _ (mem j jw) ne cr
      (by simpa only [x,PartitionBits.pack_ok] using cols)
  · obtain ⟨code,_,flag⟩ := (PartitionBits.union_ok _ _ _).mp corner
    obtain ⟨top,side,never⟩ := PartitionBits.corner_at PartitionBits.checked_lanes flag
    obtain ⟨w,hw,yes,sepW⟩ := h.2 _ _ _ _ (PartitionProof.support len _ _ top) (PartitionProof.support len _ _ side)
    obtain ⟨i,eq⟩ := PartitionProof.slot len (List.mem_toFinset.mp hw)
    have no := never i ((PartitionProof.sep_at ..).mpr (eq.symm ▸ sepW))
    simp only [x,PartitionBits.pack_ok,ws,eq,yes,Bool.true_eq_false] at no
end ColorAxes

namespace Digits
open PublicFloor
open PartitionBits (Slot A M)

abbrev Index := Fin 6

def low (t : Index) : Slot := ⟨2*t.val,by have := t.isLt; omega⟩

def high (t : Index) : Slot := ⟨2*t.val+1,by have := t.isLt; omega⟩

def parent (s : Slot) : Index := ⟨s.val/2,by have := s.isLt; omega⟩

def pick (code : Nat) (j : Index) : Slot := Fin.ofNat 12 ((code>>>(4*j.val)) &&& 15)

def pack (c : Index → Fin 4) : M := PartitionBits.pack fun s => (c (parent s)).val.testBit (s.val % 2)

theorem pair_low (t : Index) : parent (low t)=t := by apply Fin.ext; change 2*t.val/2=t.val; omega

theorem pair_high (t : Index) : parent (high t)=t := by apply Fin.ext; change (2*t.val+1)/2=t.val; omega

def digit (t : Index) (v : Fin 4) : A :=
  let a := PartitionBits.lane (low t)
  let b := PartitionBits.lane (high t)
  (if v.val.testBit 0 then a else ~~~a) &&& (if v.val.testBit 1 then b else ~~~b)

theorem digit_ok (c : Index → Fin 4) (t : Index) (v : Fin 4) :
    (digit t v).getLsbD (pack c).toNat=decide (c t=v) := by
  have lo := PartitionBits.lane_ok_of (PartitionBits.checked_lanes (low t)) (pack c)
  have hi := PartitionBits.lane_ok_of (PartitionBits.checked_lanes (high t)) (pack c)
  have lowMod : (low t).val % 2=0 := by change (2*t.val) % 2=0; omega
  have highMod : (high t).val % 2=1 := by change (2*t.val+1) % 2=1; omega
  simp only [pack,PartitionBits.pack_ok,pair_low,pair_high,lowMod,highMod] at lo hi
  unfold digit
  rw [BitVec.getLsbD_and]
  simp only [apply_ite (fun w : A => w.getLsbD (pack c).toNat),PartitionBits.zeroAt]
  change _ = decide (c t=v)
  change (PartitionBits.lane (low t)).getLsbD (pack c).toNat = (c t).val.testBit 0 at lo
  change (PartitionBits.lane (high t)).getLsbD (pack c).toNat = (c t).val.testBit 1 at hi
  rw [lo,hi]
  generalize c t=x
  fin_cases x <;> fin_cases v <;> decide

def above (t : Index) (v : Fin 4) : A := PartitionBits.union
  (fun n : Fin 4 => if v<n then digit t n else 0) (List.finRange 4)

theorem above_ok (c : Index → Fin 4) (t : Index) (v : Fin 4) :
    (above t v).getLsbD (pack c).toNat=true ↔ v<c t := by
  rw [above,PartitionBits.union_ok]
  constructor
  · rintro ⟨n,_,yes⟩
    split at yes
    next lt =>
      rw [digit_ok] at yes
      have eq : c t=n := of_decide_eq_true yes
      exact eq.symm ▸ lt
    next => simp at yes
  · intro lt
    exact ⟨c t,List.mem_finRange _,by simp only [lt,ite_true,digit_ok,decide_true]⟩

def occupied (code : Nat) := PartitionBits.pack fun s => (List.finRange 6).any (fun i => pick code i==s)

def intersection (f : Index → A) : List Index → A
  | [] => BitVec.allOnes 4096
  | j::js => f j &&& intersection f js

theorem all_at {f : Index → A} {js : List Index} {x : M} (hit : (intersection f js).getLsbD x.toNat=true) :
    ∀ t∈js, (f t).getLsbD x.toNat=true := by
  induction js with
  | nil => simp
  | cons a js ih =>
    simp only [intersection,BitVec.getLsbD_and,Bool.and_eq_true] at hit
    intro t mem
    rcases List.mem_cons.mp mem with rfl|tail
    · exact hit.1
    · exact ih hit.2 t tail

def require (code : Nat) (ws : M) (f : Index → A) :=
  if ws &&& ~~~(occupied code)==0 then
    intersection (fun j => if ws.getLsbD (pick code j).val then f j else BitVec.allOnes 4096) (List.finRange 6)
  else 0

theorem required {code ws f} {x : M} (h : (require code ws f).getLsbD x.toNat=true) {s : Slot}
    (need : ws.getLsbD s.val=true) : ∃ t : Index, pick code t=s ∧ (f t).getLsbD x.toNat=true := by
  unfold require at h
  split at h
  next subset =>
    have eq := congrArg (fun v : M => v.getLsbD s.val) (beq_iff_eq.mp subset)
    have no : (0 : M).getLsbD s.val=false := Nat.zero_testBit s.val
    simp only [BitVec.getLsbD_and,BitVec.getLsbD_not,s.isLt,decide_true,Bool.true_and,need,
      no,occupied,PartitionBits.pack_ok,Bool.not_eq_false'] at eq
    obtain ⟨t,mem,yes⟩ := List.any_eq_true.mp eq
    have at_ := all_at h t mem
    have ps := beq_iff_eq.mp yes
    exact ⟨t,ps,by simpa only [ps,need,ite_true] using at_⟩
  next => simp at h
end Digits

namespace Rules
open PublicFloor Reuse Digits
open PartitionBits (M A Slot union union_ok)
open Load (Board)

def edge (b : Board) (i j : Slot) :=
  let xs := ColorAxes.records b
  let x := xs[i.val]?.getD (0,0)
  let y := xs[j.val]?.getD (0,0)
  decide ((i.val<b.2.1.length ∧ j.val<b.2.1.length ∧ b.2.1.getD i.val 0≠b.2.1.getD j.val 0) ∧
    (x.1 &&& y.1)≠0 ∧ (x.2 &&& y.2)≠0)

theorem edge_ok {b i j} (hit : edge b i j=true) :
    b.2.1.getD i.val 0 ≠ b.2.1.getD j.val 0 ∧
      Conflict.crosses graph b.2.1.toFinset (b.2.1.getD i.val 0) (b.2.1.getD j.val 0) := by
  obtain ⟨⟨hi,hj,ne⟩,r,c⟩ := of_decide_eq_true hit
  let xs := Separator.marked false b
  have len : xs.length=b.2.1.length := by simpa only [List.length_map] using congrArg List.length (Separator.words false b)
  have hx : i.val<xs.length := len.symm ▸ hi
  have hy : j.val<xs.length := len.symm ▸ hj
  have ri : (ColorAxes.records b)[i.val]?.getD (0,0)=ColorAxes.axes (coverage true xs).2.1 xs[i.val] := ColorAxes.records_at hx _
  have rj : (ColorAxes.records b)[j.val]?.getD (0,0)=ColorAxes.axes (coverage true xs).2.1 xs[j.val] := ColorAxes.records_at hy _
  rw [ri,rj] at r c
  have proof := ColorAxes.color_crosses (b:=b) (List.getElem_mem hx) (List.getElem_mem hy) r c
  have si : xs[i.val].1=b.2.1.getD i.val 0 := ColorAxes.signal_at hx
  have sj : xs[j.val].1=b.2.1.getD j.val 0 := ColorAxes.signal_at hy
  rw [si,sj] at proof
  exact ⟨ne,proof⟩

def same (i j : Index) := union (fun v : Fin 4 => digit i v &&& digit j v) (List.finRange 4)

theorem same_ok {c : Index → Fin 4} {i j} (hit : (same i j).getLsbD (pack c).toNat=true) : c i=c j := by
  obtain ⟨v,_,yes⟩ := (union_ok _ _ _).mp hit
  simp only [BitVec.getLsbD_and,digit_ok,Bool.and_eq_true,decide_eq_true_eq] at yes
  exact yes.1.trans yes.2.symm

def marks (ws : List Sig) (p q : Slot) :=
  PartitionBits.sep (PartitionBits.profile ws (PartitionProof.pos p)) (PartitionBits.profile ws (PartitionProof.negRow q))

def blocked (ws : List Sig) (code : Nat) (p q pa qa : Slot) :=
  let sides := marks ws p qa ||| marks ws pa q
  let center := marks ws p q
  union (fun v : Fin 4 => require code sides (fun t => digit t v) &&& require code center (fun t => above t v)) (List.finRange 4)

def ties (ws : List Sig) (code : Nat) (c : Sig → Nat) (v : Index → Fin 4) :=
  ∀ t, (v t).val=c (ws.getD (pick code t).val 0)

theorem forced_group {ws : List Sig} {code c labels group p q} {needed : M} (len : ws.length≤12) (assigned : ties ws code c labels)
    (contains : ∀ s : Slot, (marks ws p q).getLsbD s.val=true → needed.getLsbD s.val=true)
    (seen : (require code needed (fun t => digit t group)).getLsbD (pack labels).toNat=true) :
    support graph ws.toFinset c group.val (PartitionProof.pos p) (PartitionProof.negRow q) := by
  refine ⟨(PartitionProof.tags p).1,(PartitionProof.tags q).2,?_⟩
  intro w mem diff
  obtain ⟨s,signal⟩ := PartitionProof.slot len (List.mem_toFinset.mp mem)
  have hit := contains s ((PartitionProof.sep_at ..).mpr (signal.symm ▸ diff))
  obtain ⟨t,index,yes⟩ := required seen hit
  have val : labels t=group := of_decide_eq_true ((digit_ok _ _ _).symm.trans yes)
  have eq := assigned t
  rw [index,signal,val] at eq
  exact eq.symm

theorem no_corner {ws code c labels n p q pa qa} (len : ws.length≤12) (assigned : ties ws code c labels)
    (fit : coloring graph ws.toFinset n c)
    (bad : (blocked ws code p q pa qa).getLsbD (pack labels).toNat=true) : False := by
  obtain ⟨v,_,both⟩ := (union_ok _ _ _).mp bad
  rw [BitVec.getLsbD_and,Bool.and_eq_true] at both
  have row := forced_group len assigned (p:=p) (q:=qa) (fun s h => by rw [BitVec.getLsbD_or,h,Bool.true_or]) both.1
  have col := forced_group len assigned (p:=pa) (q:=q) (fun s h => by rw [BitVec.getLsbD_or,h,Bool.or_true]) both.1
  obtain ⟨w,mem,le,diff⟩ := fit.2.2 _ _ _ _ _ row col
  obtain ⟨s,signal⟩ := PartitionProof.slot len (List.mem_toFinset.mp mem)
  have hit : (marks ws p q).getLsbD s.val=true := (PartitionProof.sep_at ..).mpr (signal.symm ▸ diff)
  obtain ⟨t,index,yes⟩ := required both.2 hit
  have lt : v.val<(labels t).val := (above_ok ..).mp yes
  rw [assigned t,index,signal] at lt
  exact Nat.lt_irrefl _ (lt_of_le_of_lt le lt)
end Rules

namespace Rules
open PublicFloor Reuse Digits Verification
open PartitionBits (M A Slot union union_ok nibble)
open Load (Board)

def word (b : Board) (code w : Nat) : A :=
  if w<64 then
    let i := Fin.ofNat 6 (w &&& 7)
    let j := Fin.ofNat 6 ((w>>>3) &&& 7)
    if edge b (pick code i) (pick code j) then same i j else 0
  else
    let x := w-64
    blocked b.2.1 code (nibble x 0) (nibble x 1) (nibble x 2) (nibble x 3)

def accepts (b : Board) (cap code : Nat) (limit : Fin 4) (hints : List Nat) :=
  let ws := b.2.1
  let bounds := ((decide ws.Nodup && decide (ws.length≤12)) && decide (cap+1≤ws.length+limit.val)) &&
    (List.finRange 6).all (fun t => decide ((pick code t).val<ws.length))
  let overflow := union (fun t => above t limit) (List.finRange 6)
  bounds && (overflow ||| union (word b code) hints)==BitVec.allOnes 4096

theorem cut {m b cap code limit hs} (ok : accepts b cap code limit hs=true) : closed false m cap b := by
  obtain ⟨bounds,pass⟩ := Bool.and_eq_true_iff.mp ok
  obtain ⟨counts,selected⟩ := Bool.and_eq_true_iff.mp bounds
  obtain ⟨lengths,tight⟩ := Bool.and_eq_true_iff.mp counts
  obtain ⟨nd,slim⟩ := Bool.and_eq_true_iff.mp lengths
  let ws := b.2.1
  have len : ws.length≤12 := of_decide_eq_true slim
  have count : cap+1≤ws.length+limit.val := of_decide_eq_true tight
  have wmem (t : Index) : ws.getD (pick code t).val 0∈ws.toFinset := by
    have hi : (pick code t).val<ws.length := of_decide_eq_true (List.all_eq_true.mp selected t (List.mem_finRange _))
    exact List.mem_toFinset.mpr (by simpa only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi,
      Option.getD_some] using List.getElem_mem hi)
  intro k le _ run
  obtain ⟨n,c,fit,size⟩ := palette (Trace.forget run)
  change ws.toFinset.card+n≤k+2 at size
  rw [List.toFinset_card_of_nodup (of_decide_eq_true nd)] at size
  change ws.length+n≤k+2 at size
  have colors : n≤limit.val+1 := by omega
  have lim := limit.isLt
  have max_ (t : Index) : c (ws.getD (pick code t).val 0)≤limit.val := by
    have bound := fit.1 _ (wmem t)
    omega
  let vals : Index → Fin 4 := fun t => ⟨_,lt_of_le_of_lt (max_ t) lim⟩
  have assigned : ties ws code c vals := fun _ => rfl
  let x := pack vals
  have seen := congrArg (fun a : A => a.getLsbD x.toNat) (beq_iff_eq.mp pass)
  rw [BitVec.getLsbD_or,BitVec.getLsbD_allOnes,decide_eq_true x.isLt,Bool.or_eq_true] at seen
  rcases seen with invalid|clue
  · obtain ⟨t,_,bad⟩ := (union_ok _ _ _).mp invalid
    have gt : limit.val<(vals t).val := (above_ok ..).mp bad
    exact (Nat.not_lt_of_ge (max_ t)) gt
  · obtain ⟨w,_,bad⟩ := (union_ok _ _ _).mp clue
    unfold word at bad
    split at bad
    next small_ =>
      dsimp only at bad
      split at bad
      next edge_ =>
        obtain ⟨ne,cross⟩ := edge_ok edge_
        have colors := congrArg Fin.val (same_ok bad)
        exact fit.2.1 _ (wmem _) _ (wmem _) ne cross colors
      next => simp at bad
    next large_ => exact no_corner len assigned fit bad
end Rules

namespace Sensitive
open PublicFloor
open Conflict (clean image image_mem)

def isolated (y : Sig) (S : Finset Sig) (p q : Row) (w : Sig) :=
  bit p y≠bit q y ∧ bit p w≠bit q w ∧ ∀ t∈S, bit p t≠bit q t → t=w

theorem reverse {y S p q w} (h : isolated y S p q w) : isolated y S q p w :=
  ⟨h.1.symm,h.2.1.symm,fun t ht diff => h.2.2 t ht diff.symm⟩

def action (d : Nat) (a b : Bool) :=
  if d=0 then a && b else if d=1 then a || b else if d=2 then a && !b else !a && b

theorem value (p : Row) (d : Nat) (a b : Sig) : bit p (bin d a b)=action d (bit p a) (bit p b) := bit_bin ..

theorem needs {a b d p q} (change_ : bit p (bin d a b)≠bit q (bin d a b)) :
    bit p a≠bit q a ∨ bit p b≠bit q b := by
  by_contra! h
  exact change_ (by rw [value,value,h.1,h.2])

theorem mapped {u y U a b d k p q w} (run : Live u y k (insert (bin d a b) U)) (free : clean a b U w)
    (h : isolated y (insert a (insert b U)) p q w) : isolated y (insert (bin d a b) U) p q (image a b (bin d a b) w) := by
  let z := bin d a b
  have seen : ∀ t∈insert z U, bit p t≠bit q t → t=image a b z w := by
    intro t mem diff
    rcases Finset.mem_insert.mp mem with rfl|old
    · rcases needs diff with sa|sb
      · exact (if_pos (Or.inl (h.2.2 a (by simp) sa).symm)).symm
      · exact (if_pos (Or.inr (h.2.2 b (by simp) sb).symm)).symm
    · have eq := h.2.2 t (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem old)) diff
      subst t
      exact (if_neg (fun op => free op old)).symm
  obtain ⟨t,mem,diff⟩ := live_row_difference run h.1
  exact ⟨h.1,seen t mem diff ▸ diff,seen⟩

theorem left_phase {u d x x' v} (op : allowed u d) (change_ : action d x v≠action d x' v) :
    action d x v=(x ^^ (d==3)) := by
  rcases allowed_four op with rfl|rfl|⟨_,rfl⟩|⟨_,rfl⟩ <;>
    cases x <;> cases x' <;> cases v <;> first | rfl | exact False.elim (change_ rfl)

theorem right_phase {u d v x x'} (op : allowed u d) (change_ : action d v x≠action d v x') :
    action d v x=(x ^^ (d==2)) := by
  rcases allowed_four op with rfl|rfl|⟨_,rfl⟩|⟨_,rfl⟩ <;>
    cases x <;> cases x' <;> cases v <;> first | rfl | exact False.elim (change_ rfl)

def orientation (a b : Sig) (d : Nat) (w : Sig) :=
  if w=a then d==3 else if w=b then d==2 else false

theorem phase {u y U a b d k p q w} (op : allowed u d) (ab : a≠b) (tail : Live u y k (insert (bin d a b) U))
    (free : clean a b U w) (h : isolated y (insert a (insert b U)) p q w) :
    bit p (image a b (bin d a b) w)=(bit p w ^^ orientation a b d w) := by
  have diff := (mapped tail free h).2.1
  by_cases wa : w=a
  · subst w
    have fixed_ : bit p b=bit q b := by by_contra no; exact ab (h.2.2 b (by simp) no).symm
    simp only [image,eq_self,true_or,ite_true,value,orientation] at diff ⊢
    rw [←fixed_] at diff
    exact left_phase op diff
  · by_cases wb : w=b
    · subst w
      have fixed_ : bit p a=bit q a := by by_contra no; exact ab (h.2.2 a (by simp) no)
      simp only [image,eq_self,or_true,ite_true,value,orientation,wa,ite_false] at diff ⊢
      rw [←fixed_] at diff
      exact right_phase op diff
    · simp only [image,wa,wb,or_self,ite_false,orientation,Bool.xor_false]

def critical (d : Nat) (a b : Bool) := action d a b≠action d (!a) b ∧ action d a b≠action d a (!b)

theorem local_crit {u y U a b d k r p q} (ab : a≠b) (tail : Live u y k (insert (bin d a b) U))
    (ca : clean a b U a) (cb : clean a b U b) (left : isolated y (insert a (insert b U)) r p a)
    (right : isolated y (insert a (insert b U)) r q b) : critical d (bit r a) (bit r b) := by
  have ba : bit r b=bit p b := by by_contra no; exact ab (left.2.2 b (by simp) no).symm
  have aa : bit r a=bit q a := by by_contra no; exact ab (right.2.2 a (by simp) no)
  have da := (mapped tail ca left).2.1
  have db := (mapped tail cb right).2.1
  simp only [image,eq_self,true_or,or_true,ite_true,value] at da db
  have fa : bit p a= !(bit r a) := by cases x : bit r a <;> cases z : bit p a <;> simp_all [isolated]
  have fb : bit q b= !(bit r b) := by cases x : bit r b <;> cases z : bit q b <;> simp_all [isolated]
  exact ⟨by simpa only [←ba,fa] using da,by simpa only [←aa,fb] using db⟩

theorem critical_eq {u d a b c f} (op : allowed u d) (h1 : critical d a b) (h2 : critical d c f) : a=c ∧ b=f := by
  rcases allowed_four op with rfl|rfl|⟨_,rfl⟩|⟨_,rfl⟩ <;> cases a <;> cases b <;> cases c <;> cases f <;>
    first | exact ⟨rfl,rfl⟩ | exact False.elim (h1.1 rfl) | exact False.elim (h1.2 rfl) |
      exact False.elim (h2.1 rfl) | exact False.elim (h2.2 rfl)
end Sensitive

namespace Sensitive
open PublicFloor Conflict Reuse

def clash (y : Sig) (S : Finset Sig) (w v : Sig) :=
  ∃ p q pa qa pb qb : Row, isolated y S p qa w ∧ isolated y S q pa w ∧
    isolated y S p qb v ∧ isolated y S q pb v ∧ (bit p w≠bit q w ∨ bit p v≠bit q v)

theorem swap {y S w v} (h : clash y S w v) : clash y S v w := by
  obtain ⟨p,q,pa,qa,pb,qb,w1,w2,v1,v2,e⟩ := h
  exact ⟨p,q,pb,qb,pa,qa,v1,v2,w1,w2,e.elim Or.inr Or.inl⟩

theorem xor_ne {x z : Bool} (s : Bool) (bad : x≠z) : (x ^^ s) ≠ (z ^^ s) := by
  cases x <;> cases z <;> cases s <;> simp_all

theorem next_clash {u y U a b d k w v} (op : allowed u d) (ab : a≠b)
    (tail : Live u y k (insert (bin d a b) U)) (cw : clean a b U w) (cv : clean a b U v)
    (both : clash y (insert a (insert b U)) w v) :
    clash y (insert (bin d a b) U) (image a b (bin d a b) w) (image a b (bin d a b) v) := by
  obtain ⟨p,q,pa,qa,pb,qb,w1,w2,v1,v2,e⟩ := both
  refine ⟨p,q,pa,qa,pb,qb,mapped tail cw w1,mapped tail cw w2,mapped tail cv v1,mapped tail cv v2,?_⟩
  rcases e with e|e
  · exact Or.inl (by rw [phase op ab tail cw w1,phase op ab tail cw w2]; exact xor_ne _ e)
  · exact Or.inr (by rw [phase op ab tail cv v1,phase op ab tail cv v2]; exact xor_ne _ e)

theorem no_pair {u y U a b d k} (op : allowed u d) (ab : a≠b)
    (tail : Live u y k (insert (bin d a b) U)) (ca : clean a b U a) (cb : clean a b U b) :
    ¬clash y (insert a (insert b U)) a b := by
  rintro ⟨p,q,pa,qa,pb,qb,w1,w2,v1,v2,e⟩
  have same := critical_eq op (local_crit ab tail ca cb w1 v1) (local_crit ab tail ca cb w2 v2)
  exact e.elim (fun h => h same.1) (fun h => h same.2)

theorem apart {u y U a b d k w v} (op : allowed u d) (ab : a≠b)
    (fresh : bin d a b∉insert a (insert b U)) (run : Live u y k (insert (bin d a b) U))
    (mw : w∈insert a (insert b U)) (mv : v∈insert a (insert b U)) (ne : w≠v)
    (cw : clean a b U w) (cv : clean a b U v) (e : clash y (insert a (insert b U)) w v) :
    image a b (bin d a b) w ≠ image a b (bin d a b) v := by
  intro eq
  by_cases x : w=a ∨ w=b <;> by_cases t : v=a ∨ v=b
  · rcases x with rfl|rfl <;> rcases t with rfl|rfl
    · exact ne rfl
    · exact no_pair op ab run cw cv e
    · exact no_pair op ab run cv cw (swap e)
    · exact ne rfl
  · simp only [image,if_pos x,if_neg t] at eq
    exact fresh (eq ▸ mv)
  · simp only [image,if_neg x,if_pos t] at eq
    exact fresh (eq ▸ mw)
  · simp only [image,if_neg x,if_neg t] at eq
    exact ne eq

theorem paint_clash {u y U a b d k c} (op : allowed u d) (ab : a≠b)
    (fresh : bin d a b∉insert a (insert b U)) (tail : Live u y k (insert (bin d a b) U))
    (child : ∀ w∈insert (bin d a b) U, ∀ v∈insert (bin d a b) U, w≠v →
      clash y (insert (bin d a b) U) w v → c w≠c v)
    {w v} (mw : w∈insert a (insert b U)) (mv : v∈insert a (insert b U)) (ne : w≠v)
    (conflict : clash y (insert a (insert b U)) w v) :
    paint a b (bin d a b) U c w≠paint a b (bin d a b) U c v := by
  intro eq
  let color := paint a b (bin d a b) U c
  by_cases low : color w<weight a b U
  · exact ne (same_small ab low rfl eq.symm)
  · have hi : weight a b U ≤ color w := Nat.le_of_not_gt low
    obtain ⟨cw,pw⟩ := unshift hi (rfl : color w=color w)
    obtain ⟨cv,pv⟩ := unshift hi eq.symm
    exact child _ (image_mem mw) _ (image_mem mv) (apart op ab fresh tail mw mv ne (clear cw) (clear cv) conflict)
      (next_clash op ab tail (clear cw) (clear cv) conflict) (pw.trans pv.symm)
end Sensitive

namespace Sensitive
open PublicFloor Conflict Reuse

def pickEarly (a b : Sig) (U : Finset Sig) (i : Nat) := if a∈U ∧ i=0 then a else b

theorem pick_slot {a b U w} (ab : a≠b) (keep : carried a b U w) : pickEarly a b U (slot a U w)=w := by
  obtain ⟨mem,eq|eq⟩ := keep <;> subst w
  · simp [pickEarly,slot,mem]
  · by_cases yes : a∈U <;> simp [pickEarly,slot,ab.symm,yes]

theorem has_slot {a b U i} (ab : a≠b) (below : i<weight a b U) : ∃ w, carried a b U w ∧ slot a U w=i := by
  by_cases ca : a∈U <;> by_cases cb : b∈U
  · have hi : i<2 := by simpa [weight,ca,cb] using below
    by_cases zero : i=0
    · exact ⟨a,⟨ca,Or.inl rfl⟩,by simp [slot,zero]⟩
    · exact ⟨b,⟨cb,Or.inr rfl⟩,by simp only [slot,ab.symm,ite_false,ca,decide_true,Bool.toNat_true]; omega⟩
  · have hi : i=0 := by simpa [weight,ca,cb] using below
    exact ⟨a,⟨ca,Or.inl rfl⟩,by simp [slot,hi]⟩
  · have hi : i=0 := by simpa [weight,ca,cb] using below
    exact ⟨b,⟨cb,Or.inr rfl⟩,by simp [slot,ab.symm,ca,hi]⟩
  · simp [weight,ca,cb] at below

def agree (S : Finset Sig) (c : Sig → Nat) (i : Nat) (p q : Row) :=
  ∀ w∈S, c w ≤ i → bit p w=bit q w

def features (a b : Sig) (U : Finset Sig) (F : Nat → Row → Bool) (i : Nat) (p : Row) :=
  if i<weight a b U then bit p (pickEarly a b U i) else F (i-weight a b U) p

def signs (a b : Sig) (d : Nat) (U : Finset Sig) (s : Sig → Bool) (w : Sig) :=
  if carried a b U w then false else orientation a b d w ^^ s (image a b (bin d a b) w)

theorem feature_depends {a b U d c F i p q} (ab : a≠b)
    (depends : ∀ i p q, agree (insert (bin d a b) U) c i p q → F i p=F i q)
    (same : agree (insert a (insert b U)) (paint a b (bin d a b) U c) i p q) :
    features a b U F i p=features a b U F i q := by
  let z := bin d a b
  let amt := weight a b U
  by_cases below : i<weight a b U
  · obtain ⟨w,keep,s⟩ := has_slot ab below
    have eq : pickEarly a b U i=w := s ▸ pick_slot ab keep
    simp only [features,below,ite_true,eq]
    exact same _ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem keep.1)) (by rw [paint,if_pos keep,s])
  · simp only [features,below,ite_false]
    apply depends
    intro w mw bound
    rcases Finset.mem_insert.mp mw with rfl|old
    · have ea : paint a b z U c a≤amt+c z := by simpa [image] using (paint_le (a:=a) (b:=b) (z:=z) (U:=U) (c:=c) (w:=a))
      have eb : paint a b z U c b≤amt+c z := by simpa [image] using (paint_le (a:=a) (b:=b) (z:=z) (U:=U) (c:=c) (w:=b))
      change c z ≤ i-amt at bound
      change ¬i<amt at below
      have one := same a (by simp) (by change paint a b z U c a ≤ i; omega)
      have two := same b (by simp) (by change paint a b z U c b ≤ i; omega)
      rw [value,value,one,two]
    · apply same w (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem old))
      by_cases keep : carried a b U w
      · exact (Nat.le_of_lt (small keep)).trans (Nat.le_of_not_gt below)
      · rw [paint,if_neg keep,original old keep]
        omega

def Model (y : Sig) (S : Finset Sig) (n : Nat) (c : Sig → Nat) (s : Sig → Bool) (F : Nat → Row → Bool) :=
  0<n ∧ (∀ w∈S, c w<n) ∧ (∀ w∈S, ∀ v∈S, w≠v → clash y S w v → c w≠c v) ∧
  (∀ i p q, agree S c i p q → F i p=F i q) ∧
  (∀ w∈S, ∀ p q, isolated y S p q w → F (c w) p=(bit p w ^^ s w)) ∧ (∀ p, F (n-1) p=bit p y)

theorem lift_model {u y U a b d k n c s F} (op : allowed u d) (ab : a≠b)
    (fresh : bin d a b∉insert a (insert b U)) (tail : Live u y k (insert (bin d a b) U))
    (child : Model y (insert (bin d a b) U) n c s F) :
    Model y (insert a (insert b U)) (weight a b U+n) (paint a b (bin d a b) U c)
      (signs a b d U s) (features a b U F) := by
  let z := bin d a b
  let amt := weight a b U
  obtain ⟨top,bounded,separates,depends,sensitive,last⟩ := child
  refine ⟨by omega,?_,fun _ mw _ mv ne h => paint_clash op ab fresh tail separates mw mv ne h,
    fun _ _ _ entry => feature_depends ab depends entry,?_,?_⟩
  · intro w mem
    exact lt_of_le_of_lt paint_le (Nat.add_lt_add_left (bounded _ (image_mem mem)) _)
  · intro w mem p q witness
    by_cases keep : carried a b U w
    · simp only [signs,if_pos keep,features,paint,if_pos keep,pick_slot ab keep,Bool.xor_false,if_pos (slot_lt keep)]
    · have high := big (z:=z) (c:=c) keep
      have eq := sensitive _ (image_mem mem) p q (mapped tail (clear keep) witness)
      rw [features,if_neg (Nat.not_lt.mpr high),paint,if_neg keep,Nat.add_sub_cancel_left]
      rw [eq,phase op ab tail (clear keep) witness,signs,if_neg keep,Bool.xor_assoc]
  · intro p
    have hi : ¬amt+n-1<amt := by omega
    have index : amt+n-1-amt=n-1 := by omega
    exact (show features a b U F (amt+n-1) p=F (n-1) p by rw [features,if_neg hi,index]).trans (last p)

theorem model_of_live {u y S k} (run : Live u y k S) : ∃ n c s F, Model y S n c s F ∧ S.card+n≤k+2 := by
  induction run using Live.ind with
  | stop hp =>
    refine ⟨1,fun _ => 0,fun _ => false,fun _ p => bit p y,⟨by decide,by simp,by simp,?_,?_,by simp⟩,by simp⟩
    · intro i p q same
      exact same y (by simp) (Nat.zero_le _)
    · intro w mem p q _
      simpa using congrArg (bit p) (Finset.mem_singleton.mp mem).symm
  | @binary k U a b d op aa bb ab fresh tail ih =>
    obtain ⟨n,c,s,F,child,bound⟩ := ih
    refine ⟨_,_,_,_,lift_model op ab fresh tail child,?_⟩
    have nz : bin d a b∉U := fun h => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
    rw [Finset.card_insert_of_notMem nz] at bound
    have size := parent_size ab U
    unfold weight
    omega
end Sensitive

namespace Sensitive
open PublicFloor

def Two (y : Sig) (S : Finset Sig) (early sign : Sig → Bool) (head : Row → Bool) :=
  (∀ w∈S, ∀ v∈S, w≠v → clash y S w v → early w≠early v) ∧
  (∀ p q, (∀ w∈S, early w=true → bit p w=bit q w) → head p=head q) ∧
  (∀ w∈S, ∀ p q, isolated y S p q w → (if early w then head p else bit p y)=(bit p w ^^ sign w))

theorem two {u y S k} (run : Live u y k S) (limit : k≤S.card) :
    ∃ early sign head, Two y S early sign head := by
  obtain ⟨n,c,s,F,model,bound⟩ := model_of_live run
  obtain ⟨positive,compact,separates,depends,sensitive,last⟩ := model
  have nn : n=1 ∨ n=2 := by omega
  rcases nn with rfl|rfl
  · refine ⟨fun _ => false,s,fun _ => false,?_,?_,?_⟩
    · intro w hw v hv ne cl _
      have aw := compact w hw
      have av := compact v hv
      exact separates w hw v hv ne cl (by omega)
    · intros; rfl
    · intro w hw p q obs
      have aw := compact w hw
      have no : c w=0 := by omega
      have hit := sensitive w hw p q obs
      rw [no] at hit
      exact (last p).symm.trans hit
  · refine ⟨fun w => c w==0,s,F 0,?_,?_,?_⟩
    · intro w hw v hv ne cl eq
      have aw := compact w hw
      have av := compact v hv
      apply separates w hw v hv ne cl
      by_cases zero : c w=0
      · have other : c v=0 := beq_iff_eq.mp (eq.symm.trans (beq_iff_eq.mpr zero))
        omega
      · have other : c v≠0 := fun h => zero (beq_iff_eq.mp (eq.trans (beq_iff_eq.mpr h)))
        omega
    · intro p q same
      exact depends 0 p q (fun w hw h => same w hw (beq_iff_eq.mpr (by omega)))
    · intro w hw p q obs
      have hit := sensitive w hw p q obs
      by_cases zero : c w=0
      · simpa only [zero,beq_self_eq_true,ite_true] using hit
      · have hw' := compact w hw
        have eq : c w=1 := by omega
        rw [eq] at hit
        simpa only [eq,show (1==0 : Bool)=false by decide, Bool.false_eq_true,ite_false] using
          (last p).symm.trans hit
end Sensitive

namespace PhaseCheck
open PublicFloor Sensitive
open PartitionBits (Slot M A profile pack pack_ok lane allOn allOn_ok zeroAt)

abbrev wire (ws : List Sig) (i : Slot) := ws.getD i.val 0

def row (w k : Nat) : Row := Fin.ofNat 512 ((w>>>k) &&& 511)

def index (w k : Nat) : Slot := Fin.ofNat 12 ((w>>>k) &&& 15)

def mask (ws : List Sig) (p q : Row) := profile ws p ^^^ profile ws q

def choice (ws : List Sig) (early : Sig → Bool) := pack fun i => early (wire ws i)

theorem mask_bit (ws : List Sig) (p q : Row) (i : Slot) :
    (mask ws p q).getLsbD i.val = (bit p (wire ws i) ^^ bit q (wire ws i)) := by
  simp only [mask,BitVec.getLsbD_xor,PartitionBits.profile_at,bit]

theorem lane_bit (ws : List Sig) (early : Sig → Bool) (i : Slot) :
    (lane i).getLsbD (choice ws early).toNat=early (wire ws i) :=
  (PartitionBits.lane_ok_of (PartitionBits.checked_lanes i) _).trans (pack_ok _ i)

theorem xor_true {x y : Bool} : (x ^^ y)=true ↔ x≠y := by cases x <;> cases y <;> decide

def isolates (ws : List Sig) (i : Slot) (p q : Row) :=
  (decide (i.val<ws.length) && (bit p graph != bit q graph)) && (mask ws p q == pack fun j => j==i)

theorem isolated_ok {ws i p q} (len : ws.length≤12) (yes : isolates ws i p q=true) :
    wire ws i∈ws.toFinset ∧ isolated graph ws.toFinset p q (wire ws i) := by
  obtain ⟨both,hit⟩ := Bool.and_eq_true_iff.mp yes
  obtain ⟨idx,out⟩ := Bool.and_eq_true_iff.mp both
  have hi := of_decide_eq_true idx
  have diff (j : Slot) : (bit p (wire ws j) ^^ bit q (wire ws j))=(j==i) := by
    rw [←mask_bit,beq_iff_eq.mp hit,pack_ok]
  refine ⟨List.mem_toFinset.mpr (by simpa only [wire,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi,Option.getD_some] using List.getElem_mem hi),
    bne_iff_ne.mp out,xor_true.mp ((diff i).trans (beq_iff_eq.mpr rfl)),?_⟩
  intro w hw change_
  obtain ⟨j,e⟩ := PartitionProof.slot len (List.mem_toFinset.mp hw)
  have yes_ := xor_true.mpr (e.symm ▸ change_)
  have eq : j=i := beq_iff_eq.mp ((diff j).symm.trans yes_)
  exact e.symm.trans (congrArg (wire ws) eq)

theorem agree_rows {ws early s head p q} (len : ws.length≤12) (h : Two graph ws.toFinset early s head)
    (hit : (allOn (mask ws p q) true).getLsbD (choice ws early).toNat=true) : head p=head q := by
  have late := (allOn_ok _ _ _ PartitionBits.checked_lanes).mp hit
  apply h.2.1
  intro w hw outside
  obtain ⟨i,eq⟩ := PartitionProof.slot len (List.mem_toFinset.mp hw)
  by_contra bad
  have changed : (mask ws p q).getLsbD i.val=true := by
    rw [mask_bit]
    exact xor_true.mpr (by simpa only [wire,eq] using bad)
  have clash_ := late i changed
  simp only [choice,pack_ok,wire,eq,outside,Bool.not_true,Bool.true_eq_false] at clash_

def lastMask (ws : List Sig) (i : Slot) (p pp q qq : Row) : A :=
  if isolates ws i p pp && isolates ws i q qq &&
    ((bit p graph ^^ bit p (wire ws i)) != (bit q graph ^^ bit q (wire ws i))) then ~~~lane i else 0

theorem same_phase {a b c d s : Bool} (h : a=(b ^^ s)) (k : c=(d ^^ s)) : (a ^^ b)=(c ^^ d) := by
  cases b <;> cases d <;> cases s <;> simp_all

theorem last_no {ws i p pp q qq early s head} (len : ws.length≤12) (fit : Two graph ws.toFinset early s head)
    (hit : (lastMask ws i p pp q qq).getLsbD (choice ws early).toNat=true) : False := by
  unfold lastMask at hit
  split at hit
  next allowed_ =>
    obtain ⟨both,apart⟩ := Bool.and_eq_true_iff.mp allowed_
    obtain ⟨one,two⟩ := Bool.and_eq_true_iff.mp both
    obtain ⟨mem,hp⟩ := isolated_ok len one
    obtain ⟨_,hq⟩ := isolated_ok len two
    have no : early (wire ws i)=false := by simpa only [zeroAt,lane_bit,Bool.not_eq_true'] using hit
    have phaseP := fit.2.2 _ mem p pp hp
    have phaseQ := fit.2.2 _ mem q qq hq
    simp only [no,Bool.false_eq_true,ite_false] at phaseP phaseQ
    exact bne_iff_ne.mp apart (same_phase phaseP phaseQ)
  next => simp at hit

def crossMask (ws : List Sig) (i j : Slot) (p pi pj q qi qj : Row) : A :=
  if ((isolates ws i p pi && isolates ws i q qi) && (isolates ws j p pj && isolates ws j q qj)) &&
    ((wire ws i != wire ws j) && (bit p (wire ws i) != bit q (wire ws i) || bit p (wire ws j) != bit q (wire ws j)))
  then ~~~(lane i ^^^ lane j) else 0

theorem cross_no {ws i j p pi pj q qi qj early s head} (len : ws.length≤12) (fit : Two graph ws.toFinset early s head)
    (hit : (crossMask ws i j p pi pj q qi qj).getLsbD (choice ws early).toNat=true) : False := by
  unfold crossMask at hit
  split at hit
  next good =>
    obtain ⟨four,other⟩ := Bool.and_eq_true_iff.mp good
    obtain ⟨top,bot⟩ := Bool.and_eq_true_iff.mp four
    obtain ⟨one,two⟩ := Bool.and_eq_true_iff.mp top
    obtain ⟨three,four⟩ := Bool.and_eq_true_iff.mp bot
    obtain ⟨wi,h1⟩ := isolated_ok len one
    obtain ⟨_,h2⟩ := isolated_ok len two
    obtain ⟨wj,h3⟩ := isolated_ok len three
    obtain ⟨_,h4⟩ := isolated_ok len four
    obtain ⟨ne,diff⟩ := Bool.and_eq_true_iff.mp other
    have cp : clash graph ws.toFinset (wire ws i) (wire ws j) :=
      ⟨p,q,qi,pi,qj,pj,h1,h2,h3,h4,(Bool.or_eq_true_iff.mp diff).imp bne_iff_ne.mp bne_iff_ne.mp⟩
    have diff_ := xor_true.mpr (fit.1 _ wi _ wj (bne_iff_ne.mp ne) cp)
    rw [zeroAt,BitVec.getLsbD_xor,lane_bit,lane_bit,diff_] at hit
    contradiction
  next => simp at hit
end PhaseCheck

namespace PhaseCheck
open PublicFloor Sensitive
open PartitionBits (Slot M A lane allOn)

def guard (ws : List Sig) (i j : Slot) (p pp q qq : Row) : A :=
  if isolates ws i p pp && isolates ws j q qq then (lane i &&& lane j) &&& allOn (mask ws p q) true else 0

theorem xor_link {x y sx sy a b : Bool} (same : a=b) (one : a=(x ^^ sx)) (two : b=(y ^^ sy)) :
    (sx ^^ sy) = (x ^^ y) := by
  cases x <;> cases y <;> cases sx <;> cases sy <;> simp_all

theorem related {ws i j p pp q qq early s head} (len : ws.length≤12) (fit : Two graph ws.toFinset early s head)
    (hit : (guard ws i j p pp q qq).getLsbD (choice ws early).toNat=true) :
    (s (wire ws i) ^^ s (wire ws j)) = (bit p (wire ws i) ^^ bit q (wire ws j)) := by
  unfold guard at hit
  split at hit
  next live_ =>
    obtain ⟨one,two⟩ := Bool.and_eq_true_iff.mp live_
    obtain ⟨im,obsP⟩ := isolated_ok len one
    obtain ⟨jm,obsQ⟩ := isolated_ok len two
    simp only [BitVec.getLsbD_and,Bool.and_eq_true,lane_bit] at hit
    have phaseP := fit.2.2 _ im p pp obsP
    have phaseQ := fit.2.2 _ jm q qq obsQ
    simp only [hit.1.1,hit.1.2,ite_true] at phaseP phaseQ
    exact xor_link (agree_rows len fit hit.2) phaseP phaseQ
  next => simp at hit

def flip (ws : List Sig) (i : Slot) (w : Nat) := bit (row w 4) (wire ws i) ^^ bit (row w 22) (wire ws (index w 0))

def walk (ws : List Sig) (stop : Slot) : Slot → Bool → List Nat → A
  | i,v,[] => if i==stop && v then BitVec.allOnes 4096 else 0
  | i,v,w::es =>
    guard ws i (index w 0) (row w 4) (row w 13) (row w 22) (row w 31) &&&
      walk ws stop (index w 0) (v ^^ flip ws i w) es

theorem next_sign {a x y v diff : Bool} (from_ : a=(x ^^ v)) (edge : (x ^^ y)=diff) : a=(y ^^ (v ^^ diff)) := by
  cases x <;> cases y <;> cases v <;> simp_all

theorem walk_no {ws early s head} (len : ws.length≤12) (fit : Two graph ws.toFinset early s head) (stop : Slot)
    (es : List Nat) (i : Slot) (v : Bool) (sign : s (wire ws stop)=(s (wire ws i) ^^ v))
    (hit : (walk ws stop i v es).getLsbD (choice ws early).toNat=true) : False := by
  induction es generalizing i v with
  | nil =>
    simp only [walk] at hit
    split at hit
    next good =>
      obtain ⟨eq,on⟩ := Bool.and_eq_true_iff.mp good
      obtain rfl := beq_iff_eq.mp eq
      subst v
      cases h : s (wire ws i) <;> simp [h] at sign
    next => simp at hit
  | cons w es ih =>
    simp only [walk,BitVec.getLsbD_and,Bool.and_eq_true] at hit
    have edge := related len fit hit.1
    exact ih _ _ (next_sign sign edge) hit.2

def disconnected (ws : List Sig) (p q : Row) : A :=
  if bit p graph != bit q graph && mask ws p q==0 then BitVec.allOnes 4096 else 0

theorem disconnected_no {ws p q u k x} (len : ws.length≤12) (run : Live u graph k ws.toFinset)
    (hit : (disconnected ws p q).getLsbD x=true) : False := by
  unfold disconnected at hit
  split at hit
  next good =>
    obtain ⟨out,zero_⟩ := Bool.and_eq_true_iff.mp good
    obtain ⟨w,mem,diff⟩ := live_row_difference run (bne_iff_ne.mp out)
    obtain ⟨i,eq⟩ := PartitionProof.slot len (List.mem_toFinset.mp mem)
    have mask_ := (mask_bit ws p q i).trans (xor_true.mpr (by simpa only [wire,eq] using diff))
    rw [beq_iff_eq.mp zero_] at mask_
    simp at mask_
  next => simp at hit
end PhaseCheck

namespace PhaseCheck
open PublicFloor Sensitive Verification
open PartitionBits (Slot M A union union_ok)
open Load (Board)

def rule (ws : List Sig) (w : Nat) (path : List Nat) : A :=
  let kind := w &&& 3
  let i := index w 2
  if kind=0 then disconnected ws (row w 2) (row w 11)
  else if kind=1 then crossMask ws i (index w 6) (row w 10) (row w 19) (row w 28) (row w 37) (row w 46) (row w 55)
  else if kind=2 then lastMask ws i (row w 6) (row w 15) (row w 24) (row w 33)
  else walk ws i i false path

def accepts (b : Board) (cap : Nat) (rules : List (Nat × List Nat)) :=
  ((decide b.2.1.Nodup && decide (b.2.1.length≤12)) && decide (cap≤b.2.1.length)) &&
    (union (fun rec_ : Nat × List Nat => rule b.2.1 rec_.1 rec_.2) rules == BitVec.allOnes 4096)

theorem cut {u m b cap hints} (pass : accepts b cap hints=true) : closed u m cap b := by
  obtain ⟨base,full⟩ := Bool.and_eq_true_iff.mp pass
  obtain ⟨lim,cost⟩ := Bool.and_eq_true_iff.mp base
  obtain ⟨nd,sz⟩ := Bool.and_eq_true_iff.mp lim
  let ws := b.2.1
  have len : ws.length≤12 := of_decide_eq_true sz
  intro k le _ run
  have live_ := Trace.forget run
  have bound : k≤ws.toFinset.card := by
    rw [List.toFinset_card_of_nodup (of_decide_eq_true nd)]
    exact le.trans (of_decide_eq_true cost)
  obtain ⟨early,s,head,fit⟩ := two live_ bound
  let x := choice ws early
  have bad : (union (fun rec_ : Nat × List Nat => rule ws rec_.1 rec_.2) hints).getLsbD x.toNat=true := by
    rw [beq_iff_eq.mp full,BitVec.getLsbD_allOnes]
    exact decide_eq_true x.isLt
  obtain ⟨⟨w,path⟩,_,h⟩ := (union_ok _ _ _).mp bad
  unfold rule at h
  dsimp only at h
  split at h
  · exact disconnected_no len live_ h
  · split at h
    · exact cross_no len fit h
    · split at h
      · exact last_no len fit h
      · exact walk_no len fit _ path _ false (by simp) h
end PhaseCheck

namespace ReducedData

def page0 : Array Nat := #[0x5c7dc15e78e5ce30e14c14eedddcccbbaa9998775102ceb0a7aa2be88b79327ca896a424a3c84a422254808fea3a7e839fe4b89ca309a7286a0c9c2288620f00,0x29027025523d21920de9ce60a90a0c21d21929123d20ded0cd0a60a5427c26021421020c27025423ee7d67d679ea0e80e4ce20e9fe4be27e62e5ee7ce60e34e1,0xd8ab4a3ca182b427125523d22921920de64c64a544aca90a18a0c46425429022921920d0aded0ec4ec0e64e60e68cc8ac0a28a68ab4a90a54a18a0c8c82282b4,0x8a0c4cc4c42b429027025423d22921920deccec4ec0ed8ea8e4ce48e24cd8ad4a90a4cad867c624ab4a3ca18a0c8d82b527125523d22921920deccec4e4ca48a,0x85203a6674bd50456a0266c4183a9c0a53e12692067448b4ed4e9ce48cc0ab469ca70a18a0c4c02b527122921920ded4ecce4ce48ccccc4ab4a48a90a70a3ca1,0x452c3f580c41568c30580c32538c2e490c3a568c3c520c36452c3843242dd6042b560428d0e50749c419d18417cd1ddb551110eec685c4b6f6d5ae36a854a422,0x755a04995684974784951a048c56848e4e448a47c457d58e53540e514c9450c484514a8e4a541448500e464c8e4849944644844e44144e5684484e04464a8e4e,0xaf8dacac2a6948e8a78645a4e46363218120c080400485d50541c9853d99853949853552053347853099852852252a4aa52647a474d984b8d544a3da04a19a04,0x561d49718594964e4d59518494924e5460f541c906541890244115022401117263d30f223940d263530c503530522053013c04b8122046010412d2923110902f,0xf581d0871a1c286580d09d1a6c29c587d117225c29654588945448897263940c5034f85240c2913e44c1124446910a44211065530d22253093c24b89222460f,0x49091a3530522053013c048811804101021d56655948e54d853611984161057964c592cc96581560342155832e1161f563cc0f1a3c28e523930b563468a52293,0x4840a1406441f3c54f911a24f89242428f3c1c8830a04f8124056a90ca41a904852191e6419f54595151e4521114441951e05201380479114443110254909302,0x65015304501d627449cfa53e9d517445c997245c8965454997263940d263140f4e1cfb724dc2b74cbc8af0aa53910a441915024c8912243890c24e012a047a11,0x90b242c68a243550f4c1c6070a1554915043410705b915a452110c441915a25209382430906256810c052113844a910c44197263940c503d607541d3874c1950,0xe47b906e4ab106c45210c841a14c64c1132449915a052192a6419f245891244489104454f0b243d5072419506241550454089174e3cf8f243c68f0a3950e4e38,0x420d0a7527d09f1a7c61d1a7d097423d38f1a3c28f421d307181c2832e0c2f11f452492b247c940dd4af4eb93af525c695185d3871a19383301564d5905bb95a]
def page1 : Array Nat := #[0x7181c28652094824e04ad91f645590d641d96f44e312ac47b114c433106c47990644e09480434168e4e192a647991464319067d617525d3974c596155651617,0x9397463d08f3e3cf0f561d187341cc03461d59f565d497425cd171a5c6165254612525d58e522948a4e3d5873e1cc0f1a3c28e523938b3e3428a4e2948f561cf,0xac523138c56a948a4e292aa47a906ad0896825a89583590522119236a8d92566955226085921228192524456894824e095a052013804a9f565d4965259392524,0xa4c3d587301cb964c49316523930b562948a4c3cf87301c6870a194864c0d5851a0949a4c7cf172e5c6170a593133c4931148252013804a8114043010605bc15,0x3b5a9338f69f39b481283785202685206eac187ba6103385102992106aa6105e9e11b081041403e31a498960e0400115643590764ac15ac5a296aa4a97563930,0x9501648f01608aa00081a1809599a89789a49181e89781bc8186daac6941981937a70922ac0933a7010b9f00fea2035991011ea700fa9f412fa739079f38e792,0xf280bce930cc29f0af2280b1f93030b280306a602ee28825e9c5a4a8158a0835a66a052518852208e52309f4a44834a2c853a348339a48f098c9509f28f0184,0xb33822b3d922ab3422abeb92a3e312a3d522a3d29ea3b512a33022a3ca93132f930b2b93031b282b9a932afe282b279323172822fa282313281af6281b23930b,0xac04aa2c04f3acccd72cce86acccce8dccbd85cca62cccefacc4d32cc4caacc4a22cc612ac7429987432ac6c2eac643a8c4bc99203f392bbbd12bbdd22b28992,0x4da90e43a9061b2703f9ab033da905e28c03028504eba124e72c1edeac1cbaab1cc5971cb62c1cffac14e32c14b22c14fbac0cdf2c0cae2c0cf7ac04db2c06aa,0x15d52915c9271653a90e37290e2b270dd1290dc5270e4fa90633290627270431ab05cd2905c1272623271c2dab1dbd271e4ba9161f271385a91647a90bfdab0b,0x5a911296aa04bc43f31242293128e8d016d9aba94daba6f3ab9eefab96ebab8cc9ab8e16a235d991360dab0e5bab0657a9063b29062f271435ab1609a316e19f,0x2149833a188d3123c84331fea4031ec9c1b1c4861b1f6a4131cca4131e49c131b086131faa40b1aea7031a4a7c31a89fc31949eb160da19914aac4b1b0821929,0xf934e936138693515e6933124e8f0b8a4a4092529301220990ba2c930922ba203a5a9205259850521c9803a049203a1c8d05204854124484452629f33a569235,0xa10142da1c90feac8147eac613b3aa093af2a093caaa093a62a093f3aa0139ea11939aaa193be2a193f7aa093c22a093efaa013e72a015e592013c6a6f93ba2a,0xd52959155b30163d92013c8b3513c9a9293cda921149ab19399a919289a911029a90947dab01122ac293fda129611a1216aaac1906da1114caac11431a109435]
def page2 : Array Nat := #[0xd0e390e3cd09cb89cd05c605cc01c681d0c790c7d0c190c1d0879087d081908084401d4bc2a0116cf29016c929016c3a3716bf9a716bb29716b529716e729596,0x432100b3cd1bcb1bcb91cc0fc68e49004208418842064187cd03cb83c603c6004a86430641864e0443044185d0819081d0a390a3d09790964f02410253004101,0x939ee738ce2b83e0780a8d976558fe4ca7e6bca5e2fcabe6b1e8e6819ee8719bc87193e84191c84100659b96d24e2f4a3979dde85a6b2169fe84a7321292e840,0xa0066866065864861cbbaa99987775542000a9eb29fa974e9e97a626e94aba179e7ca79d75e34978b77e14af8427e0a82a8a1aac899a716608596706488187e,0xe44e40ec0e9ce48e24a44a1867cad5689681679675ec4ec0e48e9ae22a0e68267ea8c668658656aadeb0ea4e9ce98e84e7ce78e74e34e30e2ce14e10e08aa0a9,0x74ad066866065d659e3ce0c6884a8ab067867163d0a9ec8ec0ebceb8ecce48e44e34e30e2ce14e10e08ab4688ad4ab068467c67867464a62eeb9aa1ebceb8e4c,0x8ad0a0c6d46c86bc6b8a8d66965d6594c9eb4e2ce28e10e0ce00a30690668658654ec8ec0ebceb8ed8e9ce98e94e34e30e2ce14e10e08aaca28a0469468467c6,0x44331162d21a2ad83ad83469e7369a1928982acc4e64554e4437a4c0126481ac073a9c4ea481727c80abf5ea9b1a67a1765c97651ed4ec8ebceb8e30e2ce10cc,0x4470e17fab2e6f44e92fb3110f2674be2443dd788769010e56a13cab2436d14a028888d55821a684634cfa0699d20d338a17aaf430cc506aa310c334baa98875,0x54e75b29c2b4538b30a15ac4e20c908398720d156254eb94abd99d579212af20a4fad44a0d09d3d9f127b3aa4eacee9cc949399090c144a80ac6e6ec44a01879,0xfc4072703f561ba80dd306e9437101b870d9406e342f18179d0bc205a282f3c038c0040008300a8aec1511c6aa01b054234aa7c6634f1d929d7b053b75ca79e3,0xd3f30cc3f38d4abbad2abae4c1627c2800290612b40119006b8032e00b4001900303d5838ca8c6d3dda2ae50372b6b35b58266a122c486625ca2a0057321f970,0x328c93208d71e1eff361cc072c1c206300793d5443d4c5743d46d841d30cb4194658b1bb546ae3bb5aae3b8cf2e3b6c2ae105d080003ce041285dc13ed7bf32c,0x282079c6141861036af5911f1dd4f51d3f4dd2f49d0f3fcf73bce757d1f35ccf31cbf2dc6f19c5f15c4f11c3f0bc2707c1703c06355250155d46cd332cc32ecb,0x1638a1c40e0c7043811c00c5c5482800c99ea474e3a61d20e3471838a1c48e147063811528a9033219116595554cf3cd2cb2471c4e34cb2c30bacaaa9a69a492,0x1a6094f68333f99dccbdc5dc32d1760cbc6142c91840b2e9073c39d1ce0e287103871c28e107063821c08e005482800cc865832211b00d9e9073c39d1ce0e307]
def page3 : Array Nat := #[0x31c90e2455a2901430a0c56a1a00cf9678f563a81d38e9874a3a41c40e1c70c32818986903381931d39e98f1a78c3c29e94f3a78b3c21a28e521ab0d486a034e,0xd80e4871a3891c08ab450e2b50d1068433c28d0c0848841209e1d70ed47583a21d00e787263911d80e9c7243891848a4450c2b50d11680b3c59d3049ec476039,0xa4c51c1880c3060c24410804f9264f5c3b51d60e8873e39e1c88ec47503931c40e1c56a2ac0d1167cb3c59d3541a4cb105083d88ebc75a3931c88e3c7103861,0x46442af156868056a2ac0d1068433a2a01498a383081221d78eb47243911d88ea072638e1c40e187063811840ab855a1a00cc8ad45581a20d0867c33c2b1154,0x55a285140068832c2a10c4aec0f5e7a73d31e44f0a6ad2401084f603af1d70eb476a3ac1d10e8473e39e1ce8e487223901d88ea07403931c70e1c70c3841c18e,0x6b53561684b3e59e2ce9644b167b31d78eb876a3ac1d11e78f227903c11ab4d006b53561ed87663b01d78eb87543b51d60e8873e39e1c90e447203851c20e08,0xb31d50e4c7243911c78e347183831c08ab834419b0910ad45581a00c8863c3180221d80ebc75c3b51d60e8473e39e1d98e487223901c68e307163851c21ab4d0,0x2911ad4b4059e2ce9a88b1858331114448447b51d60e8474039f1cf0e747663a21c98e4872038f1910c4834412a0911ad4d585a02cf9674d4462228910a88447,0x28e6072e38b1c2ee13705a83d40ea0334b990c99546aa4251e210148423e01d1d70ed47583a11d00e7c73c39d1d50e887263911c80e3c7183831911c44b4459b,0xad8b565a82d39690d6859a2cc9640f643b01d78eb476c3a91d40e9c74838d1c60e287123881c28e0c7022ad1559a2cd046b62d41678d685982cb9ebc75c3a61d,0xf643ae1d68eac7523a51d20e687323961c58e287063821c08e0055a2800d59664b207b21d80eb875a3b41cd0e6473038d1c58e287123841c19e00d5a68c3401,0x6a1b00d786b834a2a30cd065c32c1321d80ebc75c3ad1da0e647303971cb0e2470a3841c18e087023801569a00b565a82d39694b486b42cc9660b2e5962c8163,0x11a1da8ec87623b01d70eb471a38c1c58e0c70233018d0ad05181b00d726955469994cc265926091a5c614689567b51d90ec075e3ae1c68e307163321418a043,0xa0cc866032e1960c684d01480341d09e78f3a78c3c59e10f046802d71a8cb2e5902c39290f6a3af1d70eb471a38c1c58e1070638118d0ad051a1a60cc865825e,0x3da8d440aad03b6690ae6585f3e841c2e780226680ae6602a897401ec475e3ae1d68e3471838b1c50e147083831c10e047002b414006c435e1ae0d6869054619,0x38c4e1fa1aab7a17ac39c6a9f926a4b899a27a71ecf52da3f616abf599a9b542a474b3a23596ad70c1e06e6fea6852a96844ab2043aadc42aad83ea8d841aad4]
def page4 : Array Nat := #[0xac91abaa50b5635084631001269276eccd30e3cc91e08c66e00c4ba00e30ac4dc7aa0cb461cc99618e18ac44b361c673ecc22fac0143a480b4a27e35ebf94be4,0x6cacc5faaa84b664842226c677ec8092e0826bacc1f9aa809a649d42641e06ea99d1e998076599b4e9542d66d4176615c8aa54d263548462d653ac502c66d257,0x985e469639ebce1feb4d4ee2cccde10c79e04c57ab4dfbaa8cd3644cb6640c9a63ce27eb88a7e0ca6dacc8d364894364092663c83b288a37ebc61deb4455ab46,0xe1166b6c94fce1cdfb6a4dc7698cb7694c9b690c3d2ace5dec45fa6a44b769c59969043065041c64843c2ac619ad81f96a409b69c1c669802f652c1b64ac5f46,0xf5e14097e0806ae0004fa002306bc0b86b82186b40412d00cfe11dca6d5e6d6c9e176b5c402d1cade0d9ac6d5a6c6c9a576c58b86c1a2f6bda166b58522b58ce,0xc1c17e381c14e340a53e1c1c18e141c1ee101c12c501c10a9c24216681c0f6641caeaa810216441c116102b9658e26154c80c208432d0a6e6c84422d053fe280,0xe7c642fe386427e346429e306432e2c6431e246424aa4642086c64216606422aa86423a88642562c5c1ceb01c15ea42a53ea01c13e9c1c19e981c1de841c1be7,0x43658203c669144465d1c3ac68e43b668d03b65cdc41658dc38468d036c688444a8c9444664903b6609034468a42ceb02426ea42430ea02428e9c242ae98642d,0x48012805d2967c1128678103b282dc412828669ab21e666820614ab1c52bab1a668689908567d9caf645108065cc43c6844444678443ca8c203c664243b66024,0x7c16196782a55ac821a8a50082c61c144428408fced848f9ecc48fbea848fde4848f8a1048b5ad449abab048846884a5767c51a76784a5366061a7a50482c620,0x964ca43b288a42126ca49f684509d67861a864c66136841e2b67c10b9678e1a764ce450284e443288e5c468851f567858fce9c201ca4c15caad40656ab015ac6,0x5a2e9c05a4ed005a3e68059ee3405a5e30059bab4059aa280598684041b67c042f67405c6ad2859966a849b662861965e85f965a84bdab0a46f6849c6e67ca1a,0xa502668989b66098b765c99c7658a42d6509c1b64899e06149df666044442ac61b4e382c17ad4042f6700e6e6684dfc6644c2328c459dec8059fec005a1ed80,0xea019e8e9819eded019ebe6019ece5c225de3819efe3419f0e3018fce2019e2e1419e3e102c2dad419dfaac19e1a342d02ad819de6a099dd678841b67099fbad,0x576602430651aa53649aa54625ad026d544d8a8d64876695c60661526565d6a556c524bc669121265d1cba660843c2ac6a5dec419e6ec019e7ebc19eaed819e9,0x1380261986539161f859e1671805e1743d8a11c46216857140460c02a094170501000aa5de7c2a5be342a59e142030a382a566d42a556bc2a5869c2a6e6682a]
def page5 : Array Nat := #[0x9d581ea00f4e07a603d281e200f0e072803c680e30070a039d01c580e100514028c14980a294535e25a2115707acc3d5c0fab01d380e98074a038801c380ca0,0x46f1637841b450d2286836281014d20669c233a119a08cb04ac0055a028006c203674132e098804c382e4c055a029101430087c0344019d015a0065c05600292,0xb5b0569c2b4c15a50ace856582d6615910ac585a000d26029308c404e4c15220a8604ce82aac14120bab01d400e9c074c03a501c400e1c0454038d1bc60de7,0x78174a03a901d080e340718038b01c400e1c0748039c2dc316e04b32859872c4d0f46058462c16160e86a04150401a800d380678011602b20b5685a0c2d02168,0x8b00c50061c0464021a008580268012800ad0acb842a027560ba6059402e8c0f3e079e03ce81e1c0e4005a703d400e9c074a019b0ec8076303a221c9b0f49856,0xad40558019e015800a48051202a511438882444620db006d7836b81b5a0da606d2836901b260d910618836b403260191075780668032801a400cc8065c031a01,0xe9325c48e264336a019f585323298e93a628d29c40f68c450c21a610488821840302290015a80674033801081e040f28c312a18860d4e83a101f260291014780,0x674032000a2b05f9d278e94274a32a501120041761c210fd281e2c0f04079c03c081a84031a018caa54bf701695cb4835a53a829d376a8289408220291036a5,0xa30e51866782a6a122308d00448c206a102308cd826bc1336021d0091006800326019008c7848882144109b080e84088233c058302d10066c056a02ac00d08,0xc56462948f4ad655b26ad0a33e52ad255a112588d6c39a7185b8920c134a01a438cb1c610e306738d37459babcd96e3c9b0e510528821440ca20454812a8094e,0x611ad08d204a8c2334119808ca84a30250a12050919030c81b6a01b06adab16c98b60c5af628c310598b6ac0b144ce1e69ce98038a41c56822bc0b40019c8ac9,0x38dc80693e20b7075a006680328011a015180664033001964cc426251351a94bd305718230c04460b72ed8906c4733c28ba004d8023c0106003d135185e34251,0x38038801c380e18070201a700d20064c032201881c5f890a8497a20ad104988088415a1e8a0ada856bc2b4e141604d781290010000191dd18de806f3a379c1bc,0x71115d12232a6d42412d904dc9b1090635a120ae1c0011c0804b8df2f8608c4178065099288c36239b118d88465c174e03a501d200e8c0740039f01cf00e7407,0xc4272a287a6b550f1e9911e8c55c3c6ee285d1f520b99918062bb4802566700466cc00196ad24123404858a9c909d4492147852175b4428ea674506b54098daa,0x535b3c2a6b378c1ea6d6e2e2428c5da24c0bd9eb10f995501eae6183eaf5787c82a60f5c5060cd325c1a57538052eae338c35a5130a84a304d411293ab215074]
def page6 : Array Nat := #[0x45993bb8ab237714642ee26c7ddc3e1bbb87223770d68ade0b5adbc45a1b77bb196753ac2ceac5e1e3a7a6369f9761ab9218354358004be9f5f4b51abedae3,0x5b9f32eb7386596e8060002e8a44293d0c68a8ad4d26cd01a4bd9e346ed8245312c488644c9147086229934e3eaf6907e3b428f82d9d0083568010465c022f55,0x15d2604e1961c01be3dc14c67580a8d4b017265e80651b29ac93652f7be1a52f1c0ca60da89441b4929536b61eb8d343d368161b3b60b92ca797268d82dd01ae,0xe39893326728cc658ca24ac69921991a2111a33e372efad04d042cb89c90990139285602724fa484e4d40d872c92b403429b2e06e2c68809c5b5a0138aab1027,0x38ba400492b2c01125a38009c154f1137e94e2751f3f36e9fe0e6dd1d82cda1e7856c988956ca34eab176624d12ebc419f5d9ca956a939668939ed0d02723399,0xc520c8a8ca476795712e2c28e252035640a4459f81480555028fe646051f0cf3eb4b6a77d56eb4c28ad42ac5123c5309acd0ab13568152264e4ea4009cdc6001,0xd96cd2dbc8d985b4aa264a82532fc006375bd3bcb49fa71199514e3372829c63d5b528c82b4a518fb354a31dac29463946d2dbb6b6a4196569482ba66a90666c,0xb9c0c5f8317c0c5e88b2d040a88600840a6b26514f5555b59749f35f2f56be7a52af7c44a560d9394a41b2328d2e6d61d322cbc3bb78a261b76b6ab96ee6bd6e,0x183538e0329f2cb28a5698011a400364402888d6fa399c16360c4859700aa801930064401900063c021b004477c35cc2c6f88cbeaa6d83db40f2bc40a066e708,0x74ee6143a86324acd552a2d37646c8492f30e11c1aeeaa661dd95510c67ab14ea85ba718e8857921ae4446a912a844294e9ba5e7b96e4385e1382a0e9a6318be,0x61cbb8462eab94ca83546660cbaa131862c8b899f68ebdd739772ce81ccb82d5fa834cd84a0feb9cbbb1750e81ccb0855caa084083f68ebdd739972ee59c3bb0,0x1a5534630c592e965ed5d9bb075ee4599b2f564a0d1a1b5552a854d294b1962e99d2f9650d3da3b075ce49c228353462c54bb075ee99c8b8550667d54bae746e,0x2249a9c1bbc80207a704173e080e48bbb998877743d8d7f17969b344f2ebce3d7cef96a0d4135a664fc43b2b05a530dde9073ed1d73a5720e11972b25066d0d7,0xd2abb6b24a1f66145ea828dc9050aae0a0558141ac826cc622f3b405f7560bbe4817fc882eb3405a5680b6aac172c882cab2059d520b1a501611a6292b145776,0x42ea42eaf038b2183d7b507a7660f1e481e7c883c333075d220ed6d41d8d983a6a90755420e8a501ce99c2d1b3452360a4fecc499c8092e91076d6c24a6ac492,0xe04ae00b10083fc3bfda4f12df0bebdb3adaeaeb665a242ad16991697151614991497149903118c8357902fa72f9f2f982f922fa62f9e2f972f912f822f812f0]
def page7 : Array Nat := #[0x596cff17133fc57aac8169962056640814e34204fca80142a80372f6cbeb601716986d6bb2d6d76ab440bd46810620c1dd2004692005e8304bc04ae0499043,0x79325f2050e1c9dc2123a624f2e47e448d88916902154c43a5c834890211ea3a7e9392e3f89e1b83e7b8ce2385c1683a7a8ca22858178019091105da400161b4,0x24612608621d23d1fc09d31d3bd0fa09809f4173f73d34133f33d75074073272671065062661021c55053252631045042621001c46307356b41444dea899d294,0x471a75e72e70a66463461a22856454253431a55e52fd0bc65c35a1bc2fc0b829f2f52f74c74872672271e70c74e73e73072471a71270674a73a72c72071670e6,0x71c70e75e74c72e71861c55a53051441056255054053251c30e55e54c53c52e51850a41c111811f5375174f71170b35335134f51951150b55ed10f6475274273,0x3c52e52221942f01975cf30f64f52f42f34f1af16f5ef4cf2ef0ad64d52d42d34b16d5ed4cd3cd2ed10d0ac64a1ac0a918f6075c73473072c716762750740732,0xcd18d10a32a2e85682ef6075c74673072c72071270ef08f10f0ad06d46b20d3cc0a920f6875c75a72c74273471871671470c70673c72e72261862e52c5065425,0x76075c74e74a72672470e73c72271070a66666250c36a36836634a54c53c52e51050a26626340b734f32f2ef2af4cf18f10f0ae32e2ed2ea56c2eb34b32b2ed4,0x6676476275e75c75a74a72672470c74c73c72e72271871070a66666265e62255e52445e36a36836434a54c53c52e522518510266262a5ec2285ef6a768766762,0x956a625ae9815ea9054a9814691059e9a9278ca53a9a8fa8ca39a360a784629e0984aa0117b568175ef5af48f24f0cf06f3cf18f0ae0ad06d3cd18c0af6a7687,0x32906c49b1b029be181a5950c2e5cb0b912e7ad0a3599269660b03950cfa681058c0686290108c495e30a5788287a309a18d28c6309db88076e1598688667621,0xabf21d5611057ac082dd10414e84209558104da20822d09294a528c1ef739ad6b5472111af2906b481caf2f5e9020783035a0c1b1ad0f6ebcbdba62e5abc9c28,0xca461c667d5e328ea618d1440ae7a1764f46590c69648b9db045deac22df54116baf08b3c88457adb22c3579159aac8a957e455a5f229d23914a9e4895d7843f,0xd88cb2ec0659f3232d3981953d90caaea465472832af87117dc20cb0ebc658f4c32b788195dc28ca6cc8652d6031068c193f060ca1ac865155232829409cec58,0x581d882bced015ef320aff93058bc902c3ebc16274c0aeead20cf4b82b9a4015c556119d9708cecb0269abd15d54cc19e91451b4422e7a1515bc68917c975981,0xae04c74884822bd24df5c1373b409bbd184dae5826bf5e13639e09adc884d5cd0267d681342a308d2cb04cbabc26653c421a91110d4284ca8d180212e8afbb30]
def page8 : Array Nat := #[0x242a60a4d4b82a1a447485101a86851e4a9995254c1292c2291ff9009e7c38433a40267b663285b10884d7848d6b9470d0a9014af48f9c80430a4024635e1231,0x1e3303890a61c386c0e10a98f4c14af970a55c88f31e20794e6654a7300a53888e44abc79452614a2901e4eda95266d0b50b663c99b21942d804906b8a9434e5,0xfd586c98345019260c14066080102018c7f198b44a1e0f074321200bcb3b52a57da0f2aecc795f6454abb00a63d716c0ea8a96f4e14bba51e5bc9852de401607,0x174c078803c08167c0f5003a00fcc87e4c3f0e1fa60fcf07ca03e261f080e87078203a101f2c0110008780344022c2210110788f521fa10f8607aa43d421d0c0,0x18280c080244020202c981a740d08051103c980e480722039001c580e780710038501ce00e1807060311098284c042520119308c584a702202108b098d02c60,0x153e029a0b4f85a082d1612a007d200ea80736039301c900e40071e03a601cf00e5c0718038801c280e04074a039d01cb00e2c070e0384019500c4806220310,0x60c8206244300819990b4184664212e12b5015600688034202b0015380a48051a02a511438848842402212115287a1c3d0e1aa10b4d05a7c2d4a16870b4c03a6,0x49bf22df9a6fc637e2dbf08df826f88b7a69b940009e004e002600114008898104c022651e0b9f014880810055602a300cd00644053e02a50143808d00230011,0x8893772f269e464d1c6498f8592ef0325cc4644350480008954d58ba96ac0b60d81cb9d6d9e22d7095f0886561e2be200d3c068c034401a140920008f79cdb7e,0xfa041555a619998c3db2f85f65b0f2cae19da0932d1325b8264a1c88d37821bc31e38ce944f5c089eb8013174a061e740c1c5d17b84a37f2336ae326c9c2cc73,0x3ae5c588df8c16230e90588c7951627ae28588bb2a1622dc3c588aa8b1622c630588ae971622843c5a2a1a10b205ca4028122a002034a4008082a0003d074c09,0x67ba2af197ea6bc6638daf19ae96bc66f9daf196caabc67ea4af278632be1e2a5af195a76bca328f2c233ea8588d7a216234e6c589eb8f1628ce34588e7a6162,0xd248184ba5e9393e1f86e9f98e3789e1309c1286a9e98a368961209413812a72bba9eacbcea2a5e9b00a8aa6c02a3a5f00a8691c040160b0200581c019ceaabc,0xcdcc58c50b4ccccc48c40b585b50b4a2c5a85bd41d01cc9c99c3994189983887114109883807138c1ee5a0c34974c8fe4521c82339f45f2489c490f48a129f41,0x8c005704e848045c405d23c83d43d03ccbc9bc3bc33d33cf3cbbc8bc63c0b94389b84383388b80b482873043502c33533462842043d41d2f92ed46d2e92fd5dc,0xd3bc23883823552c8353ac22882823d91d49d09cd1c59d3fcc7c97c279978d785f8c78268a754f4d6c5f53f4c7496c271970d685f0c68260a70ca83b57148145]
def page9 : Array Nat := #[0x6a82246a06bda1d91d89d71cc1c69c49c21989971849820da0d90d88d714c1469448c2098897104e827dadd0dd05c6dc4d90584d0ecd0cd0546d44c90504c0ed,0x18698c157145150b4d2c334fb492c2286b0c246a43206bd71cb9d91d49d09cd1c61c59d81d39cf9cc1c218215915495094d0c60c5958153b4fb4c344ac231928,0xcc3c4bc2384b823432da2d7ad2b4c2c2304a822583d71cc3cb3cabc33cfbc6bc238c3822c334fb46ac228c28224c24320c3d71d09cd1c69c51c31cf9cc1c91c2,0xd0a4c2dd87106247d91d89d81d69d39cc1c69c49c21989981849580d391a1181020d90d88d694c546d44cc2498c98504c1a4184025da3d7bd73d33d2bc83c3b,0xc11ca9f48eec09b79225ce34a0ab0267a4893e8d28bec41dfa007fac71c2a0c8aec69af93a57e3a9fab1a65a4e92a8ea4783a8df88837e16076a9215a6885299,0x6b20536362858a82522a2bb8d6aee25a728d6a2635a47b0289ad4a16b0290ec01eb9f05de24222b3075a88212b0073a7d9428968fec11e79f487ac91d2a1483a,0x2b51c81466a409a355072a8101f50139ca518c630841ce6b1283146b4e198f6866866c1870b06f4ec13d3a74a66c539db05006b9151982be658a8d952efeb440,0x4108f0c884029641f92d20f8849041d59620ea810ff52507fa7043d94941ec9d40eb56d875aa4438d4b41c69d10da52d06d275033d18818e6a40be355876ab90,0xd1a250e753a872a49438a44a1c21250bfcc0855a6f429531a1b7a750b9cc2867a9d427d30a1639910974c886bea042bf322196a810954c8845a9442252c210e8,0x320f2975129da8893ecc44873e223f92111b99888bc4844436a221db311094f8883a49440a66a1fe1250f9d6087be8843d74e21e79210f1910877c4943ad58a1,0x3f523317941989c60ccbec066674e3327891985990cc1a5c629d1a32f6861980c48cb983465e55232ee941974c60cbeac265fd4f340698994344ccb88ca61291,0x96b5223b5a861da50c0ed3ad096a5563b56a31da8cd08a365c46b3223afab011a95392a3a49751d12bb4634519e48a8f0ebc677f3233379709e1cb0cc6ec866,0x8a7d1805248a9a8945c499a2e34c5577f5e0bbfad1db3da12daeac76df463b6b9a11bbcb88dce44877f2033bf871dbdd808dae9c96ef243b77891daf9a0e54a6,0x96a0a9c47f53e23f69211f69988f9849a1214e8bbbb505d9d982edec4177f260bc79105ebcf82f3e481756660baf3105cf5802e6a44172b6a0b91b305cf5382e,0xcf67b057cb65b28508773292888401f8f47634150a44c251205002913ed44897662443af1169c8890de7c486724242b33121189083da4448136a2405b31200d7,0xca2d543a9805262a22d4d2a4a5382c505898c0aab12302c6810cce169d47346a60ccc169a1c9039343908727283c2c74a0d0b1d0e021c1067eba5cae06bb59aa]
def page10 : Array Nat := #[0x7880f0a1e04396071c0e0218802ce07a807400e641c98387073c0e441c087280e261c20388850e0f540ea01d303a407240c9c19202260350049c1cc3a98724a,0xa0a541c9839207220e9c1cc0383074a0e581c3838006240c9c1820303060004240c98d831a083e845cd0b8b17142e785cb8b9116022a844c50aa6174c0e441c6,0xa86af0a1c06b80d69ea6381c74388cb1195255e4a846c30d0e0b6816b42c306970b560a5c110261c4c10968529125204c22908120e26a3432a8618f4f1eb0155,0x3e0e481c68328050c082414f8a92151a2a1c34801a6046804381040201036a06cc0d901b0035c0a800c30a8c126624c44978908114c20d04040a870d6816602c,0x45020d05520a6814a018d03180a60046900d27522ea05d38ba4171a2e245940aa7151a2a245048ba907420e501c7078c0d181ea01d00393071c0e201c303a707,0x552e075d54341d6c3ab07565718a5352c0a1c052ec9dd917b22de5734a5692cda8d5582a9f55609a6515018a5013a024014b0ca5193a32586480c8b1b6226343,0x2c4641d693a6240d4c0e160b6216602980518082c16d005725b23d4a7a2cf439d803a627258e459c87390070748128c25104a109415ac5a18d1b1a2635842a78,0x7240e5c1c8838c07020c20189030506220a90086820505260a301cc5392a71b4e128cc5298a5254a368c25098a1206ad894d06b205340ac0158ea93d5339663,0x41178e081b643a6474f0e971d1834c46840e111862302074c89a20d601cd010c22b443348ac10c22234423080611571e973d147ac46418fa407320e4c1c40398,0x107200e3c1cf839807060e781cb838807020c44182830306020424102829f0510022c1cc37846f06d661b4c35846b06d261a0fa88a35200a180d30185046808c,0x580c882b105500ac0153869f0b08141024886a20336088810e81a0033e064c0c801220136008800e9ab11d403a386c38e8d1a0e3e6c38806130d361440209879,0x98012c021801f803a00300010010a018403e725cad19225257440ac81292a7193e327c55406a7094e1aec05004b8094a124024584800f460a541488289043006,0xa5cd4d18ba315c6218c1e180d3348061805792910c6818c030205ab0b4c1a7c34c05840c12101030b01b5035e06b8151959a2a305058ada91b5152c08fc10200,0x2402068c0d145aa0b0416072c0c5814b1196228b809b25a743648ac0cd39aa7351a6a24d439a09314e6258c4399b31c6818d011a40a7417072b8e4b9c9538307,0xd400ccd08044fd3807ee7c03cf1a018b03008484801d6c9a7ed4ad2d8a5682acca4146612bab3480279a00114d010682b99b6cf5f2d4e66f22104803d198a44a,0x3c33e0102a802acc30072abca3854c518e8c283e84141e020a4df48021b84010dc10081ea433e72819dba60cfb548632e20039f4c055b9700c9c60077e1411b]
def page11 : Array Nat := #[0xa9c16f51a0b4689059b0482c8e3408474e03678901bb4680f7a9c3685121b2e090db9c48406a2427b54e11fdb100e8d7804743803ad6a01c6ac00ccd10078680,0xf3e3407971203c30902035380e8a36b735135b9209ac0f4680dc624064d6404558a01f75800e0a48303d121a708a0c0c4486ca024384f4e038b8d01b5c480f8,0x5181116549c1d3e4cd789066bc182c6e2405031200068900004481076c1275b3292d8a52de8d00706ac0378a401b96090ddb0e8100ad4469b3e2416b21215d38,0x72c4483a38600d351a0360ab01ac4c017d060cbd83e56b8a025884e917908088731e35d4a21b69d20198e491cc71a8c858f4686451bb5a4c39bb061c90830e85,0x8d03e94481f36101f8c120bfc3607ca0203f96c40fc35a07868d03c14481df825febb325788be2a245e13d02289ef54e0746860392d3810f6c0a9f17c2c309f0,0x85206533290304e94813c68240ad46120519a090228d05417aac082bc1c0d767b3982b65a9f8de411489028bb8d80f745607ca2703d70201f76d00fb53007d6,0xa84fa7c5144d4a2a135101580d0402c000201114f560089ba90044bcc0027ee10013cf068088f29404c586a14b689d0a0b04e82075b5290394e9481ba40a40d5,0x7e9f5d1a5492e8ce8497466424b0a0aa6510b9d50085be6c04437200216b8f010bfcf8085de34042bf3a2a21b8b150a9950a853c40542961e2a141221509cc78,0x9c3467c301a2f7ac05179d5028bae98145cf3e0a2e3920516f95028b5a7c145a5240a2ce12051c5cf808dae48046f53ec2346926119b09308e3e7d746df24ba3,0xd1ec481e8f5210f4775583a3d1a21d1db538e8eca487478a443a396121d1d556088d46884473d28223cf9f011e5c9008f0c48047453f7239a92b91c9095c8e1a,0xcd4fbb46a9fdda2ec2eec0160f768b13fbb00083dd20ada8e9076c87475d463a4119a1d206990e902468747f36a023f29d011f748008faa10047ca667a3dc9d3,0xf80d35e14069af080b4c3a605a63cf02d25ca016936120b49f2705a494802d20a381690d4c0b4890905a3dd380d1fe7c068e70a0331b8301a36cf80ca0a0c068,0x5e42a600d294880683a14039094c5b138852d27b559091165c86a0d4e4444292222834690d10a248699720034afa801a59d000d2ae380694f0e034b7a701a5dc,0xb62c1790d4c0bd8d1205ebdd38135de4807aef126a5778535eb5539b359a48d7acd126a56585359aa4694c73224a69a01a519eaaf00ccb4400d36a0c04eeb5c0,0x205ee9150297308817b4f5403db3a201ed7cd80f6ae4c04d67160bdb7a705f31c282f98e1017b874c0bdc78c05ecb9502f67c4817b364e0ce2e8b05ec2c98298,0x7be03033e589c1534d580938928c47d1d580a670ae013364b0099a210073dd303ba12921de855a8c986ab0676c34432615a119309550c90e64467bbe540a5d92]
def page12 : Array Nat := #[0x6d90a31466051dd2642bee5b001f6e9a00f3e2e804da12203ed4b001f641f00fb00d004d786a43ea6ab1df411f0eed726077bf0303bc4c9f1a61a4c0cf7a07c6,0xeaa7a69f4d3d149269e7a4134f34249a78c904efac5d003db2d001f113000f7091007ba49003d90f801c91127da02b0187b6d98d691a486b42d123573ca71877,0xf740e3a811852ebc1c520aa2070082a03c9adccd8288fb4487a84f53829f5a7c14fa5240a7c612053dada809f96cc04fc35eaa7869f553c1492a9df8495a2114,0x48f1324016149386a4c010c0087e04ef025b8117c1a8dfc6eda0f6a4fb5abdad46da86f83086923052920d094480109d60ad40725c11269e920e4529a182f081,0x9101c100e040720038439c01cc2ce610730239809cc00e20a718a38c49ce40a11a44812208110108b0a00967ecea98a94a10a60252d4296914d3aa6875293a96,0xd0393e01a31d580ea3471303825144c082b8313a188b0c4386ac020300eb004430206010800035520e9d21cc95c649d32cd8b070593c239c01c580e28071203,0xf3e9df058210410e1c840c4804a4c194c0c90044382a98033c029e014400a14040a009e6fc6b6a0db52eda886c4f36299096855ab1e0b8c0cc613a28a6100888,0xa2c46d4049c0c00cf862067927004754c821ac1b12130d934186c3558295626148990ca4262c3106870782a803c754c1e2a8c0f0284078d8443c00101e100400,0x9c161bf24b082f0cc3a39161a949806be0e825e0740adc3001381800ba12d72125aa2a93b514c87a8b24c534c0629ac1314b2c18a5ae4c52562628e3710d0ce8,0x111b56a944494aa50db56a043c94a810ea529ea13138c68844c31a1f110c5038440040808000b1d80500f1421f6f240fb51087df6a63cf8cf1e30814f3dd3c79,0x898bcec211ff2d0897390c225de1d08777864225d6410847783c211d60d087758f4225c2330896d4bc225bd3b0896bd14019a14afd664183f51a51acc36e4eb3,0x725a14d5c7be2054d2ed4f4f79e51d3d299214897dd0c225ff3508981ca4226171d0877fc6c21e171908983d042261f2708485c3c2120f0d08783cf4226272f0,0x415881541651d02ae8966e442d01000660a42e3cc40118f4f145e35351178d4e54be3138d198c4e10663182d0b8b4f54662d3bc198b1ce195aa729615f46847d,0xea658741c0ee0c8f12b0884815a0ca193b85701e24d9237e60a6bcec1ac491276098938b50010001ae8dc6b888e6818d99b0848a02394dcca6d04ee728af86b6,0x3610439542933108a10990801c8888877666666665333222218e45dba817e805b9366e21d72815c4d970872aa04ea012a4d8988718a0461361423a5e6787c1d0,0xea1d0399710cc98d30c22844d592a9542a68c62b1550a814c988464868862314324220a413d52e6b4d7a372ee598ba1954665ccb117032ea1d0399726e219431]
def page13 : Array Nat := #[0xe9b43aac676a761e9a03aafe2d1d62d12a641764ec5d6b91740e2198b0821c6c8d6aa03104c48403101ceb1cf39d750c7910aac55047a10fb2752e85cd38c762,0xe638844e86b205053431f63775fd4c26fa1857f2932fe3273b54c26aa184ed2931d63272fd5ae639a5cb634b92aad726cd2e451a589d4043a92e6c7062c736e1,0xaf6a755094fa6579949a539874a5266d4a4bd79509b520345e2f6a3c6e8a76dd8c2df9399bf113c3c8a7595ac2b5a2996b3d3a7ac615149cca1889dfa4509c84,0xc9808a006ac049800a00ad249862a9da854fb31eb760553ebcaadd40563991e9f26156e1c2a39995472f1e8e2612eac5aa11a252e314a6b6a94c6cd79cd83531,0x5028d01e800e200a800a3b6623661b6069e439bea4ae84aaa4aa84a430ae5c765c2c68086408580aac0a8cd468d064d058dea41e841c301aa41a8414301eac0,0x40a52010015015681a0d2933c63596754659b6d96765439d6c666c1659c81966e61801d0d0203810d00438c0ecc038c038b04ca05098d070d078cc48d03a4c3,0x335e056154815953403d74a00583160146998151a5fb143c9df4ed51793f4cde4f5277bbac4de4eb0f7babcd002bb34a32ecba8ea3347884cd1a426520507150,0x476988ac890d2620a23ea3d3f92f13e23c2d83b1161684505f00215de1fdf77c7e025e958032976014a5f017687e01dc1f009685600dc0c8153b6a014cd9815,0xf26f10e50e26d1061c90ca50a2651021df4ef12e4ee12908b4eb12a4fa13b48b1eb07b48b1eb0caa999998887666554444333221027f5453e4c9bd312f9124b2,0x2ef68b2ca34518a2f119019628914b64b5ea64a3451a22811490eb62b32b1cb5eb2eb18a62a33a1d10ff4ef24f12f4af20f0ee4ee24e12b22b1e906b0ea0ff50,0x75b617c76a010e20973f24b06b0a55ea0a35f15f05ff26b5eb24b20a5e95e85e766b22b1056656255ea22a1025e15e05fb2ea2e656b1053252ea1022e25612e0,0x685b36bc8cd65c67f4c86834bc67c43026566b25f65f2bbe4d21364c41be48417c4881164840d448aaa87773274ebd64ebc126bcb36d162e5d60e301063060e3,0xf64c2cf6407cb4bc7cceccaccec0acee9c2cd6447c8accac8ac02c94447c44bcaccec52b2e642976bc2954d02914bd81065d6856c0661630681430acd6c82b36,0x542b0e1289884384b0c1da40ac784aa4154c0daa029508a444b4e1d270e89072a8274e12a90953842a82b540b92069502a481a5005130281f32382007756bc7c,0xc788c3839101c870c94024381226010e0044144508916338d1a948ca346b022d8f12c18943c4a0625a40ec1876902b1e1127004214424911044aa16528aa9c51,0x31868b3209990e280702038002c7e361b1a0d898ac4ccd84aec2336195a495d2e0e75073daf8ed3ad6496b12b32201860d2046b0835041ac80b2445422298b16]
def page14 : Array Nat := #[0x712095813d2240be44025d931207481b5418279c302d52411075211ae98321c88245921857522136a0012c98231322284060802c9ae4c169509aa64c54260f90,0xd28090ad8f052d50f04a9d0f031c612199caced4a1ea9563411e868195a90b0b2815d4502b587019ba40b171e04d49012681817b83325a4869343cc7ed380ed2,0x99ca47465ba975a5ba674ac2a974ab8aa74a55a700a3d27f49db8c549cc11549d3115498ca600d8ca400a5ba901a5ba7010d2a90d97c87098f48609a5da8098b,0x544433211004df2097e4923892359144b248344bd2f93f0fe9fc4f84e4fc2742586b4f625c2527a12a13c09101c960ee18d48740ee2accaa0099ca775d9ca576,0xee50e26d0e61ca50a2650e21df4ef12e4ee12b12a4ea12f0cf0272ab0cb0332bf48f1ef0270cb48b1eb03a49a03f48f0c702b48b0cffffeeedddccbba9876666,0xa64a34517229a62a1cb1c710b14b02339b32710b5ab2bb03b1cb5ab15f48f50f26f0cf4cf22f02e4ce22d02b2061c60a70cb4c50da4df4ad4a74b54bf50f26f0,0x60260168160108061f5c93073072c70853052c50843033030c131031b5cb1491a71aa3451aa3041a30c01a95a76275cb1270856255ca1250915b24f628b30708,0x513632a5b1428c72a76c402311a8cac42a448d364c1670f0148449ed3aa2e9006a0d3bd019de9200b418fdbbaa7420b6074ea60968908762b12660562560a124,0xd0f3fb77254c0eac30b2ec0273613f5b21becd02c6342d3150290d96ad90e1668627162c5b011e9807aa100a212acdb118ac70af6c04eb1a2353010686804210,0x514fa704a3549451a9c15194c528ca4049dd4d44ee9e1265535132a7a89ed42833e48417e2440b5921052896827e3e410b1f20350f9d9e87a807e3c400b1e202,0x61a32fd321986982c5a62560511aa2dcaf1169d988b164845656622a512114857e885462462b32a2759851228ca883461447b32222d9510f6ccc877656129f52,0x47b566a3cd1268b0d3aee166076da303b54181dbada2edf6c1771630bb5d345db29828d0645767230b32d97198ac68cc8e24660a1a32f40d19bed80cfd660663,0x2900122059115261511158f0d8109950da4058f05a7152712a70b0e05a805280513010e03ebb35b433aea51b1714118e8a888504028021d59111f9d9a8fb649,0xd810da40581452445a43d8f3b0e0d13090e0ba4058623861da41d8f1d2419ad0d860581059333873513328735082e92218a0b0e03a90ba50aa90aa50b22052a,0x2113090503091302138312831525130e058f0580030e2c882c872ca623a41395130e11af04aa24a422a720aa25861d06190e09130114218c19141da91529158f,0x309038f028f0a11098b0b8005a405810524050103984b8449984983400a1488030d051302089b98959291989127890e710e2b880528a5896b84692b611439a6]
def page15 : Array Nat := #[0x178b260250f8012729a81888193008b009b100b4013138b41ba40b950b810d8609950b8602865b9c4d834d034db020182118199500151c930c8f0a9008930c91,0xe0471891c01cd9400e1c6006f45003551801750f7a1e80bc6ce05c87a48e1348958da43ad136a1623a0cabcd0f507ac41e33604a17b54407b90205ad30e06e9c,0x90d43ac077495464aaa9dd4238c9691370b269b1d12496e528e4560475ab5002cd93ad4d445694c25051716820d274142d39e872b0d289584204a52225d39080,0xc455013c4550f331b48803134860444d9303155280213d8fa211d0fa210d8f820f591720dd11720d6946a01ba90202aa903bb4b42ea897930b00c5d06b622c75,0x7022a513da2b592a227b220a2730b0a26b8f08a95a50a2628f0d46da705474a730a1ca53546b09321f4a60a44ba90a1eaa90a1dd8f021d50f051f3a444bab8f3,0x52a0a399220bb741103b85a65bb93115bb7d265a3638353b35a74bbbd274b32590032fc0803385a663313086330526632f39f5b2eda75b31d275b2e19f5dadca,0xb4b054a8a4a0b499d03224158f0245d0f02445996a435196a3ed8a5a3e50a5c4499833b4918341d098323b32204bac940bbac920a3ac9108c4daa0c44b900bba,0x2899440872d26c7ec1fc0ad9224901be45e7a819e4da788756a0559364e21cd281344d8a88f4be1d8738750e43bc1cb6332605c071422cecc6172a8eb6833bc8,0xe70103c50c07832dac3aec651b1a644d3c89871c4158944058887018e452d92cd1c62d8acc9c429928d1460451c67d43c9bc4394389b441872432d42c99c4294,0x6245a4161852714485091040da061651240e30a1820004edb10a3a6254b2d0291d99523af1e4b26144acca89578f15130a12635402d274ed4829d9419371bb81,0x42c3858112a04a40a980a8124c492123c291024cb0e1218593144c90e363c583140cb8f16905831490d03369058f0ea43a60aa42a60e44d2a2a44d271448d921,0x50b8e44df2202743d5ee0c2f4902543c1f6a91d69c97648fb69c26610280e902a412a83a70a9c0aa044d90e443891304535296a35913022211436a459414a4d1,0x8f34a714d2942e3a9338e9852aa95482a82b4908b96aa3052ab3b224d7c87b396a2cdd28d4ce910145103ef22c6d6a46b65068e37e7453d322c60e345ca362d2,0xfd3a93f2aa5534ac54f2a]
def pageData : Array (Array Nat) := #[page0,page1,page2,page3,page4,page5,page6,page7,page8,page9,page10,page11,page12,page13,page14,page15]
def pageWord (i : Nat) := ((pageData[i/16]?).getD #[])[i % 16]?.getD 0

abbrev Segment := Nat × Nat × Nat × Nat × Nat × Nat × Nat
def segments : Array Segment := #[(1,0,0,4,0,0,0),(0,10,0,4,0,0,0),(0,10,0,4,0,0,4),(15,10,0,4,0,0,0),(0,160,0,4,0,4,0),(10,160,0,4,0,4,4),(162,340,4,8,2,0,0),(13,2368,4,8,3,8,0),(51,2649,4,4,2,8,4),(445,3925,8,16,4,0,0),(156,10379,8,16,5,9,0),(82,14203,8,8,5,9,4),(46,16587,9,8,6,0,0),(9,17377,9,16,6,6,0),(8,17584,9,4,4,6,4),(1,17794,0,4,0,0,0),(0,17804,0,4,0,0,0),(0,17804,0,4,0,0,4),(12,17804,0,4,0,0,0),(0,17924,0,4,0,4,0),(20,17924,0,4,0,4,4),(142,18284,4,8,2,0,0),(19,20060,4,4,2,8,0),(52,20460,4,4,1,8,4),(39,21708,8,32,7,0,0),(9,22387,8,16,8,6,0),(10,22611,8,16,8,6,4),(6,22899,6,8,4,0,0),(0,22989,6,4,0,3,0),(0,22989,6,4,0,3,4),(1,22989,0,4,0,0,0),(0,22999,0,4,0,0,0),(0,22999,0,4,0,0,4),(45,22999,0,4,0,0,0),(0,23449,0,4,0,6,0),(2,23449,0,4,0,6,4),(639,23489,6,16,3,0,0),(140,32036,6,32,4,10,0),(185,35426,6,16,4,10,4),(407,40678,10,16,7,0,0),(99,47857,10,16,8,9,0),(80,50600,10,32,8,9,4),(27,53110,9,16,8,0,0),(4,53614,9,4,7,5,0),(1,53711,9,4,0,5,4),(1,53739,5,4,0,0,0),(0,53754,5,4,0,0,0),(0,53754,5,4,0,0,4),(1,53754,0,4,0,0,0),(0,53764,0,4,0,0,0),(0,53764,0,4,0,0,4),(12,53764,0,4,0,0,0),(0,53884,0,4,0,4,0),(9,53884,0,4,0,4,4),(118,54046,4,8,1,0,0),(12,55404,4,8,2,7,0),(47,55640,4,4,2,7,4),(39,56769,7,16,6,0,0),(9,57414,7,16,7,6,0),(11,57628,7,8,6,6,4),(1,57928,0,4,0,0,0),(0,57938,0,4,0,0,0),(0,57938,0,4,0,0,4),(19,57938,0,4,0,0,0),(0,58128,0,4,0,5,0),(15,58128,0,4,0,5,4),(307,58413,5,32,2,0,0),(47,62147,5,8,3,9,0),(142,63211,5,8,2,9,4),(172,66851,9,16,7,0,0),(34,69874,9,16,5,8,0),(42,70683,9,64,8,8,4),(1,71952,0,4,0,0,0),(0,71962,0,4,0,0,0),(0,71962,0,4,0,0,4),(20,71962,0,4,0,0,0),(0,72162,0,4,0,5,0),(10,72162,0,4,0,5,4),(276,72352,5,32,2,0,0),(62,75709,5,16,3,9,0),(160,77093,5,8,2,9,4),(506,81193,9,16,5,0,0),(144,89071,9,8,6,9,0),(230,92833,9,16,6,9,4),(126,99638,9,16,7,0,0),(49,101852,9,16,8,7,0),(57,103113,9,64,9,7,4),(12,104832,7,16,7,0,0),(5,105043,7,8,6,4,0),(6,105150,7,8,7,4,4),(3,105307,4,4,2,0,0),(1,105347,4,4,0,2,0),(1,105363,4,4,0,2,4),(2,105383,2,4,1,0,0),(0,105407,2,4,0,1,0),(0,105407,2,4,0,1,4),(1,105407,1,4,0,0,0),(0,105418,1,4,0,0,0),(0,105418,1,4,0,0,4),(1,105418,0,4,0,0,0),(0,105428,0,4,0,0,0),(0,105428,0,4,0,0,4),(9,105428,0,4,0,0,0),(0,105518,0,4,0,4,0),(15,105518,0,4,0,4,4),(89,105788,4,4,1,0,0),(10,106859,4,16,3,7,0),(59,107063,4,16,2,7,4),(51,108436,7,16,6,0,0),(9,109280,7,16,6,6,0),(32,109485,7,8,6,6,4),(1,110345,6,4,0,0,0),(0,110361,6,4,0,0,0),(1,110361,6,4,0,0,4),(1,110381,0,4,0,0,0),(0,110392,0,4,0,0,0),(0,110392,0,4,0,0,4),(11,110392,0,4,0,0,0),(0,110513,0,4,0,4,0),(9,110513,0,4,0,4,4),(105,110684,4,4,1,0,0),(11,112052,4,4,2,7,0),(36,112284,4,4,2,7,4),(92,113184,7,16,6,0,0),(32,114790,7,4,5,7,0),(25,115582,7,8,6,7,4),(3,116310,7,4,0,0,0),(0,116350,7,4,0,2,0),(2,116350,7,4,0,2,4),(1,116391,0,4,0,0,0),(0,116402,0,4,0,0,0),(0,116402,0,4,0,0,4),(16,116402,0,4,0,0,0),(0,116578,0,4,0,4,0),(6,116578,0,4,0,4,4),(132,116692,4,4,1,0,0),(38,118408,4,4,2,8,0),(65,119246,4,8,2,8,4),(143,120907,8,8,5,0,0),(44,123339,8,16,6,8,0),(66,124463,8,8,5,8,4),(6,126383,8,8,5,0,0),(0,126487,8,4,0,3,0),(6,126487,8,8,0,3,4),(1,126603,0,4,0,0,0),(0,126614,0,4,0,0,0),(0,126614,0,4,0,0,4),(6,126614,0,4,0,0,0),(0,126680,0,4,0,3,0),(10,126680,0,4,0,3,4),(39,126860,3,4,1,0,0),(3,127358,3,4,1,6,0),(17,127415,3,4,2,6,4),(62,127821,6,4,3,0,0),(19,128785,6,4,3,6,0),(18,129195,6,4,1,6,4)]
def triangular : Nat := 0xfffffffffffffffeeeeeeeeeeeeeedddddddddddddccccccccccccbbbbbbbbbbbaaaaaaaaaa999999999888888887777777666666555554444333221

def extract (n shift width : Nat) := (n >>> shift) &&& ((1 <<< width)-1)

def bits (p width : Nat) :=
  let shift := p % 512
  let page := p/512
  let x := (pageWord page) >>> shift
  let v := if shift+width≤512 then x else x ||| ((pageWord (page+1)) <<< (512-shift))
  extract v 0 width

def expand (u : Bool) (n : Nat) :=
  let pair := n &&& 127
  let b := extract triangular (4*pair) 4
  let a := pair-b*(b-1)/2
  let op := if u then extract n 7 2 else 3*(extract n 7 1)
  let keep := n >>> (if u then 9 else 8)
  a+16*b+256*op+1024*keep

def segment (level kind : Nat) : Segment := segments[3*level+kind]?.getD (0,0,0,1,0,0,0)

def get (u : Bool) (s : Segment) (kind i : Nat) : Nat × Nat × Nat × Nat :=
  let (n,start,pw,block,w,dw,sw) := s
  let aw := if u then 11 else 10
  let parent := bits (start+(i/block)*pw) pw
  let size := w+aw+dw+sw
  let recStart := start+((n+block-1)/block)*pw
  let v := bits (recStart+i*size) size
  (parent+extract v 0 w,expand u (extract v w aw),
   if kind=0 then i else extract v (w+aw) dw,extract v (w+aw+dw) sw)

def roots : Array (Nat × Nat × Nat × Nat × Nat × Nat × Nat) := #[(0,4,6,0,0,0,0),(0,0,6,0,0,0,0),(0,0,4,0,0,0,0),(0,0,1,0,0,0,5),(0,0,2,0,0,5,0),(0,0,3,0,0,5,0),(0,4,6,3,0,5,5),(0,0,6,3,0,10,6),(0,0,4,3,0,16,4),(0,0,1,3,0,20,4),(0,0,2,3,0,24,9),(0,0,3,3,0,33,5),(1,0,1,1,0,38,0),(1,0,2,1,0,38,0),(1,0,3,1,0,38,0),(1,0,4,1,0,38,0),(1,0,4,2,0,38,0),(1,0,6,1,0,38,0),(1,0,6,2,0,38,0),(1,4,6,1,0,38,0),(1,0,1,0,0,38,0),(1,0,2,0,0,38,0),(1,0,3,0,0,38,0),(1,0,4,0,0,38,0),(1,0,6,0,0,38,0),(1,4,6,0,0,38,0),(1,0,1,3,0,38,5),(1,0,4,3,0,43,0),(1,0,6,3,0,43,0),(1,4,6,3,0,43,0),(1,0,2,3,0,43,5),(1,0,3,3,0,48,4)]
end ReducedData

namespace Ledger

def field (word : Nat → Nat) (pos width : Nat) :=
  let off := pos % 512
  let p := pos/512
  let a := word p >>> off
  (if off+width≤512 then a else a ||| (word (p+1) <<< (512-off))) &&& ((1<<<width)-1)

def packed (width i : Nat) (pages : Array (Array Nat)) :=
  field (fun j => ((pages[j/16]?).getD #[])[j % 16]?.getD 0) (i*width) width

def tokenKeyGet (i : Nat) := Ledger.packed 1 i #[
    #[0x2]]
def tokenIdGet (i : Nat) := Ledger.packed 1 i #[
    #[0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x3efe004f2000ff00000000000000000000000000000000000000000000000000000000]]
def tokenLowGet (i : Nat) := Ledger.packed 11 i #[
    #[0xbc01810018030050032dc5b40496c9572aa54ca894f29a5280f0160340700501a030060080160200400a002008048080040080380600a0100180200200401001,0xcb694c5c80100900400404171590b2d66acc590b2165cb59692ce594b19612a2529700040080400200400801008594b2657cae02200c0396e00eb21644ad9585,0x9eb25682c8590b3d642cb593314b6cc498730a60cc097f2aa5f17001204c04809012024042c8594b3a5ecbc9772ea5c8120160040900b01002d642c89712dcb9,0xe684cf00c00cb78162ec05564ad359eb26674cd9992ae6597200200800804004b3566ad259ab3568cca9933226381498d29cba97400400804002004008020085,0x7f2fcb216417d9b736a6c8072de01cbe00703001e6c4d700c05cb78162ecb3566acd59ab526b4d52f45ee6a2c8590b21644d32f45e4bc2c859ab2165cd29a25d,0xc0180b176032069642c899f384031760325b8b69835905b4b69822da5b4c0ac8590b5d642c85913826f9802fcb21642d7590b226f4dd9b85f56b2d65aeb596a9,0x73ce600e6100396e00e01c03ac82da5f0b716e2dcb2964ce500e01e724d799f38cb796f2deb21644cf00c5b80b4e200c6080e16e00e06e6796f02c5da684cf00,0xb9df3b8c098c3165f4bb98a31260d6aac8590b65642c89da620c398230e61d642c8590b61642c89d8b20b74d230cb21642d730ab35641852db3ae754e99d1396,0x668cc9982f2b21644f432e658cacf3590b21641949e064cc92d5590b216dac8590b21644f29e25fa782cd322b227819031e5e1642c8590b216418e31ab69642c,0xd2dc590b71644f9590b21642d7590b21682c85973e27bcd49ad35a6b16d590b21642c859d351642d75913da6b4d65905cd642c8590b2269cf59a666e7918a9e2,0x5c2b816fcfe9fa5d0c02cd346b3566acd2f45ed642c8590b21642c82da6896f16e5906866ecfc34061ccf96d302630c599e2fa675642d5590b75644fb338b227,0xa1741a79e1400d22e735a6b0d59aa3526a0d3add5bab756e9a634ab756eadd34661cc398230e61d66ae45c8b9972ad25c8b927f9a459ab34c996e5c0b8d712df,0x4fc326648da2c85aeb21642c89c1408c017e5a6b2967acb593404d9add5baba966acd5c0b356eadd3646116eaea5a8b44d8ad4360654d79875c8ba5721ae590b,0x72b21642c8590b21642c8590b21641b8590b21642c8590b21642c8590b21642c8590b21642c8590bad642c95bd40cb696d330b20db997590b21641b63326d4b7,0x285d0aa1342283d06a0b4100b022040084dd9bb0400580881d03e04408811022044088110160780eac85906e9652c9594b21642c8590b21642c8592b21642c83,0xbea4147e8f1bba3a6ee8e51b5e7469792f0046bbd78af05debbd77d19a3145e8b515377450ddaee5dabb1642c8a266ee891bc37a6f4de1bca2344287d0ea1b43],
    #[0xbfd7f2c8590bf97eac85f8bec12afa2db4b69652ba5409294d28a4e6ee931bb590be4e05252e749291d2237eb217c2e85eeb21642c85ecb217aad75e8b22909,0x84308616c2984b0860eb21642c8a76b216453a608c1183304608c1413b04a734e0131bfa6f4da9ad34a666ece0b03604b2180ac85ed4ca98d30a5f4b9642fe60,0x10600b41782e0400b41702d0587181002a056714151c462cc618bb0a62cc54b6b04590c50de1c13820a589ac8624c45821c3384c4187ac8590c3986b0c050c21,0x71ea2d4406f50ea1541a814fe9f53da78078161bb040084140210420b4150200680a81a03605a0d41a83205a0b4190200400c81083405004c1782f0660c81883,0xe1c638c0b6ad82d32e726ad02d32e6f2acd5807c0f6abd56aab552a9d52aa20f2a803b0640841081e376722a7d4ea9b532a5d4aa920e81cd4807151ea3035064,0x39872d8e31b088c698cd71ae15bc219bcadd5b6b6042ad75aab4569ad0106b3d66acb5901d82d08158eb103fac3582afd5eabb570179bc3786f4de1c6378728d,0xf2bdd3d396c9d93325648c8d642c8644b21642c8590c86bd5793795e0de55aaef5d8e71cb064c818f31e63cc78e684663ec798f31e63cc76ba845ae95ceb91cd,0xb3065ecb996b2c656caac58473a9628de589b106f2c3d86b0b612c19bb3a760ac09d23a20b416329590b21641d0590ca1642c8590b2164580aff5f8e857d39f5,0x2606009b3c676ce99cac8590b21642c8590b219c33766cb21642c85aab21642d566acd190ad5b25646c858fb1d634e39d73ad5ece9d8c3aaccc24330664cbd98,0x2cf51b6a2d41642c8590b216434f69cb22ced9cb37669a6b4c696131a534968ed21a3b4768c12c25345688d0da1599b3165ecb5953ad651a0849680cfd9f33db,0xc56b4d69ac3596a6d4dacb536b0d5ed39dbae06f0de5a6379694ed5a4378cf1ab355590b20ecac8590b21642c8590d519e3535aad4ad1d40b45684ecda0b3e76,0x8d79aa3540a0d75ae5ad09e782d61c709c77ceb5ab09a770e59c5678cf19e33c66ed6d9e33c678cf19e33c678cf19bdaab4877ad4973a476a0ee9d63b872ce99,0xb3b1e0a878edb5b5b696ced91bcb636c1b33656c8d91b23636c4ce429b610a4146d7d5eb5c788de1dc396768ee1cb3c2d81aeb5d6bad75ae35f6bad75aeb516a,0x1b80768e3dbf6e8dd16436d590b21642c86e6dc9b8b706dedb9b6dbeb7b6f2dd9d6b7476adcdb8b6f4bad935a6d8c982aac8590dad643636d4d4da9b696d0b21,0xdd1ab2c8610b21642c8590b216dac86fadf16437b611722e39da37771ae19dab714bae2dc43c970ee137a6f2dd5642c8590b21642c8590de19bb77590dd9badc,0xb3856acd59c2383704165c0b806fed5aea5d33b557ee95d1ba173cf49e83cece8f31bc610c218430b61016184b7e6117382b834b9b732afdcbb957242b1e53c4],
    #[0xbc074eefddebbb772eddda3db764f60353d8e39c6b8c0be179c5b8a0bb762eb85bbac1702db74678e258e37a66edb1c438770cdd0f585abaa71cf59cb3d4d59a,0x21cd399730c656439772ccf18433c5b5799ca9efbcac2daeb53590e5184308610c2dc9b09611791c933c722cf1aeb3c6b4cf19bb30720c8dc7b083dd78ef15e1,0x31e2e67c9642c8610b21643a959061183ba8610cf1845e8bce720f8ba774ce95b2364696e91d1b43742e899bba10c2e81cf8603e0e79ceb9c39ae6d9bac8590c,0x90ed1d9bb3764ec5d7bb175eeb9d83af75d7aef51f432e658f99bc75aeb1d5b266e57a5b23086f81958436474c789b20646c8c1831b62678d799e33c0c4c25d5,0x16430b590c2164042610c20ff308752ea5dd3a97306ed843b96147f4fe1fb3f47eaf6ac8376b21641f9590ee1dbbb6590b22f61f8590c2d839f776a7d8faac85,0x7bdeb20ed3c5384819643c45917b9e1ac80d21a102bc20ce811e0bc0406808e8a013eab21dfb08610199df3bd400ef0ffb0b590b21ddbbb3ecc21843086dac2,0xcf41afa0e41c83dafac8590758eb20e41af3de72c80dcf35642c8418f31aea0b0da829a5b47796824363ca590f25642c82da822f81f50d6f21e3bc65901a8dda,0x842c8590c25ebbd67acdb5eaac80e0f51bf1bcbe2b21643087a6f4964367610c2037ac8616b59aeb51678d799e3d15ec84dba3745ecd750921142213d082db41,0x859071d0e3373f4d590dbde7ba829ee2097b6869841fa610f68feac80e2c25ddac87b2f61ec219610c20fdb643c4b2164042430b210ba1642a850ed3d4590b21,0xb21642c8610b2184308616c21852c8590f8efbdf6beb7d2f9a2043e825f120943cf843a2c8696f810f34bbe41cc39316630f7d8c30a62cb5ddda1c5aede90eac,0xd01e0020043d07b03c1e8020790f289c00876412ea5130787a0d75a8b3c6bccf112a240dc825f32234441a83b8767ca7e4fcac87c88843aaf63f4b2104ac8710,0x7e4fc5643f0590b2164604a7b80f0122b7cefbdf3bee7cefb5f6601c008a80f3eb7d4b21f4ac87d0f9d642c85917feff228bfb7f0de229bf68a113dfabf37e03,0x4b08e10c1e6f118e0e4608bd15a2745cfe1643fc7f6feb06d2e45a71d643f97f0f456460cc1182dfbbf57ecfd5fa3f3c158243ee08c0f818de6054588ac3e2c8,0x40146c8d70d234468b21642c8590b21642c8590b21642c8466b230cac8801001ff8800feffb0c07ec2f85b0add0c288c9159c7590b21642c87fab2164230c278,0xf80bce31c638c60ce2a3c3920ec410310080ac410310620c4188311060c44101d44e0ed13a3b0762051d40680ab21642c88088e601a3846eb21642c8591009ac,0x11fe35c6821b19e32c638c317885c5d8b71662bc558a714628c4f89b11e25c4988c1003b47c0bc420013788f4b696d2da89c31a27c458871061fc3d8770e61b0],
    #[0x3f398733169cd48c9151eac8590b21642c84898f5225aac7d8f71e63b590b21642c8590b21642c85bcb216463ac7290120240c7187f1ba434849071b61b480b2,0xb21642c8c9992eb764ac6f927241cf39f878e824348c92123c0a77621e04b57656eee043bb8110220440881102204407c8f91b16a3ec8b91321e42c82913206,0x64412819045642c85919472864f3b092c15ac8820ce607ac8590b216440e81d035642c8590b220664ec9b5b8eb9d7494924eaa3b5e702d642c8590b21642c859,0x982d05a0b41682d05b2ce583789332bd39cac7972aa514a090d27c148290520a4148290520a4158287772a173ca79292017349d9492324d49822209af7590b21,0x6e0dc1a83d06e0ec1c83706e0dc1b83706e0dc1b83706e0da32cc09532f9bccbd9772e65b3d27a51965a4a6949249e747705a0b41682d05a0b41a8330620b88,0x3bc590c3e04667ccc8f8b696d2da718c19c94b4b21642c8ccb9912c9f959198d1e1c94b095d6f42382d089774215bcb796f420cc59852b25583706e0dc1f837,0x590b21642c88530a9644298139b91f66d2e79b0ddc2884eb21642c85910996442484b091642c86af9af356692e66f3341f53eaeed6425b30eb21642c8590b21e,0xbd00200854801782f0590bc1ddbc04be9796417361f02177ac85910216425d590b212e2c8590c3d642c8590b21642c8590b21e1c2b786b2177aef590b21642c8,0xa682da99d336224cb0df392c886cb21642c84c8b21642c8ce2708e62c886b0d131a044c10cc454324c4906189bb8610bcb9c2e4c30b52fa0ece0981644258599,0x5a65cde1c738e6f513a69c458871061fc3d8770e67312060ce2a693920043d0040080341782f05023c4708d1180041782f1160b5139973780b5641ff2da89de3,0x84608c12c2311f095d05a074067fcfd9f73ee7ccf62533d679ced9e33be76c5b9d71689302271c4200112471d1f26ace99d0489c744e9a4eb1d63ad568191bc0,0x6fab40b577aef5e0bc3469cdd19a2d0068a5debbd77aef5debbd77aef5df0e61c2f0870bc3449ccd1073343e86d0b8793726d401873421cc4d89af41e2d12e8f,0xfa5abee95c3c7413723e40c9c5352f05e0bc1782f05e0bc17843b5e10e978574d28730e689ad27a4b48a70401a4048af05e0bc1782f08750e84cd17d1e263472,0x4fc4488227a20b2b88710620c428831062009dd3ba704e69bb0c71d3969a3a47184109b87f0fa044088110220440887b0221e4088110f32063fae5a674c62dd2,0x24609bb50a7539a9a4de44a7b0f6224c4815c2b623bd87b111a22ea0ae9a7c560ab4a28590aa741542a4540a714c294520a31442845004e38e9cf4f20e05e208,0x89d3c9bc3ac758de1bc3ac758eb1c638a724f9ac8d4b137511c24f07093ba764ecbc2262f0776c81782f0640bc225af08748c0588b03782bf526a3c80977076a],
    #[0x7c3cd51a0753bbb5905ce28a7c59061cc3ac830e61d642c8590b21643bc61eb216430f810c3f33bdf7bef7defc508a0f03539c738e744e8af089f1393da7ad4c,0x406f01e02c8780745e043c4e0a05402c84fe25187a02810f02278000011622c4588af15e2bc561651562aaf98a8eb629c52d529fb3623e590b213eac88110f18,0xc2306ae4d7ab7566ab5002d1e045f8bea162f45d5909f96445c8b6b2142a844fd169418b3406a0a2c458590b222cac8404b21efeaa590b2101450590b221ebc0,0x6afd5e9ad35a6b4d69ad35c6b2ed1a93598716ca21439858d29c5434688cebc2334658cb19358eb0d5e9ad04a094125d8bb1768c71885ac617870f1782f05e0b,0xc8017847089e2e93da7a173a985c27b5e0bc178200874801002f0590c19642f016ea2b5a2c84d71b57846f8ddacf559765e11b57846c5debc164289590bbf59,0x23b476590b21642c85911d63a473179adce3eb638ea32394714d7ad4b7a0e2ec960b7a8030ebbe041cc82cb21641c2590001782f05e0a29782f05e0869458bb6,0x4d7475947a6a13f20de00be9052064047f5206f23f27e5211f52ea854e10e949291d731f14829017b1ece69bb8f4a3d4728dd711e63c4778748f9642c8590b2,0xbaf0eb3d0590d7d072d741ed7d071d641a8398347b590a5149a8d4f09e0e11d64d272587c8790cc3d87b0f75a301d6c3417eeb642c84d7671cb99c705ab21642,0x130d41a6348e10d11a08154c2c841ca5d640cf916338668cc40832c652c8314324640c718c9e0628c4186309310c161f229644189130f9d69738a0a5a4421352,0x91e36d358da1b2360e62c8590a7e383576aec250ca9e1ae3594ec8e91a9a24643f7b0a706abbb42aeed002f08fa9754da9a42a7e81a2174ba854fd21642aa65,0x9e93d2f01bd25d3d2a65e125946c951baa9564494780a921e49392524551aa21b8b20e8c3c590a855044c776801784705e11c1784705e0801782f0590bc2482f,0x6a8d1ca391878e393727a4dc8793b21c7149c9363857cbad91526b5f6bd4fcaad640e0554f9935aa9590b224ca854fcb224c2854e0839542f04f437d53a7a4f4,0x5903cc7926b4d6b21784a15e123d358f11e1281642f01deac5582261dc3b4762c88f6abe4f8eb1d43a53c0e85909e13c2784f037d570e755aa34733d08f6ab14,0x8b10e20c3f87b0ee1cc361f0179c638c60ce2a3c3920107f8fe0060041683b568718168fd1f83e87d8f61f43e47c2c81ee3ac7b2b31ea3d24dac8564b21784a2,0xac8590b21642c8590b21642c8590b21642c8c3d87b1162139e73ce7e22c438830fe1e56cad54061dc39b00e787cd7f880169d63ac75aad82d38c0b4e31973938,0xac758eb1c638c714e49f3590b2164665cc8964fcac8cc65b51e1c95e6bcd799025e6bcd79af32029fb24ec2d449f93a900570b21642c8590b23101cfd82adce7],
    #[0x48610c2164288490820e418421051300ac8202b57f29179aee206b215f2f35e6bcd79abd946b20e12bc53e8d11a2bb575b0d5cac8590b2164665cc8965641d63,0xdddb9b6f6d6d9db1b5d606d6dabb5369ed2da3b4367ece23a4700a91b235b37666cbd95b276411923045c8b115019b1f636c5d88450899132244448810f21c43,0x9bec91efa586b0f7cef8defbdb7aef4de7bc92692249bbc7786efdddbb7766eb49a484b9a4d24047f756e9dd0b0926ee7dcdb97726e3dc5b848f2c1dc1b7f6f6,0x8f71de39c6f8d716e33c638bf16e2a75b8a713469c4b88f10e1bc3f8770de19c2f85709e11c1f81f063adc1782703e05c078012724dbff7f6fd24ab1126924df,0x8586b0d61f42e82b0d1a740e7fcfb9ef3ce77ce894f39e71cdf9b735e69ccf99731e60a349472fe5ca9b96f2ce57cab94f28e4fc9b92f24e47c8b90f1de41c7f,0x5009f93e03dd37a674b27a4f09d93a11e243a57492284e49c13726c4d49a1332644c4980842604bc8009825c4009692ce91d1d4692be8dd17a2234255d0d61f0,0x3f66ecbd93b1f62ec3d83aff5eebbd73adf5aeb3d60a594a29246ca414728dd5fab11328bd57aa753ea5d47a8144286508a080cd8fb1b62ec422644888f4fe9c,0xf0de17c278351a550a99522a3e0bc0aa6f01dffbf77d51a540a7f63ef9defbd779ef1ddfbb75658a53bbaf74ee7dcbb8f7029bdbfb776ded9dafb514ced3da3b,0x8fd1799f43e7bd079ff3de74b6f9cf37e6bccf983ade5fcb716e31e57ca793f25e451a790f1fe3bc6f8cf17e2946f89eefe21469592b0974aba5d2acb1bc3955,0xf2e54dcb7de7bbf75ee78b717f71c54eb7b7f6ded7da7b3f65ec7d87aff4feb7d77adf4deb3d5f14e268d38d712e33c4788746f55ea7d47a7e25e9bd2fa43ade,0xb9f6fed23458df67ec7d751a569637d6faab196328dfa875be9a8d54df4be8a8d51bf40eb7cff9df37e67cbf95f27e47c7f8df17e27c3f85ccfe0fc0f7fefbde,0x8b291722c454061642c6588b09602be0688295e034574ae2c6fd7fa946fe951bfa3f3a8dfcdd03f2fa5fc8a3546a8dfc675bf17e2fc3f83ef95b51bf7beea8df,0x1b00c0140100400600800800fffffbfeffcff7febfcff82d5fdfc57eefec974b4a7efebfd3f9ff2fe3fc3f7feefdbfb163968d9bb3365ecad93b208c9182ce59,0xc01702c0540a16b0260480881001e03806f25e51c8f95f29e49c9f93722e8a033a223401602804808469c5003f40e268d390f1de3fcab8f71de41cfb8e7]]
def tokenGet (i : Nat) := (tokenKeyGet (tokenIdGet i) <<< 11) ||| tokenLowGet i

def paletteGet (i : Nat) := Ledger.packed 77 i #[
    #[0x50000000017000020800000000043d00298000000005100a0700000000000000015e00002010000008000298000000000800000016880000000010000002e00,0x55580000040010004403e0000000200080000014c0800200000000001008500012800082010005700000020000000000ab4400040000200000045020100010,0x24050020000020d50701844000000245c2b818001000800000084572400000c0000000061e0400008050080004016de90220800100010002e141011002200008,0x10a0214e808000210000004013fe0011040412008020dd400081600000003449a900000040000010028b1a08220800000000410ce000008843000200853b0,0x43c0ca08080800102002ab07020020000000005c511812201020100000659340800000000000004584000000001000110b00300008e00080006111d700002901,0x10402810a000100000000231c01011040000001017cc0400000010000022ec20241020000800115f038000090810408242ed100a088000000000,0x400012eb838000148002000004543c04038000000004888070000461008000005503800022000401008608a0000100002000084100e00000200020008aa2f502,0xc69600000410100008001af02044000002003112d2810020000400800eb80c08000000200000041868400840010000421e064200200000000014003800000000,0x282200040011ed01000300040000a1b80c00001a0040021005ff6040090001040141a80500001202090000002cf0000000000000000b620080451002008101,0x2023c8c0000000020000005382000000001000004026700000008a00040415e31000000010000000091800001000000000441800000000000000000002020,0xb5000000004000000009c500030200000001105220000000100000002300040015080400000509780400040010008803bc002001402010000015e48000010204,0x10020a001401de20100060304000000279c08000808200000449300400000401000000d95000000021000021424a108104000400000a105c0000088800001005,0x102258400000000000004116c000002804000008089ff000036020000401483680000000000000088b40000000a0400000047a4000028001000a0061c20000,0xec040004a480000800be400000400000008010e10100250004000008af2440401040420040413ee00080400000400008f800040602080014016c2800011000c0,0x208080054016c4000403850000000207fc00004018200008425e802000004100028001d700000100080000015e00104020084800a089b6008001800200100107,0x883e400000808e0010010b6e04000404100080222d202000602080054100eb80000911040100009668000004082009100579824008408200000209a700001],
    #[0x102208000804696030001001400020036940000c800200000053fe000004041004080219f020000040b0000015e9820001011480]]

def accountGet (i : Nat) := Ledger.packed 16 i #[
    #[0x1f001e001d001c001b001a0019001800170016001500140093001200110010000f000e000d000c000b000a0009000800070006000500040003000200010000,0x3307a9073206a30621003105a3053004a404260013002f002e002d002c002b002a00290028002700260025002403900023031002a3022201a2011000210020,0x16ae162315a31523149500301420139f132012ad123011b2113210a0102e0fae0f210e9f0e240dad0d230c900c230b920b300aa70a2409ad092d08ad0032082f,0x2283220321be21400040003f003e003d20a31a3c20341fbb1f211eba00391e341db81d371ca41c1f1bb31b271a9d1a341986192d18b6182d1793003517340534,0x2a8c00372a5129d22951005028a92829004f27cc004e273626a40046004d2646004c004b004a00490048004725c62543004524c4243623a9004300420041233d,0x399f393738bc383c37b22880375536c63656005535c63554349d340033c2330032a7324c318331033080302d2f832f1d2ed12e032d902d242c9e2c4a2bd32b46,0x49bc493c48bc483c47c6474c46cc464c45cc45364480440043bc432942c6424a41b4415240bc403c3fbc3f243e823e3c3db43d373cbc3c463bc63b573ad43a36,0x3b005a0038572756a7562755bc550a548a4903543c53bc5346490a52cc524c518a515950bc503c4fd84f3c4ebc4e3d4dbc4d3c4cb64c3c4b834b3c4aa94a37,0x63bc631a006462d4623961e3616260b460345fe15f555d835ee05e5f5dd25db65d335cb35c335c5a5c5b5ba85b5e5ac35a4459dd5950005c005b58bc580357c2,0x6f4e6ee85c686e676dcd6d665c496cc36c436bc46b5d6a836a6869bb694f00670066005200610065005168d8680367d8675466a766495d256585652864df6425,0x7cdc7c6e006e005d003c7bbc7b6d7ac37a3b79e879037883785177ed776676e6765a75c97560006c74ce741a73eb006a734d72e3724d7183716970d2705d6f83,0x809980297f997f4e600f7eef5e636cee7e6e7dee7d4e]]

def programKeyGet (i : Nat) := Ledger.packed 26 i #[
    #[0x6c03001bae40070f900000e00050a1001b96400003500000d000003600000cc00421980108650046410014184004219000008400002300000a00000370000000,0x3900110e4006212001b9e40066290000088006802001a04c007065001a994006415001196400701600000c4006216001c025006c5900000c800002500000e100,0x382c8600000367819894d4d31a001a9e4cc24153201968007018001901400703300141e4006a69801c164006879001c08c006413001900c00640900128650064,0xc82615]]
def programIdGet (i : Nat) := Ledger.packed 6 i #[
    #[0x144c14010001c14124402483c410410040f00b00e28618638920700d00c2080041002c6180289008000000205107180105144140100003002000001,0x1428001e00074a00000040058059670068001b6c00006990185d30132c000001000041000000001501500b00000000028000a0000160002d029500000a0000,0x35800685409c06a696501a0242838c042268000040000034068a29a58069a00000088a0000210200000000003000003000000142cb50a0402c07d000b40b01,0x290000514080282280edce91acc28ae78df6400acad742c3400bae433529580280cb1c0036f000b8b42daeb02b02cac0a80000010a405a9410000280596583,0x0]]
def programLowGet (i : Nat) := Ledger.packed 18 i #[
    #[0xce0026041ce6640db00850739b805d073b42ce32620d1ce34739c2033241a42ce86538c90290739a10310b390806002e6084e4200b084e6c611a08600252c84e,0xd2ce7040cb9886408cb9ceb2008d24e34538d44e2a538194ec6538d2ce4653a4bce6e21da90610b38194e6a40cca0232609b81b26420d34e34b3800cab202041,0x1da9026c809a8020020800840020fc805b4a230807f2014c18568295c18334539c107a8219c14eb4139080710b3b42ce34d38cc0632e18cb0632a1942ce92738,0xa400284e6a201b0006a005a8006640000938a13998806c009284e6c015980166001284e640059000065384ace12938cb4e0021800804a139b20770e0c00be6c8,0x400281a8112c000194e00259d34e1433ab2ce6ca12b1ce6c019c28270a01280170603284e70401b0068a139284e70001ba806e201b0070022ca9ce6a600a94e6,0x94e70013c8002a605b1876a60cd34e6c40da984d5338a98068411c10400255b1832c01598042a60519032600498002c13990042400598114a044284e0653800a,0x5c10170209c08110b39a0016e405a88104339a00564209908100207c8040a020190832411b0072ca11a90430809c2042a73ba9800027ec80624002c802640441,0x339a9010025d88020433999010433810ce72138194e72139880110738284e62015880000228008572139494e44339a88644219984e002f410ce0026800926622,0x46412c84e12339418372138d14e32539a8832a739a98524020a9ce0a138194e00318900062035514e52402c8ceb4139c181c4339c14e10b39880670005880704,0x4eb413954ce7021842ce70216d04e0a1399805b413800b664029980d70016498475138009c12201d1ce4653ac84e6a6059881b213990060653841ce0a13a284e,0x280457538a94e12216c80446405108326338984e70005194ef2005a9ce2a60198072a611280a34739284e641399008f2204904e002b9190b0653ac800b200190,0x1390832a431a900660314189f2200c8cef2139c0800653b984e0a139084eaa604a9046a53ad0012a60619032a615490372610d94e6413ad04e2601400b02a404,0xe201800b2f001400a5002d4009be60]]
def programGet (i : Nat) := (programKeyGet (programIdGet i) <<< 18) ||| programLowGet i

def csStartGet (i : Nat) := Ledger.packed 11 i #[
    #[0xd83a0700dc1a4338650c61842e0560a81482804e098128240460881082003e0780e81c0340640c01702904e0941182003c0680b8150220340580600800800000,0x8f41e23b8750e71c43786b8d51a2338660ca190318620c21702d85a0b21602b8560aa150298520a213e2744d09812c2504888e114220430831021f83e07a0f01,0x24638c59853045fcbd1782ec5ccb796b2d2590af95b2b2550a914f29a520a29432824f89d1352624b49592924e4889011b23245c8a91221a428831011fc3f07c,0x5142204368650aa1341e82d03a043fa7e0fa1f23dc7b0f51e83ca78cf09df3ba764eb9d23a072ce41c53846fcde1b93666c0d69a834c690d099f33a664cb9943,0xd45a4b41672cc592af95e2b956cad156aab550a955029e532a41452865029fd3ea7b4ee9d13826c4d299d32a614b89652b25149e931252484889051da364628b,0x4d5da9b5169ed35a534768ad0da0b3f678ce99c33165eca193324644c798e31a630c5589b0f61ac2181b015f6bdd7aaf35e2bbd762ea5d0b9970add5b6b656ba,0xf6beb7d0f91f13e07bcf6de9bce798f29e43c5784ef5dcbb776aec5d6bab750e99d1ba0738e61cab9071ae25c2b806fcde9bbb736e2dbdb53676c4d81af35c6b,0xf8f71e63b4748e11b634c668c917e2e4598ad1522944e89912a244448851021f43c8750d6194308590a21242083905a0941081701e02c037feff5fd3f67e4fc1,0x4728d517a2944687d0ca1341e82cff9f53d6794f09db3ae74ce79cb3826f4dc9b5352694d099d32a644c69832fa5ccb59632ae544a393d2624948d90d21240c7,0x9db1b5f6b6d55a8b4d692d159db37662c9d89b0f616c1d7eaf95deba56fad359ab055caad54ea8d4fa9b52ea3543a834fe9d537a694ca9752ca5349691d21a3d,0x2ef5dcbb575ae95d0b8f712e15bfb7b6ded]]

def csItemKeyGet (i : Nat) := Ledger.packed 16 i #[
    #[0x2315201157a007a0022029b429741003b441b2802001231102601024128426141124044618a45441230512240441214402412501042124b121b4241121140000,0x805123b030b3263252602674215020b62952280023b1231040016900610017248001422434432b941063895864226442402522452105b221295020b103600025,0x126628a71491685063b058605360206761507233367358a0467405216022623530655521302540240a91b42120620442b26004920491549120522057631083b0,0x1563006947642477b30855392235048128010a2100824284233523b7224401421533502728572a4448842345274412630443026929b120a70022824b23010221,0x214526771581152170871281144171471a412a770a8851193425b02712218532a108386543b10a410113514704792532042254274864426427744724b1082867,0xb721097307a9b34144776245830148a42635853b436503597563710357215421453262444a2407a82562047383114062195340846144406401b3b24167744311,0x5220b48183b1210047a42330403271142032672265222362026670242802237703762110190302260143033602368774a539823582453225806285626482b521,0x631517601360106514201220150323b420b755870a225109019352265442722401b8853807210b91bb9147a0297005226300400234426632426531050a811633,0x2802914200212644263230003662306601331b6024617a4122569b089b140112194264421b08110831017a02b10b31b40631480128050873016186000b91260,0xb22616032a940346049356390566b368608200880526296221060a8063050520633505364065431410640860830830066042024027b48300b7a080b108808100,0x800861226a42041310840780b7a823146802831bb068b0080265b49112652615462500594085472500850065708480684425463543050645b220266226456492,0x4632211643020642425525522502078b279426b4064345623a421233342230226635]]
def csItemIdGet (i : Nat) := Ledger.packed 9 i #[
    #[0x8040042a090a0242a050b0201205040540e08098502608048481c0b058442008078381e0e0582c1a0204004120c0200c100b050240a060401c0c050200c0401,0x6013178945c26168b0562a148a04c27130942a240188c441c0a88436200f804021e0e820200f04070101b0d060321805860101104034100a04060100e008542e,0x2c94490a11428052481490050a11c7c03230f07c45220f806432104c823a1f074803f0e80c763e1d8507a031e0ec74391c0dc6c1b1a84c5e011a04c6601190c4,0x599c5c26248a4d66a349a0ce2b330d40a4a12194c80531988c26024948925f24914625e1f174b85b2a168b2582b908763a2b154a85313948a21b2813c9c4d261,0x937a04f88141204da7a3c9b500663d9fcfc7d3e1ecf4793c190ee3c309d8c0053a9d0e66f0298ce409029c4de700298cde6e301b45c691319c5c26148b84c6c1,0xa91481e51e8d470311a8c382204c8b4501d124c028b8e6783aa20c249029801205260200e4c040240a88040250e8641160c082399ecd885349bcf685421f1066,0x542090a05d4aa451a886a0945851420950271324d4fa453c9d26a71369a3e13c289948934289948935228249934f8264c25d2c9515209264d13250f88249a489,0xaa89283552ad06aa1e014c637419215283349c5087c0420c12a8418242883049301007361bd068841825403c460a54e172513010a63c0240a144422d04692c20,0x3b1840ab5362b168b3590d4c2052620c184c41821066f581301835421f0f6b124ac092904189890af419c490ae242b5264f4489956ac250e848355520d54a941,0x241a99c2e4a51130106c39820dec05bafcf4642f1a44c2e5f2f456670b929784c040f116bb42290f6493b2e85c4914931060804ae508a641a0c10b85b9e56c77,0x944c3d1e50e5e02b2428c85329906c76301492c517178922928024924e0612510263c924907c3c948c6c45220d067c3d1e40ac36117982c00b928484d4f92810,0x39387c3d1e5007a3c814c0586632c10671e014c02e13334d0695f33056671709892693419c5c2c1319c940812124ce6129091966164a109861029b0e62e361cd,0x79c490db46b6946836bb5d18d941b6106376ba2c6e8b28b30de8b5082492d66aa10bcab14b51a6cc2892428c90298d100c41925a48368aada0cf41925549e4e3,0x740990bce82104dce31732bdca8338898ce76290240a14720f0c2763038d5650713840a130a0b84c05318a5c0516f8a556a92282516a8549e1ba786f375b8055,0x6a337afc929f4c850ecf2248a492cc149bd7cb230bc49249459ede0ef061246809419a4e2ca421f0108539bb8f2e13b3b40a140a385508c46bb1d6ea26ba49a0,0x83f027e4043ef7803f1fef77f3f5f81f673e868087dbe868ce0700412701ba05ee0b7cbd1da053005106aa1b9f1f0f72c3d878f57a1f09a522392546f3379b0e],
    #[0x22150b87c2a1c3486bf5f50b864148b0b8542600f7803f03e34043f5f4348000490375023002091e1b5df0841920e03783821fafa834160903040f10e0781c0,0xe0063b1e18206402f3c47e3d1d8e21c2a608daae311a098d840cc8c0ae32cc31460a2ab8c1fc550f8545d1b160802195038abde28fd89c4a230a2f116208c1a,0x1a0084a3ec261b064a126008c441c92488061c08468241b6008c38208d00c441c918fa30031208a46409100c28d31f0e00acc3191c7c031146a42dc0d92a3412,0x961800c7140620a4cca4ab0d94650ca094ca587124048360b98cc04e843e4be352e96c86587195ca9be271386c4f2194a9e4d27941c4552793c9852180185421,0x795629412d4f6e33fa00cd3a9c9f904b571ce25a7f412d5c67b969fd00663da9cfcd66a8a4bcab9bb51993628b4d56d65589d3f35071a8ce291309ca3348d28d,0x209c92cc13b328d30a31828a3ca221d08cca194492d30bd088ef7075046242615005c26161a0cf3f248a67b0f15ced985e55cf8525e55924533d87cf2762b699,0xe188c1aa26a6b09834da1330534d130b04d4d611d182b35ad304c2e131245868338723ed555d2c5cab6ab8da8d555d285420a4c7c533755d201d460db9037474,0x91cac1008841950a174472db59a829321feaef5ab5542649098c857547384cf67f6b1ec5cd6363e4f953a507ea44000a66847ca8bf2a12d1353c4cc260cb56f4,0xcd1669e0ae767729050c15db2d92c762b0978461b954b84213b057d575eae9a05342661f2392bac1feb95bad56104b571ce29a7fac8a14c26412d5c67ba69fcf,0x4a992a0b806c296f66050376e1e5b50e6866355561ca5d4956e324bc44d5f09d824711b65ad5751a9508502ea6c944d6a439ecff696b179aaab3f06ad0d03fd9,0x66251780c50a692898502e92899ab4b419a4207c8e1c41c0809]]
def csItemGet (i : Nat) := csItemKeyGet (csItemIdGet i)

def starts : Array Nat := #[0,1,16,178,623,669,670,682,824,863,869,870,915,1554,1961,1988,1989,1990,2002,2120,2159,2160,2179,2486,2658,2659,2679,2955,3461,3587,3599,3602,3604,3605,3606,3615,3704,3755,3756,3757,3768,3873,3965,3968,3969,3985,4117,4260,4266,4267,4273,4312]

def programBase := 364

def colorBase := 712

def moreBase := 1189

def phaseBase := 1732

def corners (s : Nat) := let a := csStartGet s; (List.range' a (csStartGet (s+1)-a)).map csItemGet
def atLevel (h i : Nat) := tokenGet (starts[h]?.getD 0+i)

end Ledger

namespace PhaseRegistry
open Ledger (field)
def phaseCodeKeyGet (i : Nat) := Ledger.packed 19 i #[
    #[0x44a1709042118302210840060603e058781d0b8380a024360d066180b82c150502603848110001e1003c1c068300b050120801c0c0281003010020000000,0x700e000081b8a00001c6c1703c6a1a0b814198641b0c4600b0842f0d8000300005068b805168062c0ac00018a8290000002000030c0a0240a83427000020b098,0xf004238b8380808c02000100001e452206e43108580001c401f86e1701c820001a401fc123e0000c000161a1fc5e3e0f4001e0a800028683b000091d0840b1c8,0xd06461208c010034be2f1385d2e0b64a168182c9602b2b8ac551501c0294c0d290a202140002793803268984b0bc1000920401385248014941b07c4909022480,0x9199007f1ec083f0ec3c3e8f8331ecf43c9e077020ec301d4363a04c7309046721c4e0379b80b368d86b1a82a019a468000066700ccc2619464090c600130c40,0x6440f1344c90c143c00a7a2605c4b800961412a9424d1c49a48911d9202a23d1c468308c000288b0c51400022890b9107f21c764321480421062820842102047,0x42a0003024130000b96c080002ca80414e1f000152f298000514a782902a200660004c462e004ae518183614092062885050954205013e9e00d3a26270000493,0xae4015c16e082d8085a8b0b409166041196400ac4802a9607824d5e0003e202081a3b1685c55ab8ad560000f0001d00038ab0f82caa0001b000341a13c000caa,0x81a88134d4c69084a468910063419267a10ce66998c932d9427b24c83918e2c00d8c628b83162006c33082a60820c00317e2e0c57c5e8b8035e176062e81801,0x7a3add474ba0e7051cccd000220c394c5061c84b38c0c5e830e20b846e13800c6f8108f57802de2fc186eb70db6d1b2d8300243b2f8d7141a4d6000216a88400,0x7f9c800095fcfd3883e7e0981a7d9f4f93e0587b95ced7b056f5109e8663cc3179006f10d01824bbc00091e01f2d1de00046ee031da72179d869098d3760b6,0x42011c911000270d0fc370f899111908288000563f8525743c04872f90d062184842c2485120000981f094202a5284c4983a0ca63ba0a8240c86811490134a]]
def phaseCodeIdGet (i : Nat) := Ledger.packed 9 i #[
    #[0x1a0d00000190c05c0000000002c150a0340c10060502610058241a050602c1207050000012088400e0f07034180b0502006090181c04010401c0c050200c0401,0x5028140a042210f0240a27130944804118884221108840e211088040201008040051007c3c200f854381c0e0703c150e074361c0e070301a0d068341b0b86834,0x3c66391c0e070381c0d0681f1b8d86a14098d068341a0d06832190c86632190c86432148a462301789c5229148a4522e110345a2c15840122a148a05010140a0,0x290486432184c5c441e10c864321900804020100804021104803f1f8fc7e3f1f8fc7e3e1e8e8743a1d0445c3c1d0e8660c0582006391d80c723b1d0e870381c0,0x52a1546a5429860264402948a24d280a8184f270bc9e252708c0a4d15930544c260cc0c0424130964b2592c964b2592c94492391c08482391c8e472391c86462,0xa73390345a6e389b4d82c38028de0e06830dc6d361ac186a059a4d067330c0ca270a0ac12643198812612b80c045b3017cbc5d2e00c045b16168b2272c15cac3,0x5188b3fa150e7e26130368a439a4ce4c2622510870c2190a8441a0902800f860fe153f05cdc793e99cf87b0a9e8f2673c1c0de13181dcec6e399c84e75091d05,0x21106a05406102a75320106a55228d44a25123d1ea15027c109d4f1113a9c4da3d1e9828268300c4ca612e964aa51269248a41208f47a3d1e0f44a1d068e44a3,0x589e56479592c95cae58ab95cb00aab95c1e5599158ab0f1606c9e54878b0a956abd5cae56ab156645128944aa2c278a45155058b09e51288b0a90baa0308653,0xbe5eaed76bb5daed76bc5daed70175b2e572ba5cae572b9322e572b85badd6eb75badd6eb75a2d968155a2d02ab45a2d16ab459148185259ac964b058ac964b0,0x8ac562b158ac562b1588c454b1188c46231188c361b0d86c361b0d86c06030180c06030184c1602fd7ebf0d82d74bf5fafd7ebf5eaf57abd5c2e97abd5eaacc8,0x70b09e54b6db4a96db68b2ba65b2db2d831b5dacd56a34c321617b49a2ce6833d78584f338ae595c33594cc6493416cb65b2992bc4f3219055312d4360663b19,0x51a5e4f275b95e2e7292cd14aa779e42af077ac1dad24532d96b3772c5daec75ba9d2e858aadcee672ac4a4e67294596cb71b89c2dd6e391c6e270b81bede6eb,0xa84c220ebc8240e0e746f8560d057e3d1e90481a41e8f481405e81666c01fefe7ebf1e8f47dbb9b2fa733e5c0f87bacdecf57a3c9e4f279ac114b3793c9e41b4,0xe588f4755a045c472371a8cc622c798bbc22d1689ac22b0f8a43a271389c562913898586d1389b098312694461108844216079880c61f0e45422110886c32170,0x66933994ca653297cbe4d309349a6330294c25e529349a4cb03ccba5b2c454ae55299401a2527934980cd97cc96391b8b1aa2d1690c5a2d2491c89520390c823],
    #[0x26f40a02d45448a0d02813f9f1066942a0d02653f9f0a9273d7c371f13c9d8d89e5204cea71399c8da70f89acda6732994ca60109a4da693712944213611cd]]
def phaseCodeLowGet (i : Nat) := Ledger.packed 9 i #[
    #[0x570ff5f37e9b4b56b7276da7ed29dd2b9742a12eea74aa50cb55d2a530875b28d0294c1fe9f2b95a229f4ca5425d24c542b190ca449205acb57cae52e9651a49,0xb69b3385faf9fb4d65c2d10a9240a1924816a71369a6e2a6715f4f4f5389b7d57252de964a17d4967cf9ba5c7e525d6df964a932d85e53d3cfd4e372948b7d2e,0xa7d3158bb3d3e6311f5f4fe9b4f96b3e9f2d5e36cf5594c57dbc9daf531b75a4cae23e9e5fd3598ac56a72773a3cc6a124da64a1592b862aa113f5f2f25adc5d,0x2b87274f89d84ba1502b3d1e5705f2f2f538db4d266314c944fdbcfd6e36df539ac262992f4f2f5789e853a496fa6f4a9d2cb44228d24955a28d2f87fb79bab9,0x1088162a55d2c9742594e8540a8d46a74b28d68b45a28d8aa354249b4b8dc29325d86ba15248afcf9fadc9db6972984dd365ebe3cb28dabc5d9e8f2783fc7e5d,0x2d146c95c259469240a5568a3493a5b2b75328d04f943b194cb549a0902b442291b0b85a2d1089242a0d24a549a498a955a28d24944120508a340a8d4e817cad,0x5a2092eb64aa51e9e2d4a996aa440b4787d95ca1552875320d24814ba51b2b943a1508935b29108935425d8ca641a4908a340a218a816c255469241a09d2d964,0x9451a4990a84b295289341205468152e6309f3f16a532c851a112e8642a8d02d2e1e0d24f96cae10e844231548845a2494e8442ad74792c3625d2a65a3a512c6,0x109354e512987f97a330d9e3f29aeb3d16e10aa340a5972a874a610cba54a1d468a49e1368924bb15efe7e9fa570a74b249d4ca5caa18db9e4a5d68d85c25d2a,0x290ff7f374785b5d3f692385c2a8d52f3f4769afc2d9e976a98c1655e7e4eb71769a5cc607f3b972e19b3c6c3ae35196f4a1ff1a64429d04e5ebee50ec1db6e9,0xb793a7c5dae972f85f9fa32cd5e26cb4f9ac37e7d5d8e16db519ac2fe3cbd9e26d74d98f4ae50df7f376774a7653176daacb627f3e3eb7132cc95be9b2986522,0x55ba992ab451a998ab4492e565a4c32d1489340aa10a9274b25468642a8d26814cb216e9451a0908a84b20d689342a4b078551b252ca35a24902f96cbe1d2c97,0xcb44960f4c965aa4d8ca449b6572965aa099299632d924f3f0e6510965aa4d04864a20d2ec64a28d24a7432d146826c70f688451ad108a362a5568d9642998a8,0x10c84ec3212ab46cb2570955a2056af3f26998a9568f17d2a35a76570a75321146c552e4fb2a85aa0d248164ad908936c2e109f6f0f5f72894324987b5d26e56,0x25d268349255288240a1146a353e996a934c627e7e96cae54a8272f5b85e95b2cb47b86ba5709d8542952a837c7a3a5c6eca9526e964a4d04b2d264f08d954ba,0x5328d71a6cc6172e9879ee5c5d3daae90eca5425d89b3d37618aa4492d50aa341a9d2ec64a2092784f3a59469249a49e5967174f04c3da7e5b28953a9906a349],
    #[0x230f69e863ad124a2c9fa1b0b74aa8d0285fa7e5d2c862a092c955325524d85b25508834920524e851a5524b54938ba9c3e42dd0ab44325568a36431568a3]]
def phaseCodeGet (i : Nat) := (phaseCodeKeyGet (phaseCodeIdGet i) <<< 9) ||| phaseCodeLowGet i

def tripleGet (i : Nat) := Ledger.packed 27 i #[
    #[0x28048a4d26a34048141a068540a10040602c1a090240a0d12a140a80102804ca2112040a8541a89042402894161a050500a15058341204010182a160a0080203,0x5188440b24824c2e270238980c200088445669148108a448211289c1c060493090440011084a8502a0040a00a6120980082403a990ca020984c0e83012402894,0x26230132d148a61a090460281c0d8743230088c436590c82a0d02828241a162a050080203229058ac1205068ac5a2824110984a2612410492480906830205429,0x28502b1080c4516aa45028120b4a261208342a04743619090502c820924183c2e0440011098a442282112898082610c262301a8d868140905858a81411028544,0xa349a0944c240140406148e051068540a482c12026030981406061a0b048080806134aa452a114aa4922934964d24954ac540b05428010100c28120b068160a0,0x43a1902201085120d0401100852432590341609010100c389008048321b0d46c24020482d048945a030088a4d64920a85808050205522b0480302a0504014186,0x4120c30d148a2992090480510e270b81028241a130d048482210c46a110351e0d010008462b548a10004422516090150601446a21141a8b05422810009028326,0x948a0a8840210a250288000a051098440500a1528180800d0a01540b05004002110898404562d04300c8e408000601b0904a616090198e865348ac500a241081,0x542079341a0b9542a5562914090502e0d44821328a4581c8a040b848253094480900a06361a8d0221201a29128b40621111d0586424110188f4522e13118028,0x1a81452051601c8a0406854080902034080203163a0d0293c1a0940c2420d548a01868140405018140101e0f838102a050b00114807530194001508556211502,0xb050c461703081482449049245a2b14a29308a0980c22030281e171181058301214010586c3a110a040381a0886c3a910886ca21124d44820b068040a0106a2d,0x820021a080490040622d540a45868140a44a2d548b4502450290b45629018100d0785c0c12040614c20130004c20432412456611435184d02592092020984148,0x241a010181c12010680c020628180e068321b086120914024429a5924b0b83c082414030c424110108444854120404050392e160b091482628349a0e0522888c,0xa1d1368a4514024186a261a0480906058743214090180512032020901c081203c2a0f03150b452050101862a01080002814181c0404002112c1a090a95829008,0x200088d46c3461311811184c040c1a010d44c2448a81001503010642]]

def obsGet (i : Nat) := Ledger.packed 18 i #[
    #[0x9018041a05088041a09048340a15120942a05420102a140a0550a05040602018804203008402807030180e110a802834140b05828241a010180a0703814100c,0x40341a040c02018084c22110980a2504423090482611118802a150285030144a241d0c80221048a4643a1108c1804120b0542b158aa01201609130905020016,0x2844623098042207030201404d249249a152a8241309848141a0d029228140a4464b20482e0309008442c1209059048341a0844a21148b0b0582e1583c10080c,0xd04850a84c2224904341a85c2a82c1c52280c040834112814502c1188a070180c0c150a1b0ca090c86410894401108c24120984080c45a244c2406020d468070,0x38945a0b158141a0f058140f0b81261104201102812098124914020840230385140e0e470381c8d2682100914aa190d8543a540a0d24922994b05028160144a0,0x422428050c024a0500a21108140a0c120844224120a4502922d162301a2914a24120944245286c161301124821100900922b050b0522b14c46020d0281c0b058,0x980e0301887028482c0a45028148944824128940aa24122915a2c1418094130a410004830180514826050a02018140e030110a8145a2a03111a4c0e078030914,0xda05225120a80405422194c862b060b4580d04a8552a9520944205008042211020508249a408840a250c4604128832091e0d0683c0e050281c04864f070151a,0x108124b309a01309321941203048846c344d20806094a241209400060041a8144e27028a45a0516240300d04c120c08150a81321911a4d24824321b20d041a,0x8241826020104e011180460582840210443a261a224168080c070110084104a]]

def edgeGet (i : Nat) := Ledger.packed 22 i #[
    #[0xd44c21512855024242118894420941007dc3c1d5038714361a10c86182e1430b04582a1420984a4221020783981a0c505829c120850381900a04101808c02002,0xa60482102c115168b242e1120884042a1410b8ac8361800587d8460840f8a902a2911407d8462740c86140a043140a5c4c274038710361a00b8508501f71189,0x309d42e0140085c870181219098821641690247e3e11e8f28763a9160050723821a8d845a3790d840806024008b086c35403060450347198c906230a178ba416,0x8ae563229548a85382902c4a25071693e49c4d5038194361a22512d8361921c0e44021a2219318964a10c86d8724921f12248e466021154384420201540c4411,0x911e98e8c868219095870671119990686530283446264a319888866161a06506260a2f979430064029544422612e9720b65470e0608b45642c09085a5992c04c,0x8900321b51c924408053031100643373609d0e47683a951cba748399c946a711381be428106219314d42310703d00a0e1121b9066023369b087a6ba119a90966,0xa1e9421c150630a41206500014020150fe7e53e9e08084542b0248e47c71a9ec44e566369e88642970d19d4641f71219d4f06161980902c796309e104677509,0x4823c91c880458088028011c9c49008a4328d051a8c4459ad1148021a1951128812821e0e27b51f0fe4021022292481c5751c0644867160703d4506c70c2191,0x6d02c93545a48d1e9010b1e542c8d5309e0d1480145808d008a31c8e04ca34044a2005e9181204d0864c4259280ac0913f9f90fa7811a9c40084531c9c44960f,0xc3f80904c42c93445a4891e900198ca8ce1453c18513e9e90a2750ba9c74da691169964c240d2e96934a54d16946462350642950d19cc944b41c0e40361910c8,0x561589560a11c8f8954020548e0c6aa812512d47039312a8cd446625184094e1205307d848a540b0451462b30d86400805203290456a3151158142a030283487,0x49248d0002c4d66b222d01500c0712e9d1c1c0543e1c84ba7c7029ec458b130e15c81a5755806507caf945a515188d34ba7a15cad31c9250321b32512cc6a490,0xbe20aadd16e1415ea49d78bb45b804436ba0432d9948b535b8405481c40dad850cba75b99c96e0120dae85725185c1edd6e102432d9d48b542d070c8ab410b85,0xb144be9245e264016c463fb0d41ec256092841cc045f81041e0e5068310e6724588a842a0100884002a14026abe140a425b040c5a2c8432e996e671391f200a,0x594c9567168050cd76609d472221109b4086cb565324c2e0130d8608a8c885631d50c1870b99cd622a20a80442e153492344b41c50d8908ba51863151c8a2221,0x135e27c41e61658064da448923b458301c35f8d08940465a12504c214328a4578bb01189ccb41c45e2ec4ba51763151816d0662b3c8221610a05412612208804],
    #[0x9850581432eb5a1aa5023c18548ed151507c4940456a124d9e2960984a168453229241a65672281004c7a30792d898c92088415585652c07c968495342228581,0xc6291018488222c0710a5c9ee15341929aae021385586ad616f37c90ade9578f85b6dd86d3705ac352093544f4656088b0430b536db6a1b2d816ba3e8fe09514,0x42281046612272958c4c084022fd1800d12d1a8d400700c95d4001422d05d458243120494221a105b11cfec3606955100e433222087caf821a4d5c67810f9611,0xac5d401458ba456eb160c86c18e7c70329094c29538a94c94c146b1245481c251a80c0a8900aadcd108e26aa9056cb10428fe1d03b12b870dce9221539801c1c,0xe1325b850832ba0699599ecb51198a8886f547a0588b01f179b0117ef2231bc4de0ef20b851118ee10d844424b10062215da1420d89043aec5762d8148df2443,0x1636117a800393f5c0abe35b84c5f88894020c5f65637d2d0168b645b1241f215614b8916eb12018a882a17036898592f85719285684545bba89ee854690b216,0x18cc3230b3d160e14302ad0000012012c840e0630289816eb1475004c050613941592504138c0d2049620dc04854b118001480cfe100360d7ab207f814c0cfe2,0x7843482d07159c30a1602101858c28b20799a95400720005102d070574289129e002c240000135001c4341041442]]

def cycleStartGet (i : Nat) := Ledger.packed 10 i #[
    #[0x46b1a0661906217c5c1685815854148501344b12447114431003e0f03a0e0360d0320bc2d0ac2909c2508c2107c1d06c1905c14048100380c028080180400800,0xa35cd534cd133ccc328c7314c3304bf2f4bb2e4b72d4b32c4af2b4ab2a0a6290a22809e2709a2609624c902388c22888218832047f1f47b1e4771d4731c46f1b,0x1d45509404f93b4e5374d5334c52f4b52b4a1264912247d1d46d1945d1544d104390c4290841904404ff3f4fb3e4f73d4f33c0ee3b0ea3a0e6390e2380de370d,0xb06b9ac6a9a8699a4689a06799c6699865994649906398c6298861984609805f97c5e9785d9745c56f5b16a5a1665916157d5d56d5955d5554d5153d4d52d495,0x8821e8721a86216852128420e8320a82206812017fdfd7edf97ddf57cdf07b5ea79de5789e0779db765d7755d3745cf735ca71dc570dc16fdbc6e9b86d9b46c9,0xe89a1e85a0e819fe7d9ee799de759ce719be6d9ae6999e6598e6097a5c96a5895a549464f9364b92647916439063f8f63b8e6368d2328c22e8b22a8a22689222,0xa829ea729aa6296a5292a428ea2]]

def cycleItemGet (i : Nat) := Ledger.packed 10 i #[
    #[0x280ac2a0a40b0a027098180802509023088210801f064030781d0701b0680d0641805c160541404c120441003c0e0340c02c0a0240801c060140400c0200400,0x61540203c5414c51148471445013c4e1344c12c4a1244811c46074451103a0e43610c34108411003f0f83d0f03b0e8390e0370d8350d0330c8310c02f0b82d0b,0x1c801fc7e1f47c1ec711e8791e0771d8721d4741cc721c4701bc6e1b46c1ac6a1a46819c661945519063188441840f1406017c5e174381745c16c5a1645815c5,0xaa134a9074a82144f29ca6294a428ca2284a027c9e1849d2007d1389c26c9a2649825c962549424c922449023c522388d2308b22889220872188521083208811,0x224d0148cf338cd32ccc32c78328c92d8c831cc61b8c5310c3308c12f0c02fcbe220bd2f0bb1f4ba2e4b82dcb6124b52d03a2cc902c8b12c0af2b8ad2b0ab144,0x901400ff3f8fd3f0fb3e8f93e0d23dcf63d4f43ccf23c4f03bcee3b4ec3acea3a4e839ce6348e5390e3388e1380df378dd370db368d9360d7358d5350d3348d1,0xe4bd2e0b12d4b12b4a9294a1274982b4952448d224852047d1e4742b4711b46919461174591545113449114410f4390d4310b01d0a4250839d07419054110340,0x595555153549515414f5394d5314b5294952147519454306151143509415013f4f93d4f13b2093a4e538025370b1360ac2a4dc0b4d9354d1334c9254c5302612,0x6c6017f5f97d5f17b5e8095e5785dd6c5d9755d1735c9715c16f024295b96d5b16b5a9694ad6808567599184ad6559163589615815f5795d5715b56959561575,0x69da639da5691a3689a16819f6799d6719b669996619465d75531736594c6559464d926459063d8e635736318b62989621875c5706196a6158460d825f1814dd,0x1cf7391f225cd7312e221cb729c9721c771923715c470dc2705c06fdbe6f45b6f1bb6e9b96e1a06dd18609b66d5b46cdb26c5b06bdae6b5ac6adaa4f1a95c5a8,0xa7e5f87dd847d9f57d1f37c91f7c5f0465ef7b9ed7b1a24c9eb7a9e97a1e7799e5791e3681e2785b7781df779dd771db769d9761d775966755d474dd270dd174,0x8e228862087e1e8761c00e1b86a114d619862178593539e158521084e128461083e0e47e0d8320b4b94c82a098220781a058120380a01801ff7f9fd7f1e97edf,0x7762787e26896248]]

def cluesStartGet (i : Nat) := Ledger.packed 12 i #[
    #[0x5814d14713912e12811e11811210c1060fa0f40e70e10db0d50cf0ca0c30bd0b70ac09f09708f08507b07006605d05304a04103802f02501d01501000b006000,0x829328e28928227d27827326b26325a25525024723f23723222d22522021b21621120c2041ff1f91f31ec1e31d41cb1bf1b61aa19c18d18717f17817316e1601,0x3b83b33aa3a539b39639138a38437e37937136c36235b35434a34233b33532e32531d31731230a3022fd2f42eb2e62e12d92cf2ca2c52bb2b62b12a82a329d29,0x2551c51250b5024f94ef4e44dc4d34cc4c34ba4b14a849f49748d48547d47346c46445b45344a44143842f42541e41740e4043fc3f33ec3e53de3d63ce3c93c1,0xf69869068667f67766f66766265d65464f64763f63662e62461b6116095ff5f85e85e05d55cb5c15b75ab5a259958f58657f57656d56255855054753f53652e5,0x7cb7c47ba7b17a97a379c79278978177977476c76275d75875374e74773f73773272d72872071570e7057006fb6f66ef6e86df6d86d06c76c26bb6b36ac6a469,0x219199129099058ff8f68f18e78dd8d38cc8c78c28bb8b58ac8a78a289d89688e88487a87086985f85984e84783e83482a82181c8128087fe7f57ee7e57dc7d5,0x9a54a4fa46a3ca33a2aa25a1da18a0fa0aa029fd9f59ec9e49dc9d79d29cd9c59bc9b79af9aa9a299b99698c98497f97796f96796095895194a94393a9309289,0xa5]]

def cluesItemGet (i : Nat) := Ledger.packed 10 i #[
    #[0xc1e0741c06c1a0641801416044100301503c1804817058110301503c1404c12014110400c03c0e0340a024080300b028090200700806004000140400c0200400,0xb0c43a050340b4050b0070c8390e0370d835050340cc070c8310c02f0b81404c2d0142c0ac2a0a42809c230881c06c26084250901f08c220701b04c210142007,0x380e0ec5010c1413c411380e0ec4d1304b1281404c49014480ec3e10047108460ac450a40e0ec401103e10c4205026104250383b1003f0f83d050130f0050303,0xa19865094201900e0286318813048050800c028340b40515007174611805f17837050340cc5401c5d1705b168591605715855050130b4051505014c52144291,0x1d418014741a85d0606b05c741a85d1cc721c4701bc6e1b46c050131ac051a8130cc05010070182b144291a40e05426104250100e05413124050100c1a00e19c,0xc8a050892208704c6b014541a8862148420c82204140d0172007f04c7e0147d1747c04c1201416030150ac7b0a47a1e4150ac2a0a4780881c184771d86017c5e,0x22acaa2a43301ca829ca6050910841f0881b294a428c6e288a1050a027c9e2749c0cc9b150071749a2649825c962549424c92050911041103c9023c8e2348c22,0x2c59328c9320c7238c6314c42800530c9c1ac0515007174c2304c02fcbe2f40e2f0bb2e8b90a4b82dc0f2d8b52d0b30200e2c8b12c0001b8af2b8ad1ccac1c4a,0xec000eb3a8e93a0e7398e5390e33880e2c4da384e037cde374dc2d8db368d9360a735cd62e42909c230881b3546c0e8a2350c734cd2344d033cce01ca8334cc3,0x2941464035040209c40c051d06a174ef40829404ed2c800400ff3f8fd3f0b62d4fb020fa3e4f83dcf63d4f43ccf2384d9368f13c0b63bcee2e4293b40e2c8,0xc00038b2424ec000fd4390d3f10b2d4660200e2c909420002d8b5430b30210b2d4b418c08038b2428b00000e2c909418000a5012e0ed41cb24200041cb22c506,0x52d0094791d45d012e0ed038b2424004711b43063469194610a4187f45d16454b84500e2c909000fd44d0d448b62d504444291a4b83b40e2c9100000e2c8b143,0xc12f0392e0552d4b12b4a9294a1272d92607125490291a4b83b4b2004001a12348800484792c868004000880d48009020fd47d0d4491c2d409444de41427370b,0x1c18c621e518055061fcee3bce30a4b83b4792c8ec0013a4e4b42cc621e40d4e009021374d8fd434fc4d4b53ec084d4b52d0b302119461344cd084c8b24c4014,0x5640056157558be555461754c55153521520a5512e1500552303c1548d4f5394d1754c52d4a5254851c29519451f14450d420a829505404fd3e4f53c4ed3546c,0x9715c0b65bd6e509481142909d6d5b16b5a8295a56859d664f965591074613458d084c81548d6203d611e9602f55f2c5061fd5e575512e15c0552356d5a088b2],
    #[0x345992039916411663d8e0398d6317e5c98b629892d98861d865097e6154161183609816017f5097e5f4275f1645097b5e9795e1775d9425c9752d974431735c,0xc8b12c0002d8b52d1a7479a6695a468da06894a01c026819f6840001c026819f678006759a5899c5855d5459b570156695b568066654f5394d66197659956519,0x236ec0f6e82b458292e0ed1e4b2001b96e1b76d9b56d1b36c9b12d9b0070631882b5c829415af6b9ad6b1ab4d4b548009021aa6a59469952045a3031a803c792,0x7404e2c92f73dce050130b405735cc00852144693b40e2c81504c490140400c0272dca725c871dc6715c470dc2705c06fdbe6f5bc0a4692e0ed464b200400055,0x1cc009df4bde17801406049745d0009df4bc1312405745cc009df05034015d0775087784c0e8140d02d015dd01ddc76dda765d80a5d7759d52c9d4051d3749d1,0x57cd6c7c9f17c0fd7bcb67b8667b45014c52144297b00e4d0527ac297a9af79c0d78d1e13de67a5e57a1e7035e347813798057941f7900b78d1e78818015d174,0x21fe81e0681602804528102980d677fa028041413e007fd677f9fd7d41404df4015f37f1fb7e5f57e8140d0057ddf35b1f97e0140d1f47dd6c7d9f5050137d00,0xcb85453148510a5af8500e0ee138484a05013124058443b8420f8060e8342959e0a7fa02830468102980e0a7fa0780a0b052007a5ff829fe81c1404e00016098,0x504f749d17404e881ce87c1404c2d01616730024be1587a1d14e1c86dd80a5af8511986a198601474c417a21484a170bc2e050130b4058441312405859cc009,0x2d0144801c320bc2e8981404c2d014111204a89e2605034015d0121cb896240502d015dd01e23421de8622205013015e8846120e8140d02d0161101c328861a,0x15d0120328be2e0504f799e57a2148b62c04c490162b7900b0ed1e0ea27899e206005740480ca2a8a4140606b740880c84c0e81404e28014481a8321303a0d,0xee158f6188f0527ac296be148b23b7c4510a63a03a39199ed89a228e0a0015d01204c0ea38272280144801c321423789a368d4520a5d613a348ce328c41404e3,0xc0ee488a44c90e47050898a005122260e81404e28014111206a0ca469164490e4290640050340f0048fe1810c46149160a5af8503b854531182b8f8298500e0,0xca6391e620509c8a1d09866097e5e9765c96e5a9665895e5695414010b29525385652946500a61493e4e9364c0501392c057ce4a81e181281404e490141f844,0x4297a9e78b5e39b43a9b04c9ac9c01411120079aa699a20d1142975e678821810c1413c497a5e88515f0ee66996640502003409022260e8142806b279d012088,0xf2c90a41a782d8b5070fb9de1514c3c148510a6140383b038b2054ec4c84c0ea769d674120070c85010e739c8291380e0ee719c2150ac7b0a427851079be6e83],
    #[0x8083f5139ee81470b519911a027f509724167e2d67d18d1a0a469758ed2c908751489f0291a4ed77dd4484fd44e7b3f0b59e866444291a5d63b4b29e5087515,0x852c8b141a844bd192c8b14192f45d1645469450b2a0cde414dd370b59f5a7020291a4ed464b244000509161a4bd2ca8343c00470b52d063478291a4644640da,0x57cb2429064bc792c8683b1320a4693b5192c8010002975e92a4690a3e8e5228d0a68ca2e0aa2a89a20fd47e81472874100845c450a4693b5192c9d465116a1a,0xd1a1e40d1a12d021352d5203ee775cea04167e4d4b5480b3a7e9e50a942fa9d4669ca6e9aa6429a61af8ea97a59ed8544350a95a50298e80e4d13a2d69318d1e,0x91a4ed2c9d4adeb6ad52f486b4aceb24bd21ac6b0abe89a84222c92049524522aeab6acaaeaaa20fdaa6a8a9ea6a952f48429a328ba92a3a8a89a853aa1cb42c,0x32cb3f6cab26c8afec750a952fac3b1ac5b02c4afd42a5429b0ec2b06c0afd42a5429afabdaf2bbae8b62d41c024080ad720a5051900d6b111ae6b81182b1142,0xe3ba17ebaeea6bee960ee8b9ee6b95425fae4b0ee35f2e2b86e0509afb7edeb76dc44542522d20a6beb6edab66d8b5e03b5ad5b5148b4ed20a6d1b42cfb3acdb,0x199ed651a6c1303c09a3c0700bfd4855aadab2fe66688bf6fcbeefa3f6f9be2f7bd942522f50a427bd16cbcef2bc6f0b2cfdb2ac9b1eefbbaedbb1425fa046be,0x31ac67183f6a8c5f1666aa5c5714c4dd6c4b1166ab5c430f666b24bd21c3b0d50a950a68bc330bc2aa2c270850b070a6986be14a5f067c70550a940a63a03a39,0x250948458286b46346b32cc4fdcc32fcbb2dcb32bca942523290a6d0ca327c9b25ba82959f24c8f22c8720509720a31f2d063c7b1dc71d6c6d194d133421328d,0x50792c8687e74950b42b0f48d1f46d1744d0d42d0b41d02d6cff3ecf73cced42ceb25baac3ce723ce337cdb359edef4e9ee024080ac511e8641e5ad05734ccf2,0x1101c0201b56d54b64981cd3b4d3f7543f287d4f52d44fd47f50d3f4ed3542458692e1d52c8b1004004e8b5a4c634690ad334b4bd214e8b5d28634782b144694,0xdb36bda845da76803a9cd9f660392e05765d936310c460ad160a4b8d887972f61d835cd6a7475dcc009dfd7f5ed775cd6f5a9d28cd6758d5c29415af1900d199,0x781d291104f80015e507f7f8b11101416df77c72d0875018df8170581172d067501404f7e0177ddf1d4def7abb779de27bddf76dd774dcf72dc770dbf6edb766,0x9e220d0a47a99e2004f800142407f7f8b1110a428e1ebd8b066444250901faf62c18d1101420e1b7f8b00944783e17840a42809ebd7b911e0f82085e90901faf,0xa801e754de739be6b993f79843797e5911521560a5d709f950c911e4394e4f9252557558bee4546e438fe39485582951b8daab8c50f8be2a0d0a501755cb3b38],
    #[0x291e9d63b4792cba177973a8105b0e7e4d4b5a4cb31e5180550fe8c52147a2afa851e4b2e84792ca793b1de508511a6be1e4b2428b03787a2e3a0e5906e7f9ea,0x706606d5d544b8eb01548f4beafaa404b8ea7a8e9d06e9a783782809cdc4d41c18c620ac51454b8450792c8000880d070090213546c1ce97a44d4b59e8fb7b4,0x148bd4291e8b8ebf96acdd4e5ab3421d4584de1e8b8e8396acd06e7f96acc01e754d55d562fb9151b90ebb8fe3b90ebb93e4949522ae0a546eb6aae31434d51b,0x19df150875161e599a421d4edfc4f0fc2f078dec70af03bfefbbdef3bb3f7baee59aee3b7edbb5ed3b3ecb8dec599ec]]

def step (i : Nat) :=
  let w := edgeGet i
  (w &&& 15) ||| (obsGet ((w>>>4) &&& 511) <<< 4) ||| (obsGet (w>>>13) <<< 22)

def clue (i : Nat) : Nat × List Nat :=
  let w := phaseCodeGet i
  let kind := w &&& 3
  if kind=1 then
    ((w &&& 1023) ||| (tripleGet ((w>>>10) &&& 511) <<< 10) ||| (tripleGet (w>>>19) <<< 37),[])
  else if kind=2 then
    ((w &&& 63) ||| (obsGet ((w>>>6) &&& 511) <<< 6) ||| (obsGet (w>>>15) <<< 24),[])
  else if kind=3 then
    let s := w>>>6
    let a := cycleStartGet s
    (w &&& 63,(List.range' a (cycleStartGet (s+1)-a)).map fun j => step (cycleItemGet j))
  else (w,[])

def hints (i : Nat) : List (Nat × List Nat) :=
  let a := cluesStartGet i
  (List.range' a (cluesStartGet (i+1)-a)).map fun p => clue (cluesItemGet p)
end PhaseRegistry

namespace More
open Ledger (field)
def selectorGet (i : Nat) := Ledger.packed 24 i #[
    #[0x32643210a74321a84310a95432a86510a86531987210a86541876210a76510a85321654210a85432a85410865210a76210986210a87610976510a86540a87640,0x3210986521984321975430975420974321743210976541543210976540865410754210965410975421865431a76541a96541654310a74310a76540a976329754,0xa96530a96520a9654086543098651075432086431098431085432097641097531097653097654397432095321096543096531098543095432097431086432196,0x10843210a64320a63210a64310965321a43210a54310985321a97321a96532a53210a76321a97620987642a97642a96543986321854210a65210a65321a54320,0x7621a96432763210a98321873210a73210875432875420985432a85431a97631965320965431a54321a54210965420854321a74210a96320a96321865321a853,0xa74320a64321954310a84321a97532986320a87510a96521a98632a96430a98521a85420a85421976210986530a65430854310a86530a97610a85430a95321a9,0x10a75410a98710976310853210987321987421986430876420985410964210874321964320876421943210874210753210985210976321a95430a94320a75431,0x8753987621a87621a98621a98721a86410954210875210764310865310a76530863210a87321a86210a86321a86310a98610a87530986310a76310a874209876,0x987431a87431a98431a86431976431a87642864320a97530a97540986540a97640a98731765430a75430a65431a98742a87641a76531986543a86543a97643a9,0x30a87631a98620a98720a98741976430986532976420954321974210973210987530975320876521976521987631a87620975431a95410a98643a98732a76431,0xa86521a87632975410875430987632876520976520865320876310a98752a87650a98642976531a98743a87540a65310765410a864209876209876]]

def headerGet (i : Nat) := Ledger.packed 15 i #[
    #[0x8b01441da42d087160db61a7433106160bf216242ae8509098a0b782448478083e0f501c18354060a0b24155824f019208780fb818502a804140658083008600,0x13c04b0d10199e02ac48f0c89166e1f144158c5618442f6c5de0b6b120a02dc3f18b0915bc2ae45248a0313be26dc3e48955122023ac448084b103c13303e587,0x7c206224ec27c84461f9c3e587bf0eeb18a03c7854f0abe1dfa02847510e561852295860d8b850f4638787128de51bf0362457b8d7d016e350c4f5889f112c2,0x31eca7312bb297c511ca03904720f64f409c8138d16aa4a649b8892926744ca862512e6257649a0909119223e046b82e0919722d622a488c8a4c21f840a08439,0x96a51bf84098ba7971a08ca2d84b75114d184a37946f396a32c92132823916061fd257048d78abaab2224f4aa38c6618a22444a8a952b188e4a549f213d3272a,0xe37e422c961722b26a28d35096a12cc2444d18995133a266c4cb6192c31f008181ff988a040c612896018061ece5a946f28b692bb85894bfa0fe92bc25b9cbd3,0x91d5f3a647350e431c45058a0b40e1b9bce1f686ea0db41b4e1f2e6258d9790192bae6964883925a262e166414c9af230e83f187a51a4a34ec5d404691192234,0xa64e5cc4e02bc207840f081d9fc93f6224c448d94e20c5c7d7830d0a3a0994116c8151f0a3112135cf65044a08e40ac8af91e872928795cf0c1df536ea6ad0ec,0x55216d149843303eda06736181f3086587a942324db09bf989141a244c4a43203c20624ff081e101b41264f5900b1c3129368119016135905140a4cfa813af27,0x68093f524ba2bf457691ad22fa41247f887191dea34e46568bfd1520aa343b889f063ce22f43ce32af0d619211bb24d649bf93710a561454a8e95251bbe37fcc,0x4d1294e527aa37432c9114065c517545ea86a4fd49fa90aa88aa4feaa0dc5f588914ff49ea854727764e72693137aa6ae4cfa98a12faa5b5006a958d29aa4c03,0x370401357212e025b84b608e212d595a40b384bcc2c640468abcc4302c985882b0215ec2b825684ac088ac200255b01b0555000405480a800d4029c05300a665,0x31b3135634e01303e607cc0328c52589fab5141a29089876b0a22a8c45288a52af960b0c0e97fd2f9a5eb490693d823765e66bbd9005114a22aeab048e92e82,0xb6b88d6118a212046988d2c1aa935046982b411a56ad0168dad11d226b41c682ecfe19df989866fe6225991b2d2657027e2b500ca06480c8018e68ebd1a7a1f8,0xb843691cd7090dec1c1988ef6f6816202e0b7c86f02dd20019a0c724b467488e38ab36e0e8b4c3c405c61f9017b92faa9816d90da2002836433702c10c00eb60,0x10b84d1d00e80168039f610705ad90721ca3734ee5bc43435be16862118e34248d70aa22d52a18d286b06300c4e0b90471ec7211c5981b32b0029]]

def includedGet (i : Nat) := Ledger.packed 22 i #[
    #[0x7c0214f00037c0007f0015fc0007f0031ac0027f0001fc0007f0001fc0007f0085ec0085f0001fc0007f0050fc0015f000d7c0099f0001fc002bf00037c0007f,0x7f0001fc0027f00437c0007f00527c005572001dc005570003fc01ac70003fc000ff0003fc0049f00d43c0017f0001fc0014f04523c004bf0001fc00a370003,0x1168c0017f0001fc0017700c17c0007f42149c0143f0001fc010df001bdc012bd00027c00af700053c040bf00343c000ff00057c0017f00037c00ac70028dc00,0x400557002e3c04ac70003ec040cf0005fc006df00027c0350f0001fc0014f0001fc0017f0015fc0207f0081fc00c6b00acfc002af01033c002af0001fd000ff0,0x5f05279c000bf000afc0a8690001fc000ff0018fcb005f02a0bc0c58f0023bc0013f02ae540305f0006fc6195300067c011cf0014bc040bf002a3c000fb004af,0xc17c288bb0010fc0207704ae74000ff004d9c0f30500217c0105f00217c286bb008aac082ab0005fc003670041fc0524f0821bc0819f0041fc004b70003fc001,0x2a78300737c00bef000fec0321f06ae4401c6f0001fc0045f0001fc042d70001fc304e30fe1ec422af06409c001bf0003fc0a0af0082bc1ce8f012efc002bf02,0xf0001fc0029f0001fc000ff0001fc0e29b009b7c044cf37026c0e4c701607c0746b1403cc808df030a6c2109f0134dc09397035e2c00f8702760c0146f024abc,0xef4095ed076594000ff0001fc0529f00473c0207f0008fc023af0009fc0099f01165c06b27012abc101b70c496c028af0002fc0b6d70708ec113970002fc0125,0x7f00a8fc005b70003fc0007f0411fc0047f0003fc008af00063c2b12b0001fc005df0401fc0045f0008fc0005f0001fc0403f030e9c0007f0000fc0015f000,0x4aec0099f0041fc0027f00237c0007f0001fc02aaf00117c0115f008edc06ca300cd6c0bc1300c1fc3866700237c01d1e0101fc009af0001fc0013f0010fc0,0xfc0092f0045ec02cbf0200fc000bf0147dc000bf0022bc012c30001fc000bf0010fc6344b01533c04d5710375c1a4b30045bc442c30084fc165e3081c9c0034f,0xcb500359c0017f0003fc0017f600bcc0007f0024bc000df02154c015570002fc000bf02247c0a62f0001fc0007f0001fc03d550018fc0049f0082fc002bd0002,0x84b1c1883f009bac324fb03171c00d678bd77c034d702139c0097f00217c0683700893c0052f00467c2a14f000ffc19a9d00287c0103f0bc82c008ef0003fc04,0xc01735004c6c0019f00626c2049f0810fc000bf0003fc000ff4009ec004ef0101fc0482f10996c13dc701346c0043f0001fc125d70003fc00abd0042fc0426f0,0xbd0028fc01173000b7c60bc30028fc0007f0001fc0226f0001fc0032f0041fc008db00a8ac5007f0928f4047270428bc1af050408fc081cf00cc5c0007f0001f],
    #[0x873c0817f0004fc0007f0001fc0007f0001fc0007f0001fc0007f0001fc0007f0001fc000ff0003fc000ff0003fc000ff0003fc0017f009a3c0017f017c0d005,0x119f1104ec01337000b3c0007f0001fc0023f0001fc0007f0001fc0007f000cfc0007f0001fc0007f0001fc0007f021abc075451d854c041af00953c003b701,0xf041d9c10567001e7c0171f0044fc0172f0009fc000df00555c015570045fc04c970005fc00af70081fc004b70b10ec0007f00037c000df01087c0007f0001fc,0x1fc0007f0006fc000ff0014ec0115728a7940050f010a3c0050f011cbc0408f038f140415d320efc002bf000afc000ff0003fc0033f3926a00ab1b063d1c002c,0xff0452d4063270001fc0007f0001fc002af0001fc0007f0001fc244b7007d0c0007f0001fc0007f0001fc0007f0159d80007f0003fc0007f0001fc0007f000,0x22b43c1011f0003fc000bf04067c028cf00a87c001bf000e3c0007f0002fc0007f0001fc0063700317c0007f000afc001bf00373c001bf0109ec000bf0001fc0,0xdc711950011fc10d6100a87c004ef0c361c0007f0001fc0131b0003fc0483f0001fc0007f0013bc0013f0001fc0007f0001fc20c5f0001fc006370140fc000ff,0x41e0f001cfc000ff0003fc000ff00a1dc4101b0654]]

def startGet (i : Nat) := Ledger.packed 11 i #[
    #[0x56995109cb30a4cc778a90d20b3f179aecdc636b692cb1842e758ca95422644908c5081f23a66ccc716d2aa4d08d8ff1cc328560980f81902703e05a08008800,0x7c5f4fe13ad73ae2bbc766ea5d1599720e24c0d79ee0da0af95]]

def itemGet (i : Nat) := Ledger.packed 8 i #[
    #[0x2018a0f0e0d0a0b070c090806050403020100a56f5036340d0c0b0504020100782d89886f635d4d3c2b1d190b04011614556f4d332b26201f1e1d1910060201,0x19030100b86e72493e3640280d4d0ea56f02090c0a07340b05040100c56a5c26251e170d001c1b1a0a071606051910030201de58006f4d33201d1c1b19160d06,0x60373a3069443c2f321e1516270c2d002c1d19038272680f4c4b402d0c0b09068b8a070403020100a6814478463ab02d4026339325391e1d2c0737573c0b8027,0xde9484802c2715031c12131b1911181714100a0502160d0601a888763863373373050fa632481d506e5d3c2b0b0c006f2704193401b06d4c3b83a22e4f6a91,0x716f5f2b2a281007340501025f4e4b2a47b96550362909390a635d3828003e2c2b27040302342b04bb7f69920ed3b9a09912582917280a1b193e275957250302,0xf502e2c1901003327050a1d08070b0209030cafaeadacaba691551700161513100d0a0605013312080302d5c87f70646a5c4d321dd0c0a4771903000aa52926,0x66f88635d3c2b011d190b4d04968b757129cda0bc379f340c1827047360092a3a1e2f9d163c939202102c38211f1d195d00bfbe949b800d6d35062f045c5b8a,0xb93d2b280100201f1e141d191002a3d38bcc847f69675747318a2f371b3200014b17271d190c0b020a09072c03dddcdb506a4ec61064392c28488c7302893a2d,0x6836064908480347070a05040201009e9d9c908b867f3c5d4b2f4f2a9392393d211d36012535991709342738372c1900a19e847f895e57241b4d58251c232122,0x90736f514e4d22040800b88b0f0e9c108a36070b096d0c032c271d0d803b332c066e4e0f41871f0550264d1d0c005d3c342b19270b016f046f4d4a0b340d0f2d,0x50764a412a77741f3a4b382722042d465db03c1e1d1610021901008c8985794125bd733cc90f2655201e80574d02375d0b9134006f332b1f011d1910b9b6a694,0x41503a393022192d158c3c1d100c09070504030a0201340b00a67b6ccf6664532c1d341108a910494d074fac0b0a32adab0f010c050403020900caaaa59f9168,0x3d1e4519170454432d160c03301c152c1d100902b0844c475d39502f1d1c1b0ac59b024b8a403834301a29008b85431445191509042c2717d2c1b5b3b1645d60,0xbb021c1045193143c5602d27160c036d361d15302cada3ac9f70376c227b71645f174d043f19013929403e3834052b2803412a090a00026ba3605a31124f2f2e,0x190c161c2d301d02312c151003a89c8f948b6d686447611d100f22a97166395d75400e3eb29f504f2b284b094e0a0004022c2703d7ba93855e504b352e4f1e14,0x60021d341927010038052d362c033cbcada2918e6a6d545f444f33422916c5a349121c32006260612d1715100c2c1d19090302c57d0501564a67493a60474536],
    #[0x3c25270d0b6301372c19030090b18d6eb541709f47635f2a5029715d3e39282b402709040a38002c0302d8b09c9a957f686b64c742461c2f17311349090c6d16,0x71c6a331b061d1901b094369fb2b196582f412b0a09a56f635d6834a81f0f050201382c1903504b3e4e0400aaa5916e59588053503e2f089b574b38338f6665,0xb7b6b16a4491b383865758325554538143522da42b1e168773603c5d1f340b51370201001d1910c38e8483895882572d0b267a0595d57d10020d00c26f4d2803,0x30c699236431e541d3004024d0a293d09351739383734272c0019a7d5586f5371403c37a01b220aa8016641093e3834d31fb92c285d031d63392b271900cec6,0x635d463c886f892b2d044d1d1901bbbaa08f99694f3836758073503f0e3e3c37352b2a231d59b94d57250b5d00341901a26d6c664f8ab0477f1263444c2d1001,0x49030200e0d3abbc86c580bd50a7334a1a16140f94102d2c2761081d198b0c3a0b0706400400018a090203d0dfcec9a28c777a765844664132272010b20b0f06,0x8d8cce80827873453c1960181602d8462b274d1d0b0400898863584320145d018f7b6b4239c053a5328b0a648a5c382f4c0b5fc119a33c2c481d040c0107094b,0x393870a66f47192a40093e0f32270a1007022b004134281d01c57e7d7caf4f603c36302f997f791c7b29640c345f549d3d1e0493011239373809192c271700b0,0xb3b28c717b476e3eb90e9c310d687ca349b4286f070a0f0134050402968d504c453a602fb0435725371630150c04463c1d1914068027180b0100a9664f5f4b8c,0xd2fa6463b8091d6370f32150c603c3306011e2d1d2c1927160003b9a2918c6a442b26251c1b0d2c2757895810d90203d314336f20c56d05071d4d19160601b5,0x1e3632151c1b170f0cb8270e0d16420631340405020800101903019e6b5e7f4dc42505652a295f3d3e1d3404270a191b1f002b280302d7d8b07754534f454314,0x375d1e2c03021610012d1d463c1900b0864e4d3b38201f340b6875462d3a2c10020c7774765d22371e1605197348003c270401dac7b06d835e4f4d60386a2d30,0xa07032c0200cbbb939b7d643d3935699a10991e430c3495867a792f68553c17013260271d780337002c19a4a29c9991908f6a68554d340504c9c8c75438833a,0x5631301535a125651320551d1b10080e266f99022700146d1e4d0134d3b90403053d28191f2ba7a565635f3753294826198d12496847386610090c640b273c1d,0x501f320e0da608050226635138101d5d2b2704016f34190f00e1b49c9796937d7a7868677c62492f422c10980a6d6a341c1b160d07069503054d1d19d45d5e5c,0xd139ce374e]]

def keyGet (i : Nat) := Ledger.packed 16 i #[
    #[0x89410ac1002a057626754ac500080a66268421ca046629961ac440642a840021835b23450a6564c885a8637548c404cb48a5856a00100029002c0018002b0011,0x12a403a904d16a620261826a6482646283f1126400280023867b0a8218a42346467306f3a698001a6bc723a747e437c5002007eb89f129972097515974d70766,0x67b4006528e785aa98432541b76106a9b5612896884143514842a14801f809f304c203b90022764379930ab32ab4b99875736ac223f607b61266b46a49422285,0xb481365314b6157362846b560ad1926a01fb2ab7546729f767c84264476442a407cb19430019015340413846b4616b5336b3056207e5457229a2684004d880a8,0x37832951b460b04861838098b7e053a066f010a358a004dbb8e021d41a6123b78042b57a65620ab964832bd4565967c2894800c815664665b27ab56a5ad241db,0x3acbb26689ba83f02390106400f91564126172673765b34868497359556720a204810461837545c43a654843048269b3828b814bb34b484148a42651b5c020e7,0x7e8056039463996097629f41ac1606200625ac169f0015089f0287505c8499142cb08e95a667143209108990a81469134ca65c8bac030c508a06640b57bb14b,0x69900483]]

def check (i : Nat) (b : Load.Board) (cap : Nat) :=
  let h := headerGet i
  let s := h>>>9
  let a := startGet s
  let seen := includedGet i
  let hints := (List.range (startGet (s+1)-a)).filterMap fun j =>
    if seen.testBit (j/2) then some (keyGet (itemGet (a+j))) else none
  Rules.accepts b cap (selectorGet (h &&& 255)) (Fin.ofNat 4 (2+((h>>>8) &&& 1))) hints
end More

namespace ReceiptData
open Ledger (field)
def pairGet (i : Nat) := Ledger.packed 16 i #[
    #[0x14035021050605032811914048064920120c2411]]

def posRows : Array Nat := #[3,6,12,24,17,33,66,132,264,160,320,288,133,38,162,26,13,21,37,168,44,54,58,388,22,105,106,277,308,74,259,321,120,389,393,19,262,266,273,11,148,152,81,82,108,56,265,178,284,306,278,392,324,292,41,145,176,304,154,97,76,387,139,170,194,196]

def negRows : Array Nat := #[42,50,69,104,116,138,201,208,261,276,385,402,34,129,5,18,10,128,32,136,40,130,36,16,8,384,260,20,2,1,257,72,9,258,4,272,144,80,0,48,68,64,256,146,192]

def nearGet (i : Nat) := Ledger.packed 32 i #[
    #[0x295107a221b4901007552996028631218007a1310bb318b30780a12126547010024631210bb318b42b4495702b4495601a219671022631212310045023100440,0x23011242b720a121041883652867a242041223540a852bb6297117a2172671212934757069347560075529a70442235404122343293475502345344066547010,0xa8228b32867a2310720614143011243296237a302206121022061310720612029510791b2206110024631100720613023453441022061202807a23229347560,0x1a852ba526b53010260530100b8318b3012312b2075b9995230112320418a343452334b5452334b4075529854867a2520a852bb7ba208681b22061210a208681,0x2807a2210418a332430112212867a2213a852ba60780a11002263110296237a22345345063453440072061312837a2624a852ba5172671100b8318b229b11792,0x2867a2510a8228a643011232694475602867a2612375344204219660ba2086702b3495508867a26263453430297117922345343029623792233772322867a232,0x291475802b1495602b149570142140300526306014264041b780a1101744711002403110230112210a208660022061100a318671290475502904756005263020,0x231004630a208680231004530a2086902867a2522b449571b24631101261402080b7a160024631a00a31967064122373024631b1811490606412234361144010,0x28860ab92b4495648867a2312867a2412867a243694475612315047023b05460295107920a60a67129510782075529970a208697041223650bb318b50a208691,0x28b60ab8295207a36b4495706b4495606412235421b4401028860ab82867a2726940b5600ab56bb70bb318930bb318a30bb318a48b4495606bb248a408b95bb7,0x6728a2510a8228a228865aa80a30a6712b449580475529868867a24269005562231504500a60868181b490100a408681810490100a2086a161b440100a308681,0x231504600a20867166b440102b4495500a20a671615440107804a364665440104867a24228860aa823047221b48190202b4495536728a2616728a2622b449551,0x6943b564446772310a208670660230a02b4495400bb318926ab248a35ab248a44ab56ba52b44956329005551290055612067a240660530a18067a230056630a0,0x6900554169005552231534406944755023450450231504402944756023153450b426401086b44010b246612128860aa70a2196710a2196814467724269437564,0x810490402067a231b2263010041883436728a263436772420a2186810a2086872310043081b49060614495504067a2316944b5500bb31863234004406940b540,0x2b4492412b4492622867a2546744725369437253430112316943b25367447242022630106602309081b498212067a2304301151005663090b780a1500a822892],
    #[0x2067a2502067a221231534306b431262482304532315043029147560b226402066044010b481901023700421430112106900524123723421293772412b449252,0x2900555029710792237004402900556086053010290055708900556067447231446772204467b2106944754023720421290772416744b23183041020]]

def farGet (i : Nat) := Ledger.packed 47 i #[
    #[0xc4491c2619822b90381b2b045720703544089e40e1ec8b1650a82510cc18a9238753a831324713a74862248e135090c4491c265d022790387ba9c38d1a60ca4,0xae12580193845d30d802174c3845b0064e9a70c860041d34e190c010ba35c24b0010746b84960042e98708b60085d30e116c0081c38d1a60c93689b25142f069,0x636485513903668322a07206cd064500e45021288189c81b341915140fbe79e3b0281f7cf3c7608e38b1b249301e4102270f503c82044e1ea2e9a70c8600c9d1,0x9d04c80ea05cd061146252c289011944a585120243787c69d04ca31256124208ca24ac2484121a044f2070f53587a88cf286471c58d921584e38b1b242b11c71,0x1e410da26c9450bc9baadc55280217469c38c18a130d887181d0162ca1504a2a445982a08254887b060f04a911660a82090dd56e2a94008443d83078243787c6,0x88211c8a0425105338e2c6c924c2a269d73cb59562ca1504121a85562c082a3508ce40e5acaa119c81cb50dd40b9a0c2209c3e030790323162c6831a4270f80c,0x5518872234c0f0540f7cc1e090e25e88d043c1ac3d446794214089e40e1e847206cd064504e40d9a0c898443911a607936873234c2f28a269d73cb550e450212,0x42e1fa4f3c1a0694b51d4055ca0c612c0a5b438e2c6c924e083184b0296d5c3f49e783411c716364927170fd279e0d2472281094418ce38b1b249409cc163648,0x9e310916cf194061022da710610c488a0480c21891140905e310916cf081c3db4e81140387b69d022a2f3284d927841e6509b24f10c0690321a71080d206434e,0xc8a04250253399c084a0464e34a52341a08e6702128121c209a4f02421387b69d022c2da7387a04481b4e70f40890bcca13649e3280c2045b4e4270f6d3a0458,0x14084a048272f59d5649d103301a0c01030e6a5b388a475c24de40ac0d3659740d5c1e2903559728186563418d108109c88a04c50213911409cd03301a0d3881,0x7cf3c75c601a8125938820e615b3a5a43914084a04e27228109409c9c3f49e783401c8a0425026141dc06834e40c35a8a2c2294e450212812920660341803139,0x9e78338a0f20341a710992d4750154070f6d3a04505c2c831052a81c716364856041cc25811126ead5db281146a36f3224f084c79c3ef062041ac25164b4081f,0x160132387b69d022a101a40c869cca07ea3e15b384285a7a52421806a04964e42f18848b67885c3f49e78330387e93cf067058b28541044271c58d92098dc3f4,0x8a2e2c88d060484c58b1a0c6993a3d74e80450986c438c0e61327747a0104207ea3e15b28c02546e8b661a93bc3d04c20e104089c3d41c20811387a8b90628,0x60f207de3a81327747a0108663ce1f783184285a7a52432747ae9d]]

def begin_Get (i : Nat) := Ledger.packed 10 i #[
    #[0xa42849e2749a250902388c228862007b1e4781d4721b46b1a467194641805d16052134491143d0ec340c82e0ac280902006c1a0601404c0f0380b01c0200000,0x25b96c5955c56157521424ed364bd2648d20475194550e42506411013fcfc3e8f83d0ed394e1378d9350d0330c931cc6314c3308bd2ecb92d8b42c0ae2b4ab2a,0x324a91a3f8de2e8a62889a2487e1b8621684e0b81e04805fe7e5f17a9e5789df771d7759d4749cb719c4705bf6e9b76c9aa695a0669946498f62d855f97c5d97,0xe1b5acfb3acbb0abbad6b0abeadaaeaaaa2a6a96a4a8aa0a7a9ca6a96a5290a3e8ea2e809fa7d9f27a9e6789da759ce6c9a66698a5f9765a95e5594e529424e9,0xe2787e1b84e0b80dfb7ddeb72dc76edb35dd5b54d374bd2743d073dcef36cd734ccb2fcb32aca326c9323c871fc771bc6717c4f10c330ac2306c0efcbeaf3ba2,0x39ce678c]]

def itemGet (i : Nat) := Ledger.packed 9 i #[
    #[0x35088b06833138946431180bc5c2d160ac4c2a148a0280c138404c251208c4421100303e1e0e8702e1b0d06430110b8482c150a0342612088401e0e06830160a,0xaa160a850485429850705206144a050278449c0c25134543d119189822259289248239188a44218705419089082e41200fc623e1e8f0203b128e818391c0dc6c,0x5ca66a328c0d26833894583029874b26632830c8633114c601730924860c2f044862c0e10cc00c0d97c885e2d174a21b278eca65c0885c3a5b2d16484582b958,0x421d0c8513211068240a00fe7e3e9f0f47b3d1e4f0773b1d4e873159645e582c9b8a672389c0c66f349b8a6582b074a64f2e044c25d3690cd86b29908b0660d8,0xc1d28d323a45289321f45a853a1028a813e9e4ea39389b4d040b40e428981e0f4ca612c974b0e01e954a0b51025498d924914823d1c8d1aa311688430e914894,0xea253ac41e1b4ea2960af532b84aad56094368a1d26556aa4ea2836a94c89436991d229509a0f948d43a4529d142628840363c1d2994a3a4ca2d488a450e9328,0x5883a6030cc0c26089580bf5f2e870885daf4ac735e2ed74385cae10a0e078990a0f070981c264889918111c1684ab75b2656a2507971688e1389518b32e2c8c,0x37d903a12b7980dd6e309822562b00b86a1a360708834995b6da59365b06a6ba21acd507319a8d369278ccd16833d9ccd6632d94c9613218e0e07168b40e6331,0x57ab5deee33095c8ed763ad4c9e2eba93ee92b8e0d28832ba1cea65599980661d06c4a1b53399481d72a9d82e45338c36661286dc49d522984a1b1d3858ee033,0x5383c1a0b0481c0a028837b5e00ff57bf9fae67e399f6be5e2e870b97d3e59cc6070398c5a630e01cc67c3ddecf56a30022c6063d156f36baed5e1d793c5e09f,0x39088540a37075eb558cc66a95a35197c399aac68c39a2f168ab9a28e60e999c8e60ec4dce6689444b8346c1a9b03834996210f8743614d72bc32170a8142610,0xea7f3a9f4e27b379e4de773a9cce26f369acd2673298cae612f974b6592b954a65125922c15c0a05c9e4d251d49026ad91c8a43208a39a051e8fc79b10280c76,0x4da2cf66b2d92af5aaed5a71639bcdac561a8d82bf5ea7d76b95bad566b157ab4e671559bcdaa953a9546a14fa7536994b00d2a9348a38028d45a250e8541a04,0x5c260f0581c05a68579b55e2ff7ebb5f6f97bbd5e6f176bbdd8097500dd2e7729c4de6d610180ae370008028f6fb75b6d95babd6abb569dcea6f36b5d26d547b,0x384d469f4c09d2e92ff799be8e6da2d0823419fcf677399b0381b3569bce640b98cbe5b2b94c9d0b2591c0e43098bc7e3b1b8cc5e331784c560b1388c3e1b018,0xeff84e371789c3e14e38360e06437f80df6f701bcddcdb75b90282771b7db6d70569bb6d309b3d96c761afd2eaf0b43d76b6f582bfe1307acd5d0f55a3bcea71],
    #[0xe873f9dcde672f95c9e46178fadc14e]]

def rectangle (w p q : Nat) : Near.Hint :=
  let pi := fun n => posRows[(w >>> (8+n*(p+q))) &&& ((1<<<p)-1)]?.getD 0
  let ni := fun n => negRows[(w >>> (8+p+n*(p+q))) &&& ((1<<<q)-1)]?.getD 0
  .inr (w &&& 15,(w>>>4) &&& 15,pi 0,ni 0,pi 1,ni 1,pi 2,ni 2)

def witness (i : Nat) : Near.Hint :=
  if i<10 then let w := pairGet i; .inl (w &&& 511,(w>>>9) &&& 511)
  else if i<297 then rectangle (nearGet (i-10)) 4 4
  else rectangle (farGet (i-297)) 7 6

def hints (s : Nat) := let a := begin_Get s; (List.range' a (begin_Get (s+1)-a)).map fun j => witness (itemGet j)
end ReceiptData

namespace Reduced
open PublicFloor Verification Inputs
open Load (Board Root Link)

def root (i : Nat) : Root := ReducedData.roots[i]?.getD (0,0,0,0,0,0,0)

def mode (r : Root) := r.1!=0

def height (r : Root) := r.2.2.2.2.2.2

def level (r : Root) (h : Nat) := r.2.2.2.2.2.1+h

def budget (r : Root) (h : Nat) := cap (mode r)-h

def segment (r : Root) (h t : Nat) := ReducedData.segment (level r h) t

def count (r : Root) : Nat → Nat
  | 0 => 1
  | h+1 => if h<height r then (segment r h 0).1 else 0

def entry (r : Root) : Nat → Nat → Board
  | 0,_ => (0,inputs,[])
  | h+1,j =>
    let (p,act,_,_) := ReducedData.get (mode r) (segment r h 0) 0 j
    Load.successor (rank (mode r)) (entry r h p) act

def token (r : Root) (h j : Nat) := if h=0 then 1 else Ledger.atLevel (level r (h-1)) j

def future (r : Root) (h j : Nat) :=
  if j<count r h ∧ token r h j≠0 then some (entry r h j) else none

def outgoing (r : Root) (h p : Nat) :=
  if h≥height r then [] else [0,1,2].flatMap fun kind =>
    let v := segment r h kind
    Table.window (ReducedData.get (mode r) v kind) p 0 v.1

def palette (tag : Nat) := (List.finRange 79).filter fun i => (Ledger.paletteGet (Ledger.accountGet (tag-1) &&& 127)).testBit i.val

def structural (b : Board) (cap tag : Nat) :=
  if tag<Ledger.moreBase then
    (decide b.2.1.Nodup && decide (cap≤b.2.1.length)) &&
      ColorAxes.rejects b (Ledger.corners (tag-Ledger.colorBase))
  else More.check (tag-Ledger.moreBase) b cap

theorem structural_ok {m cap b tag} (test : structural b cap tag=true) : closed false m cap b := by
  unfold structural at test
  split at test
  · obtain ⟨both,hit⟩ := Bool.and_eq_true_iff.mp test
    obtain ⟨nd,hi⟩ := Bool.and_eq_true_iff.mp both
    intro k le _ run
    apply ColorAxes.cut _ hit (Trace.forget run)
    rw [List.toFinset_card_of_nodup (of_decide_eq_true nd)]
    exact le.trans (of_decide_eq_true hi)
  · exact Rules.cut test

def full (r : Root) (m h : Nat) :=
  ∀ j, j<count r h → token r h j≠0 → closed (mode r) m (budget r h) (entry r h j)

theorem follows {r m h} (later : full r m (h+1)) {i d} (eq : future r (h+1) i=some d) :
    closed (mode r) m (budget r h-1) d := by
  unfold future at eq
  split at eq
  next ok =>
    injection eq with eq
    subst d
    rw [show budget r h-1=budget r (h+1) by unfold budget; omega]
    exact later _ ok.1 ok.2
  next => contradiction

theorem last (r : Root) (m : Nat) : full r m (height r+1) := by
  intro j hj
  simp [count] at hj
end Reduced

namespace SignedSupply
open PublicFloor Verification Project Atlas
open Load (Board)

def check (cap : Nat) (b : Board) (i : Fin 79) (alt : List Choice) :=
  let mask := domain i
  let const := b.2.1.countP (isMaskedConstant mask)
  let cut := if i.val=78 then decide (alt.length < b.2.2.length+const) else decide (cap+alt.length < lower 0 i+const)
  (cut && Cuts.feasibleB true inputs alt) && b.2.1.all (availableB true mask (wires inputs alt))

theorem sound {m cap} {b : Board} {i : Fin 79} {alt : List Choice}
    (low : Lower true inputs graph m) (nd : b.2.1.Nodup) (ok : check cap b i alt=true) : closed true m cap b := by
  intro k le exactSize run
  obtain ⟨left,supplied⟩ := Bool.and_eq_true_iff.mp ok
  obtain ⟨cut,good⟩ := Bool.and_eq_true_iff.mp left
  obtain ⟨slice,_⟩ := geometry low i
  obtain ⟨f,roots,dom,base,nc,floor⟩ := slice
  obtain ⟨bank,paid,provides⟩ := attain dom base alt (Cuts.feasible_ok good)
  have ready : supply true bank ((b.2.1.map observe).map (restrictRows f)) := by
    intro w hw
    obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hw
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hm
    exact availableB_sound dom provides (List.all_eq_true.mp supplied v hv)
  have limit := projected_bound f (list_run (Trace.forget run) b.2.1 nd rfl) nc paid ready floor
  have counted := count_constants dom b.2.1
  have costs : price true inputs (domain i) alt≤alt.length := List.countP_le_length
  change (if i.val=78 then decide (alt.length<b.2.2.length+b.2.1.countP (isMaskedConstant (domain i)))
    else decide (cap+alt.length<lower 0 i+b.2.1.countP (isMaskedConstant (domain i))))=true at cut
  by_cases last : i.val=78
  · rw [if_pos last] at cut
    have x := of_decide_eq_true cut
    simp only [lower,if_pos last] at limit
    omega
  · rw [if_neg last] at cut
    have x := of_decide_eq_true cut
    simp only [lower,if_neg last] at limit x
    omega
end SignedSupply

namespace Leaf
open PublicFloor Project Atlas Verification
open Load (Board)

def first := inputs.getD 0 zero

theorem first_mem : first∈inputs := by decide +kernel

def pick (gs : List Choice) (j : Nat) := (inputs++gs.reverse.map choiceVal).getD j first

theorem pick_ok (gs : List Choice) (j : Nat) : pick gs j ∈ wires inputs gs := by
  unfold pick
  simp only [List.getD_eq_getElem?_getD]
  cases e : (inputs++gs.reverse.map choiceVal)[j]? with
  | none => exact List.mem_append_right _ first_mem
  | some v =>
    have hv := List.mem_of_getElem? e
    simp only [wires,List.mem_append,List.mem_map,List.mem_reverse] at hv ⊢
    exact hv.symm

def codeOp (u : Bool) (c : Nat) := (c/256) % (if u then 4 else 2)

theorem allowed_op (u : Bool) (c : Nat) : allowed u (codeOp u c) := by
  cases u <;> simp only [allowed,codeOp,Bool.false_eq_true,ite_false,ite_true]
  · exact Or.inl (Nat.mod_lt _ (by decide))
  · exact Or.inr ⟨True.intro,Nat.mod_lt _ (by decide)⟩

def decode (u : Bool) : Nat → Nat → List Choice
  | 0,_ => []
  | n+1,c =>
    let width := if u then 1024 else 512
    if c<width then [] else
      let gs := decode u n (c/width)
      (codeOp u c,pick gs (c % 16),pick gs ((c/16)%16))::gs

theorem decoded (u : Bool) (n c : Nat) : feasible u inputs (decode u n c) := by
  induction n generalizing c with
  | zero => trivial
  | succ n ih =>
    by_cases early : c<(if u then 1024 else 512)
    · rw [decode,if_pos early]
      trivial
    · rw [decode,if_neg early]
      exact ⟨allowed_op u c,pick_ok _ _,pick_ok _ _,ih _⟩

theorem paid_le (ms : Sig) (gs : List Choice) :
    Mono.paidCount graph ms inputs gs≤gs.length := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    simp only [Mono.paidCount,List.length_cons]
    cases Mono.reused graph ms (wires inputs gs) g <;>
      simp only [Bool.not_true,Bool.not_false,Bool.toNat_true,Bool.toNat_false] <;> omega

def cover (u : Bool) (mask : Sig) (pool : List Sig) (w : Sig) :=
  if RankedIndex.number w<9 then true else
    if u then availableB true mask pool w else
      (zero::one::pool).any fun v => Mono.dominatesB graph mask v w

theorem mono_cover {mask gs w} (h : cover false mask (wires inputs gs) w=true) :
    (zero::one::wires inputs gs).any (fun v => Mono.dominatesB graph mask v w)=true := by
  unfold cover at h
  split at h
  next known =>
    rw [RankedIndex.number_ok,show 9=inputs.length by rfl,List.idxOf_lt_length_iff] at known
    apply List.any_eq_true.mpr
    refine ⟨w,List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_right _ known)),?_⟩
    simp [Mono.dominatesB,zero]
  next => exact h

theorem signed_cover {mask gs w} (h : cover true mask (wires inputs gs) w=true) :
    availableB true mask (wires inputs gs) w=true := by
  unfold cover at h
  split at h
  next known =>
    rw [RankedIndex.number_ok,show 9=inputs.length by rfl,List.idxOf_lt_length_iff] at known
    unfold availableB
    apply Bool.or_eq_true_iff.mpr
    left
    apply Bool.or_eq_true_iff.mpr
    right
    exact List.any_eq_true.mpr ⟨_,List.mem_map_of_mem (List.mem_append_right _ known),beq_self_eq_true _⟩
  next => exact h

def limit (cap : Nat) (b : Board) (i : Fin 79) (mask : Sig) (n : Nat) :=
  let c := b.2.1.countP (isMaskedConstant mask)
  if i.val=78 then decide (n<b.2.2.length+c) else decide (cap+n<lower 0 i+c)

theorem limit_mono {cap b i mask n n'} (ok : limit cap b i mask n=true) (le : n'≤n) :
    limit cap b i mask n'=true := by
  unfold limit at ok ⊢
  split at ok
  · rename_i eq
    rw [if_pos eq]
    exact decide_eq_true (lt_of_le_of_lt le (of_decide_eq_true ok))
  · rename_i ne
    rw [if_neg ne]
    have := of_decide_eq_true ok
    exact decide_eq_true (by omega)

def check (u : Bool) (cap : Nat) (b : Board) (i : Fin 79) (word : Nat) :=
  let gs := decode u (if u then 7 else 5) word
  let mask := if u then domain i else border i
  (decide b.2.1.Nodup && limit cap b i mask gs.length) &&
    b.2.1.all (cover u mask (wires inputs gs))

theorem sound {u m cap b i word} (low : Lower u inputs graph m) (ok : check u cap b i word=true) :
    closed u m cap b := by
  obtain ⟨both,supply⟩ := Bool.and_eq_true_iff.mp ok
  obtain ⟨nd,cost⟩ := Bool.and_eq_true_iff.mp both
  cases u with
  | false =>
    let gs := decode false 5 word
    apply Substitute.sound (i:=i) (alt:=gs) low (of_decide_eq_true nd)
    apply Bool.and_eq_true_iff.mpr
    refine ⟨Bool.and_eq_true_iff.mpr ⟨limit_mono cost (paid_le (border i) gs),Cuts.feasible_yes (decoded false _ _)⟩,?_⟩
    apply List.all_eq_true.mpr
    exact fun w hw => mono_cover (List.all_eq_true.mp supply w hw)
  | true =>
    let gs := decode true 7 word
    apply SignedSupply.sound (i:=i) (alt:=gs) low (of_decide_eq_true nd)
    apply Bool.and_eq_true_iff.mpr
    refine ⟨Bool.and_eq_true_iff.mpr ⟨cost,Cuts.feasible_yes (decoded true _ _)⟩,?_⟩
    apply List.all_eq_true.mpr
    exact fun w hw => signed_cover (List.all_eq_true.mp supply w hw)
end Leaf

namespace Reduced
open PublicFloor Verification Load

def replacement (u : Bool) (b : Board) (cap tag : Nat) :=
  let w := Ledger.programGet (tag-Ledger.programBase)
  Leaf.check u cap b (Fin.ofNat 79 (w &&& 127)) (w>>>7)

theorem replacement_ok {u b cap tag m} (low : Lower u inputs graph m) (yes : replacement u b cap tag=true) :
    closed u m cap b := Leaf.sound low yes
end Reduced

namespace Replay
open PublicFloor Reduced Verification
open Load (Root)

def notes (r : Root) (h j : Nat) := ReceiptData.hints (Ledger.accountGet (token r h j-1) >>> 7)

def test (r : Root) (h j : Nat) :=
  let tag := token r h j
  let b := entry r h j
  let n := budget r h
  if tag=0 then true else if tag<Ledger.programBase then
    Packed.validate (mode r) n b (palette tag) (outgoing r h j) (future r (h+1)) (notes r h j)
  else if tag<Ledger.colorBase then replacement (mode r) b n tag else if tag<Ledger.phaseBase then !(mode r) && structural b n tag
  else PhaseCheck.accepts b n (PhaseRegistry.hints (tag-Ledger.phaseBase))

theorem point {r m h j} (low : Lower (mode r) inputs graph m) (later : full r m (h+1))
    (tag : token r h j≠0) (pass : test r h j=true) : closed (mode r) m (budget r h) (entry r h j) := by
  unfold test at pass
  rw [if_neg tag] at pass
  split at pass
  · exact Packed.verified low (fun _ _ eq => follows later eq) pass
  · split at pass
    · exact replacement_ok low pass
    · split at pass
      · obtain ⟨flag,st⟩ := Bool.and_eq_true_iff.mp pass
        have md : mode r=false := by
          cases hv : mode r with
          | false => rfl
          | true => simp [hv] at flag
        rw [md]
        exact structural_ok st
      · exact PhaseCheck.cut pass

def sectionB (r : Root) (h begin len : Nat) := (List.range' begin len).all (test r h)

end Replay

namespace Replay
open PublicFloor

def tree (r : Load.Root) (h a : Nat) : Nat → Prop
  | 0 => sectionB r h a (min 16 (Reduced.count r h-a))=true
  | d+1 => tree r h a d ∧ tree r h (a+16*2^d) d

theorem inside_tree {r h d a j} (yes : tree r h a d)
    (in_layer : j<Reduced.count r h) (lo : a≤j) (hi : j<a+16*2^d) : test r h j=true := by
  induction d generalizing a with
  | zero =>
    apply List.all_eq_true.mp yes
    apply List.mem_range'_1.mpr
    simp only [Nat.pow_zero,Nat.mul_one] at hi
    exact ⟨lo,by omega⟩
  | succ d ih =>
    change tree r h a d ∧ tree r h (a+16*2^d) d at yes
    by_cases left : j<a+16*2^d
    · exact ih yes.1 lo left
    · apply ih yes.2 (Nat.le_of_not_gt left)
      rw [Nat.pow_succ] at hi
      omega

theorem advance {r m h d} (low : Lower (Reduced.mode r) inputs graph m)
    (size_ : Reduced.count r h ≤ 16*2^d)
    (cert : tree r h 0 d) (tail : Reduced.full r m (h+1)) : Reduced.full r m h := by
  intro j hj active
  exact point low tail active (inside_tree cert hj (Nat.zero_le _) (by simpa using lt_of_lt_of_le hj size_))

def levels (r : Load.Root) (h : Nat) : List Nat → Prop
  | [] => h=Reduced.height r+1
  | d::ds => (Reduced.count r h ≤ 16*2^d ∧ tree r h 0 d) ∧ levels r (h+1) ds

theorem levels_ok {r m h ds} (low : Lower (Reduced.mode r) inputs graph m)
    (yes : levels r h ds) : Reduced.full r m h := by
  induction ds generalizing h with
  | nil =>
    change h=Reduced.height r+1 at yes
    exact yes ▸ Reduced.last r m
  | cons d ds ih => exact advance low yes.1.1 yes.1.2 (ih yes.2)
end Replay

namespace Start
def mono : Array Nat := #[0x9c0013800270004e802400a24409460128c0009c0013800270004e802200120c0141802838016008244044300886,0x802221120c015084483801620120c809000483802000920c0148824830000000000084c00483802600520c054601483,0x9c0013800270004e801e24120c058210483000040000800270004e801e02824501e00a091000020000400270004e,0x8025004a0c124c012830009c0013800270004e8023002a0c024300a838017000a0c084600283802428120c09c420483,0x20000500e00028380244122188290048860009c0013800270004e801e40a2180a4c02886000000000000270004e,0x8026480a0c0ac4202830009c0013800270004e801f040a0c229010283000040000800270004e8020420a0c026108283,0x9c0013800270004e801f609218054882486000000000000270004e80236052180446014868017601218104c00486,0x80208412180482104860000400008209000486801e82423104e00908c000020000400270004e8026811218055084486,0x9c0013800270004e8020c0a23009488288c000000000001488088c802568121824d0204860009c0013800270004e,0x801ec48260289012098000040000800270004e801ee222300a610888c000020000400270004e8024e1223009508488c,0x400000004e801e614260909005098000000013800000004e8022e8223008c42088c8016e0223020d00088c,0x801f480a4430d020291000000013800000004e801c240a44148210291000000000800000004e801c020a44126108291,0x8017200a8408c4002a18020640a842482102a100004000080482002a1801f220a842261082a1000020000400270004e,0x802148130848c4204c200002013080000804c2801d0413084482104c2000020000800008004e8023280a8428c4202a1,0x801ea8241088c420904000040013800010004e]

def signed : Array Nat := #[0x6000140001804830000800010014180083000060120c000180083804400120c0141802830000600010000180886,0x804e00522c05468148300006000180001804830000a00014094680483000060a254000180486804c00a25409468128c,0x180091000000000001488248300000000000000000000000c00018054680483000060522c00018048b,0xe0001c01508048300006102840001800a18044210284015084483000060001c0001804830000000000000000000,0x400008000100002000020000400008000100002000040001804c2000020000501e08a0910000200004000080001,0x804c28160c09c4a04830000600020000180483000040000800010000200004000080001805030000400008058290483,0x8022180002000868045002218024300a830000800014000200283000100002009c480483000068160c000180583,0xc00018124d002830000804a2c00020028b804d004a2c124d0128300008000180002002830000a00014024300283,0x80001c0002002830000000000000000000000000000000020029100000000000a4d028860000000000000000000,0x20000402610828300002000040000800010000e0001c82910028300008122980002002a1804c412298829104886,0x40000800020030300004000082291102830000400008000100002000020000400008000100002000040002000c2,0x10000200ac5002830000880e0c000200383804e480e0c0ac52028300008000200002002830000400008000100002,0xc000180446004860000a0423000028008c80456042300446014860000a00018000280486,0x804e8112980552844860000a0001c000280486000000000000000000000000000000002802910000000000054a82486,0x2000040002804c2000020000504e20908c00002000040000800010000e0001c0552804860000a112980002802a1,0x4000080001000020000400008000280104000040000804821048600004000080001000020000200004000080001,0x100002024d2004860000a81618000280586804d68161824d2204860000a00020000280486,0x804ce122b009548488c0000c0001c00030088c000000000000000000000000000000003002910000000000084c0288c,0x2000040003004c200002000040a650888c00002000040000800010000e0001c09548088c0000c122b00003002a1,0x4000080001000020000400008000300904000040000828941209800004000080001000020000200004000080001,0x100002008c40088c0000c806200003001888044e8062008c42088c0000c0002000030088c,0x40000082910000000000000000000000000001c000000291000000000000000000000000142e0000005098,0x8000010291000000000000000000000000000040000000010000000000000000000,0x2000000029100000000000000000000000080e4400002029100000000000000000000000000008000000002,0x400008000100002000020000400008000100002000040003804c200002000042271082a10000200004000080001,0x804528068020d0202a10000e000200003802a10000400008000100002000040000800038090400004000082090102a1,0x20000400008000100002000080000904c20000200004000080001000100002020d0002a10000e80680000381188,0x2000200000804c2000020000400008000100002807000000a04c200002000040000800010000200008000080002,0x400020000100904000040000800010000200004828100001209040000400008000100002]

def hint (u : Bool) (i j d : Nat) (ka kb : Bool) :=
  let (a,b,op,m) := if i<j then (i,j,d,ka.toNat+2*kb.toNat) else
    (j,i,if d=2 then 3 else if d=3 then 2 else d,kb.toNat+2*ka.toNat)
  let pair := a*(17-a)/2+(b-a-1)
  let idx := 4*((if u then 4 else 2)*pair+op)+m
  let ws := if u then signed else mono
  ((ws[idx/20]?.getD 0) >>> (19*(idx % 20))) &&& 524287
end Start

namespace Raw
open PublicFloor Trace Inputs Verification
open Node (four four_ok sameB same_ok)
open Reduced (root entry)
open Load (Board)

def seeds (u : Bool) : List Nat := if u then [26,30,31] else [3,6,7,8,9,10,11]

def first : Board := (0,inputs,[])

def test (u : Bool) (g : Step) (ka kb : Bool) :=
  let tag := Start.hint u (inputs.idxOf g.2.1) (inputs.idxOf g.2.2) g.1 ka kb
  let b := next u first g ka kb
  if tag<128 then Cuts.check u (cap u-1) b (Fin.ofNat 79 tag)
  else if tag<262272 then
    RootPins.pairLost u b.2.1 (Fin.ofNat 512 (tag-128)) (Fin.ofNat 512 ((tag-128)/512))
  else
    let k := (tag-262272)/16
    (seeds u).contains k && sameB b (entry (root k) 1 0) (Fin.ofNat 12 ((tag-262272)%16))

def row (u : Bool) (a : Sig) := inputs.all fun b => (opsOf u).all fun d =>
  if a=b then true else four (test u (d,a,b))

set_option maxRecDepth 14000 in
set_option maxHeartbeats 0 in
theorem f0 : row false (inputs.getD 0 zero)=true := by decide +kernel

set_option maxRecDepth 14000 in
set_option maxHeartbeats 0 in
theorem f1 : row false (inputs.getD 1 zero)=true := by decide +kernel

set_option maxRecDepth 14000 in
set_option maxHeartbeats 0 in
theorem f2 : row false (inputs.getD 2 zero)=true := by decide +kernel

set_option maxRecDepth 14000 in
set_option maxHeartbeats 0 in
theorem f3 : row false (inputs.getD 3 zero)=true := by decide +kernel

set_option maxRecDepth 14000 in
set_option maxHeartbeats 0 in
theorem f4 : row false (inputs.getD 4 zero)=true := by decide +kernel

set_option maxRecDepth 14000 in
set_option maxHeartbeats 0 in
theorem f5 : row false (inputs.getD 5 zero)=true := by decide +kernel

set_option maxRecDepth 14000 in
set_option maxHeartbeats 0 in
theorem f6 : row false (inputs.getD 6 zero)=true := by decide +kernel

set_option maxRecDepth 14000 in
set_option maxHeartbeats 0 in
theorem f7 : row false (inputs.getD 7 zero)=true := by decide +kernel

set_option maxRecDepth 14000 in
set_option maxHeartbeats 0 in
theorem f8 : row false (inputs.getD 8 zero)=true := by decide +kernel

theorem rowsf : inputs.all (row false)=true := by
  unfold inputs
  simp only [List.all_cons,List.all_nil,Bool.and_eq_true]
  exact ⟨f0,f1,f2,f3,f4,f5,f6,f7,f8,True.intro⟩

set_option maxRecDepth 14000 in
set_option maxHeartbeats 0 in
theorem t0 : row true (inputs.getD 0 zero)=true := by decide +kernel

set_option maxRecDepth 14000 in
set_option maxHeartbeats 0 in
theorem t1 : row true (inputs.getD 1 zero)=true := by decide +kernel

set_option maxRecDepth 14000 in
set_option maxHeartbeats 0 in
theorem t2 : row true (inputs.getD 2 zero)=true := by decide +kernel

set_option maxRecDepth 14000 in
set_option maxHeartbeats 0 in
theorem t3 : row true (inputs.getD 3 zero)=true := by decide +kernel

set_option maxRecDepth 14000 in
set_option maxHeartbeats 0 in
theorem t4 : row true (inputs.getD 4 zero)=true := by decide +kernel

set_option maxRecDepth 14000 in
set_option maxHeartbeats 0 in
theorem t5 : row true (inputs.getD 5 zero)=true := by decide +kernel

set_option maxRecDepth 14000 in
set_option maxHeartbeats 0 in
theorem t6 : row true (inputs.getD 6 zero)=true := by decide +kernel

set_option maxRecDepth 14000 in
set_option maxHeartbeats 0 in
theorem t7 : row true (inputs.getD 7 zero)=true := by decide +kernel

set_option maxRecDepth 14000 in
set_option maxHeartbeats 0 in
theorem t8 : row true (inputs.getD 8 zero)=true := by decide +kernel

theorem rowst : inputs.all (row true)=true := by
  unfold inputs
  simp only [List.all_cons,List.all_nil,Bool.and_eq_true]
  exact ⟨t0,t1,t2,t3,t4,t5,t6,t7,t8,True.intro⟩
end Raw

namespace Raw
open PublicFloor Trace Inputs Verification
open Node (four four_ok sameB same_ok)
open Reduced (root entry)
open Load (Board)

theorem initial_ok {u m} (low : Lower u inputs graph m)
    (rest : ∀ k∈seeds u, closed u m (cap u-1) (entry (root k) 1 0)) :
    closed u m (cap u) first := by
  have pass : inputs.all (row u)=true := by cases u with
                                             | false => exact rowsf
                                             | true => exact rowst
  have safe : Cuts.certified u first=true := by cases u <;> decide +kernel
  apply node (by decide +kernel : graph∉inputs)
  rintro ⟨d,a,b⟩ ka kb legal _ inA inB fresh
  have pair := List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp pass a inA) b inB) d (opsOf_mem legal.1)
  rw [if_neg legal.2.2.2] at pair
  have branch := four_ok pair ka kb
  dsimp only [test] at branch
  split at branch
  · exact cofactor low (Cuts.extend safe legal.1 inA inB fresh) _ branch
  · split at branch
    · exact lost branch
    · obtain ⟨mem,match_⟩ := Bool.and_eq_true_iff.mp branch
      exact same_ok (rest _ (List.contains_iff_mem.mp mem)) match_

theorem ten_suffice
    (rest : ∀ u m, m ≤ cap u → Lower u inputs graph m → ∀ k∈seeds u,
      closed u m (cap u-1) (entry (root k) 1 0)) :
    ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C →
      PEqualNP.MetaComplexity.circuitFun 9 C=edge → 16≤C.size :=
  original (fun u m bound low => initial_ok low (rest u m bound low))
end Raw

namespace Master
open PublicFloor Verification Inputs

def valid (u : Bool) (i : Nat) :=
  let r := Reduced.root i
  (Reduced.mode r==u && decide (0<Reduced.count r 1) && Reduced.token r 1 0!=0) &&
    Node.sameB (Reduced.entry (Reduced.root i) 1 0) (Reduced.entry r 1 0) 0

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem initial : ∀ u : Bool, (Raw.seeds u).all (valid u)=true := by decide +kernel

theorem assembled
    (proof : ∀ i u, i∈Raw.seeds u → ∀ m, m≤Inputs.cap u → Lower u inputs graph m →
      Reduced.full (Reduced.root i) m 1) :
    ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C →
      PEqualNP.MetaComplexity.circuitFun 9 C=edge → 16≤C.size := by
  apply Raw.ten_suffice
  intro u m fit low i mem
  have row := List.all_eq_true.mp (initial u) i mem
  obtain ⟨both,same⟩ := Bool.and_eq_true_iff.mp row
  obtain ⟨left,tag⟩ := Bool.and_eq_true_iff.mp both
  obtain ⟨mode,sz⟩ := Bool.and_eq_true_iff.mp left
  have done_ := proof i u mem m fit low 0 (of_decide_eq_true sz) (bne_iff_ne.mp tag)
  unfold Reduced.budget at done_
  rw [beq_iff_eq.mp mode] at done_
  exact Node.same_ok done_ same
end Master

namespace Roots
open PublicFloor Replay

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem root3 {m} (low : Lower (Reduced.mode (Reduced.root 3)) inputs graph m) : Reduced.full (Reduced.root 3) m 1 := by
  apply levels_ok (ds:=[0,0,4,5,2]) low
  simp only [levels,tree,Nat.reducePow,Nat.reduceMul,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem root6 {m} (low : Lower (Reduced.mode (Reduced.root 6)) inputs graph m) : Reduced.full (Reduced.root 6) m 1 := by
  apply levels_ok (ds:=[0,0,4,2,0]) low
  simp only [levels,tree,Nat.reducePow,Nat.reduceMul,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem root7 {m} (low : Lower (Reduced.mode (Reduced.root 7)) inputs graph m) : Reduced.full (Reduced.root 7) m 1 := by
  apply levels_ok (ds:=[0,2,6,5,1,0]) low
  simp only [levels,tree,Nat.reducePow,Nat.reduceMul,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem root8 {m} (low : Lower (Reduced.mode (Reduced.root 8)) inputs graph m) : Reduced.full (Reduced.root 8) m 1 := by
  apply levels_ok (ds:=[0,0,3,2]) low
  simp only [levels,tree,Nat.reducePow,Nat.reduceMul,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem root9 {m} (low : Lower (Reduced.mode (Reduced.root 9)) inputs graph m) : Reduced.full (Reduced.root 9) m 1 := by
  apply levels_ok (ds:=[0,1,5,4]) low
  simp only [levels,tree,Nat.reducePow,Nat.reduceMul,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem root10 {m} (low : Lower (Reduced.mode (Reduced.root 10)) inputs graph m) : Reduced.full (Reduced.root 10) m 1 := by
  apply levels_ok (ds:=[0,1,5,5,3,0,0,0,0]) low
  simp only [levels,tree,Nat.reducePow,Nat.reduceMul,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem root11 {m} (low : Lower (Reduced.mode (Reduced.root 11)) inputs graph m) : Reduced.full (Reduced.root 11) m 1 := by
  apply levels_ok (ds:=[0,0,3,2,0]) low
  simp only [levels,tree,Nat.reducePow,Nat.reduceMul,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem root26 {m} (low : Lower (Reduced.mode (Reduced.root 26)) inputs graph m) : Reduced.full (Reduced.root 26) m 1 := by
  apply levels_ok (ds:=[0,0,3,3,0]) low
  simp only [levels,tree,Nat.reducePow,Nat.reduceMul,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem root30 {m} (low : Lower (Reduced.mode (Reduced.root 30)) inputs graph m) : Reduced.full (Reduced.root 30) m 1 := by
  apply levels_ok (ds:=[0,0,4,4,0]) low
  simp only [levels,tree,Nat.reducePow,Nat.reduceMul,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem root31 {m} (low : Lower (Reduced.mode (Reduced.root 31)) inputs graph m) : Reduced.full (Reduced.root 31) m 1 := by
  apply levels_ok (ds:=[0,0,2,2]) low
  simp only [levels,tree,Nat.reducePow,Nat.reduceMul,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel

theorem all_circuits : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C →
    PEqualNP.MetaComplexity.circuitFun 9 C=edge → 16≤C.size := by
  apply Master.assembled
  intro i u mem m bound low
  cases u with
  | false =>
    simp [Raw.seeds] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact root3 low
    · exact root6 low
    · exact root7 low
    · exact root8 low
    · exact root9 low
    · exact root10 low
    · exact root11 low
  | true =>
    simp [Raw.seeds] at mem
    rcases mem with rfl|rfl|rfl
    · exact root26 low
    · exact root30 low
    · exact root31 low
end Roots

end PEqualNP.Outside.L_meta_670_aux

theorem PEqualNP.Outside.L_meta_670 : ¬ PEqualNP.MetaComplexity.HasCircuitSize 9 (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) 15 := by
  rintro ⟨C,fan,sz,e⟩
  have floor_ := PEqualNP.Outside.L_meta_670_aux.Roots.all_circuits C fan (funext e)
  omega

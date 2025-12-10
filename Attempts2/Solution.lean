import Mathlib

open scoped BigOperators

open Matrix

namespace Solution

variable {p : ℕ} [Fact p.Prime]

/-- `partialSumsDistinct l` asserts that the running sums of `l` are pairwise distinct. -/
def partialSumsDistinct (l : List (ZMod p)) : Prop :=
  (l.scanl (· + ·) (0 : ZMod p)).tail.Nodup

namespace NullstellensatzSetup

open Finset

open scoped Nat

noncomputable section

variable (n : ℕ)

private def sigmaToProd : (Σ _ : ℕ, ℕ) ↪ ℕ × ℕ :=
  ⟨fun ij => (ij.1, ij.2), by
    intro a b h
    cases a
    cases b
    cases h
    rfl⟩

private def withFst (i : ℕ) : ℕ ↪ ℕ × ℕ :=
  ⟨fun j => (i, j), by
    intro a b h
    cases h
    rfl⟩

private def withSnd (j : ℕ) : ℕ ↪ ℕ × ℕ :=
  ⟨fun i => (i, j), by
    intro a b h
    cases h
    rfl⟩

/-- all pairs `(i, j)` with `0 ≤ i < j ≤ n` and `j - i ≥ 2`. -/
def blockPairs : Finset (ℕ × ℕ) :=
  (((Finset.range n).sigma fun i => Finset.Icc (i + 2) n).map (sigmaToProd))

/-- target multi-index for the block part. -/
noncomputable def blockTarget : Fin n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun k : Fin n => n - 1 - (k : ℕ)

/-- target multi-index for the Vandermonde part. -/
noncomputable def vandTarget : Fin n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun k : Fin n => (k : ℕ)

/-- target exponent for the entire polynomial. -/
noncomputable def target : Fin n →₀ ℕ := blockTarget (n := n) + vandTarget (n := n)

/-- doubled Vandermonde target used for the refined obstruction. -/
noncomputable def newTarget : Fin n →₀ ℕ := vandTarget (n := n) + vandTarget (n := n)

@[simp] lemma blockTarget_apply (n : ℕ) (k : Fin n) :
    blockTarget (n := n) k = n - 1 - (k : ℕ) := by
  classical
  rfl

@[simp] lemma vandTarget_apply (n : ℕ) (k : Fin n) :
    vandTarget (n := n) k = (k : ℕ) := by
  classical
  rfl

@[simp] lemma target_apply (n : ℕ) (k : Fin n) :
    target (n := n) k = n - 1 := by
  classical
  have hk : (k : ℕ) ≤ n - 1 := Nat.le_pred_of_lt k.2
  simp [target, blockTarget_apply, vandTarget_apply, Nat.sub_add_cancel hk]

@[simp] lemma newTarget_apply (n : ℕ) (k : Fin n) :
    newTarget (n := n) k = 2 * (k : ℕ) := by
  classical
  simp [newTarget, vandTarget_apply, two_mul]

lemma mem_blockPairs {i j : ℕ} (n : ℕ) :
    (i, j) ∈ blockPairs (n := n) ↔ i < n ∧ i + 2 ≤ j ∧ j ≤ n := by
  classical
  unfold blockPairs
  constructor
  · intro hij
    rcases Finset.mem_map.mp hij with ⟨⟨i', j'⟩, hmem, hpair⟩
    rcases Finset.mem_sigma.mp hmem with ⟨hi, hj⟩
    rcases Finset.mem_Icc.mp hj with ⟨hij₂, hjn⟩
    have hi_eq : i' = i := congrArg Prod.fst hpair
    have hj_eq : j' = j := congrArg Prod.snd hpair
    subst hi_eq
    subst hj_eq
    exact ⟨Finset.mem_range.mp hi, hij₂, hjn⟩
  · intro h
    rcases h with ⟨hi, hij, hj⟩
    refine Finset.mem_map.mpr ?_
    refine ⟨⟨i, j⟩, ?_, rfl⟩
    refine Finset.mem_sigma.mpr ?_
    exact ⟨Finset.mem_range.mpr hi, Finset.mem_Icc.mpr ⟨hij, hj⟩⟩

lemma filter_blockPairs_fst (n i : ℕ) :
    ((blockPairs (n := n)).filter fun ij : ℕ × ℕ => ij.1 = i) =
      (Finset.Icc (i + 2) n).map (withFst i) := by
  classical
  ext ⟨a, b⟩
  constructor
  · intro h
    obtain ⟨hmem, ha⟩ := Finset.mem_filter.mp h
    subst ha
    obtain ⟨ha, hb₁, hb₂⟩ := (mem_blockPairs (n := n)).1 hmem
    refine Finset.mem_map.mpr ?_
    refine ⟨b, Finset.mem_Icc.mpr ⟨hb₁, hb₂⟩, ?_⟩
    simp [withFst]
  · intro h
    rcases Finset.mem_map.mp h with ⟨b, hb, hb'⟩
    cases hb'
    have hb' := Finset.mem_Icc.mp hb
    have hi₂ : i + 2 ≤ n := le_trans hb'.1 hb'.2
    have hi₁ : i + 1 < n := lt_of_lt_of_le (Nat.lt_succ_self _) hi₂
    have hi : i < n := lt_of_lt_of_le (Nat.lt_succ_self i) (Nat.le_of_lt hi₁)
    refine Finset.mem_filter.mpr ?_
    refine ⟨(mem_blockPairs (n := n)).2 ⟨hi, hb'.1, hb'.2⟩, rfl⟩

lemma card_blockPairs_fst (n i : ℕ) :
    ((blockPairs (n := n)).filter fun ij : ℕ × ℕ => ij.1 = i).card = n - 1 - i := by
  classical
  have h := congrArg Finset.card (filter_blockPairs_fst (n := n) (i := i))
  have hcard : (Finset.Icc (i + 2) n).card = n - 1 - i := by
    have hIcc : (Finset.Icc (i + 2) n).card = n - (i + 1) := by
      have := Nat.card_Icc (i + 2) n
      have hsucc : n + 1 - (i + 2) = n - (i + 1) := by
        simpa [Nat.succ_eq_add_one] using Nat.succ_sub_succ (n := n) (m := i + 1)
      simpa [hsucc]
        using this
    have hswap : n - (i + 1) = n - 1 - i := by
      simp [Nat.sub_sub, Nat.add_comm, Nat.add_left_comm]
    simpa [hswap] using hIcc
  simpa [Finset.card_map, hcard] using h

lemma add_two_le_iff_lt_pred {a b : ℕ} (hb : 2 ≤ b) :
    a + 2 ≤ b ↔ a < b - 1 := by
  have hb' : 1 ≤ b := le_trans (by decide : (1 : ℕ) ≤ 2) hb
  constructor
  · intro h
    have hsucc : (a + 1).succ ≤ (b - 1).succ := by
      simpa [Nat.succ_eq_add_one, Nat.sub_add_cancel hb'] using h
    have h' : a + 1 ≤ b - 1 := (Nat.succ_le_succ_iff).mp hsucc
    exact lt_of_lt_of_le (Nat.lt_succ_self _) h'
  · intro h
    have h' : a + 1 ≤ b - 1 := Nat.lt_iff_add_one_le.mp h
    have := Nat.succ_le_succ h'
    simpa [Nat.succ_eq_add_one, Nat.sub_add_cancel hb'] using this

lemma filter_blockPairs_snd (n j : ℕ) (hj : 2 ≤ j) (hj' : j ≤ n) :
    ((blockPairs (n := n)).filter fun ij : ℕ × ℕ => ij.2 = j) =
      (Finset.range (j - 1)).map (withSnd j) := by
  classical
  apply Finset.ext
  intro ij
  constructor
  · intro h
    obtain ⟨hmem, hj_eq⟩ := Finset.mem_filter.mp h
    obtain ⟨hi_lt, hij₂, hjn⟩ := (mem_blockPairs (n := n)).1 hmem
    have hi_range : ij.1 < j - 1 := by
      have : ij.1 + 2 ≤ j := by simpa [hj_eq] using hij₂
      exact (add_two_le_iff_lt_pred (a := ij.1) (hb := hj)).1 this
    refine Finset.mem_map.mpr ?_
    refine ⟨ij.1, Finset.mem_range.mpr hi_range, ?_⟩
    rcases ij with ⟨i, b⟩
    cases hj_eq
    simp [withSnd]
  · intro h
    rcases Finset.mem_map.mp h with ⟨i, hi, rfl⟩
    have hi_lt : i < j - 1 := Finset.mem_range.mp hi
    have hij₂ : i + 2 ≤ j :=
      (add_two_le_iff_lt_pred (a := i) (hb := hj)).2 hi_lt
    have hi_lt_n : i < n := by
      have hle : i + 2 ≤ n := le_trans hij₂ hj'
      have hi_succ_lt : i + 1 < n :=
        lt_of_lt_of_le (Nat.lt_succ_self (i + 1)) hle
      exact lt_trans (Nat.lt_succ_self _) hi_succ_lt
    refine Finset.mem_filter.mpr ?_
    refine ⟨(mem_blockPairs (n := n)).2 ⟨hi_lt_n, hij₂, hj'⟩, ?_⟩
    simp [withSnd]

lemma card_blockPairs_snd (n j : ℕ) (hj : 2 ≤ j) (hj' : j ≤ n) :
    ((blockPairs (n := n)).filter fun ij : ℕ × ℕ => ij.2 = j).card = j - 1 := by
  classical
  have h := filter_blockPairs_snd (n := n) (j := j) hj hj'
  simpa [h, Finset.card_map, Finset.card_range] using congrArg Finset.card h

lemma blockTarget_card_blockPairs (n : ℕ) (k : Fin n) :
    blockTarget (n := n) k =
      ((blockPairs (n := n)).filter fun ij : ℕ × ℕ => ij.1 = (k : ℕ)).card := by
  classical
  simpa [blockTarget_apply, eq_comm] using
    (card_blockPairs_fst (n := n) (i := (k : ℕ)))

def blockPairsSubtype (n : ℕ) := {ij : ℕ × ℕ // ij ∈ blockPairs (n := n)}

def blockAllowed (n : ℕ)
    (ij : blockPairsSubtype (n := n)) : Finset (Fin n) :=
  (Finset.univ.filter fun k : Fin n => ij.val.1 ≤ (k : ℕ) ∧ (k : ℕ) < ij.val.2)

lemma mem_blockAllowed {n : ℕ}
    (ij : blockPairsSubtype (n := n)) (k : Fin n) :
    k ∈ blockAllowed (n := n) ij ↔
      ij.val.1 ≤ (k : ℕ) ∧ (k : ℕ) < ij.val.2 := by
  classical
  unfold blockAllowed
  simpa [Finset.mem_filter, Finset.mem_univ]

noncomputable instance blockPairsSubtype.instFintype (n : ℕ) :
    Fintype (blockPairsSubtype (n := n)) := by
  classical
  have h :=
    (Fintype.ofFinset (blockPairs (n := n))
        (by intro ij; rfl)
      : Fintype {ij : ℕ × ℕ // ij ∈ blockPairs (n := n)})
  simpa [blockPairsSubtype] using h

instance blockPairsSubtype.instDecidableEq (n : ℕ) :
    DecidableEq (blockPairsSubtype (n := n)) := by
  classical
  infer_instance

structure BlockChoice (n : ℕ) where
  choose : blockPairsSubtype (n := n) → Fin n
  valid : ∀ ij, choose ij ∈ blockAllowed (n := n) ij

noncomputable instance (n : ℕ) : Fintype (BlockChoice (n := n)) := by
  classical
  let X := {f : blockPairsSubtype (n := n) → Fin n //
    ∀ ij, f ij ∈ blockAllowed (n := n) ij}
  refine Fintype.ofEquiv X ?_
  refine
    { toFun := fun f => ⟨f.1, f.2⟩
      invFun := fun c => ⟨c.choose, c.valid⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro f; cases f; rfl
  · intro c; cases c; rfl

namespace BlockChoice

variable {n}

lemma univ_blockSubtype (n : ℕ) :
    (Finset.univ : Finset (blockPairsSubtype (n := n))) =
      (blockPairs (n := n)).attach := by
  classical
  ext ij
  simp [blockPairsSubtype]

lemma card_filter_attach
    {α : Type*} [DecidableEq α]
    (s : Finset α) (p : α → Prop) [DecidablePred p] :
    ((s.attach).filter fun x : {a // a ∈ s} => p x.1).card =
      (s.filter p).card := by
  classical
  let f : ({a // a ∈ s}) ↪ α :=
    ⟨Subtype.val, by intro x y h; cases x; cases y; cases h; rfl⟩
  have hmap :
      ((s.attach).filter fun x : {a // a ∈ s} => p x.1).map f =
        s.filter p := by
    ext x; constructor
    · intro hx
      rcases Finset.mem_map.mp hx with ⟨x', hx', rfl⟩
      rcases Finset.mem_filter.mp hx' with ⟨-, hx_p⟩
      exact Finset.mem_filter.mpr ⟨x'.2, hx_p⟩
    · intro hx
      rcases Finset.mem_filter.mp hx with ⟨hx_mem, hx_p⟩
      refine Finset.mem_map.mpr ?_
      refine ⟨⟨x, hx_mem⟩, ?_, rfl⟩
      simp [Finset.mem_filter, hx_p]
  have := congrArg Finset.card hmap
  simpa [Finset.card_map] using this

def count (c : BlockChoice (n := n)) (k : Fin n) : ℕ :=
  ((Finset.univ.filter fun ij : blockPairsSubtype (n := n) => c.choose ij = k).card)

-- same-named structure; rely on mathlib's alignment hints
def countMulti (c : BlockChoice (n := n)) : Fin n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun k : Fin n => c.count k

@[simp] lemma countMulti_apply (c : BlockChoice (n := n)) (k : Fin n) :
    countMulti (n := n) c k = c.count k := by
  classical
  simp [countMulti]

@[ext] lemma ext {c d : BlockChoice (n := n)}
    (h : c.choose = d.choose) : c = d := by
  cases c
  cases d
  cases h
  simp

lemma choose_le_right (c : BlockChoice (n := n))
    (ij : blockPairsSubtype (n := n)) :
    ij.val.1 ≤ (c.choose ij : ℕ) :=
  ((mem_blockAllowed (n := n) ij (c.choose ij)).1 (c.valid ij)).1

lemma choose_lt_right (c : BlockChoice (n := n))
    (ij : blockPairsSubtype (n := n)) :
    (c.choose ij : ℕ) < ij.val.2 :=
  ((mem_blockAllowed (n := n) ij (c.choose ij)).1 (c.valid ij)).2

lemma count_eq_sum_indicator (c : BlockChoice (n := n)) (k : Fin n) :
    c.count k =
      ∑ ij : blockPairsSubtype (n := n),
        (if c.choose ij = k then (1 : ℕ) else 0) := by
  classical
  have h₁ :
      c.count k =
        ∑ ij ∈ Finset.univ.filter fun ij : blockPairsSubtype (n := n) => c.choose ij = k,
            (1 : ℕ) := by
    simpa [count] using
      (Finset.card_eq_sum_ones
        (s := Finset.univ.filter fun ij : blockPairsSubtype (n := n) => c.choose ij = k))
  have h₂ :
      ∑ ij ∈ Finset.univ.filter fun ij : blockPairsSubtype (n := n) => c.choose ij = k,
          (1 : ℕ)
        = ∑ ij : blockPairsSubtype (n := n),
            (if c.choose ij = k then (1 : ℕ) else 0) := by
    simpa using
      (Finset.sum_filter (s := (Finset.univ : Finset (blockPairsSubtype (n := n))))
        (p := fun ij : blockPairsSubtype (n := n) => c.choose ij = k)
        (f := fun _ : blockPairsSubtype (n := n) => (1 : ℕ)))
  simpa using h₁.trans h₂

lemma countMulti_eq_sum (c : BlockChoice (n := n)) :
    countMulti (n := n) c =
      (Finset.univ : Finset (blockPairsSubtype (n := n))).sum
        fun ij => Finsupp.single (c.choose ij) 1 := by
  classical
  ext k
  have hright :
      ((Finset.univ : Finset (blockPairsSubtype (n := n))).sum
        (fun ij => Finsupp.single (c.choose ij) 1)) k =
        ∑ ij : blockPairsSubtype (n := n),
          (if c.choose ij = k then (1 : ℕ) else 0) := by
    simpa [Finset.sum_apply]
  have hleft : countMulti (n := n) c k =
      ∑ ij : blockPairsSubtype (n := n),
        (if c.choose ij = k then (1 : ℕ) else 0) := by
    simp [countMulti_apply, count_eq_sum_indicator]
  exact hleft.trans hright.symm

def canonical (n : ℕ) : BlockChoice (n := n) := by
  classical
  refine
    { choose := fun ij => ⟨ij.val.1, (mem_blockPairs (n := n)).1 ij.property |>.1⟩
      valid := ?_ }
  intro ij
  obtain ⟨_, hij, _⟩ := (mem_blockPairs (n := n)).1 ij.property
  have hlt : (ij.val.1 : ℕ) < ij.val.2 :=
    lt_of_lt_of_le (Nat.lt_add_of_pos_right (n := ij.val.1)
        (by decide : (0 : ℕ) < 2)) hij
  simpa [blockAllowed, mem_blockAllowed, canonical] using And.intro (le_of_eq rfl) hlt

lemma canonical_choose_eq (ij : blockPairsSubtype (n := n)) (k : Fin n) :
    (canonical (n := n)).choose ij = k ↔ ij.val.1 = (k : ℕ) := by
  classical
  cases' k with k hk
  constructor
  · intro h
    have := congrArg (fun x : Fin n => (x : ℕ)) h
    simpa [canonical] using this
  · intro h
    subst h
    ext
    simp [canonical]

def terminal (n : ℕ) : BlockChoice (n := n) := by
  classical
  refine
    { choose := ?_ , valid := ?_ }
  · intro ij
    obtain ⟨_, _, hj⟩ := (mem_blockPairs (n := n)).1 ij.property
    have hpos : 0 < ij.val.2 :=
      lt_of_le_of_lt (Nat.zero_le _)
        (lt_of_lt_of_le
          (Nat.lt_add_of_pos_right (n := ij.val.1)
            (by decide : (0 : ℕ) < 2))
          ((mem_blockPairs (n := n)).1 ij.property |>.2.1))
    exact ⟨ij.val.2 - 1, lt_of_lt_of_le (Nat.pred_lt (Nat.ne_of_gt hpos)) hj⟩
  · intro ij
    have hij := (mem_blockPairs (n := n)).1 ij.property
    have hij_lt : ij.val.1 < ij.val.2 :=
      lt_of_lt_of_le
        (Nat.lt_add_of_pos_right (n := ij.val.1)
          (by decide : (0 : ℕ) < 2)) hij.2.1
    have hid_le : ij.val.1 ≤ ij.val.2 - 1 :=
      Nat.le_of_lt_succ (by simpa using hij_lt)
    have hpos : 0 < ij.val.2 := lt_of_le_of_lt (Nat.zero_le _) hij_lt
    have hj_lt : ij.val.2 - 1 < ij.val.2 := Nat.pred_lt (Nat.ne_of_gt hpos)
    have hchoice : ((terminal (n := n)).choose ij : ℕ) = ij.val.2 - 1 := rfl
    have hlt : ((terminal (n := n)).choose ij : ℕ) < ij.val.2 := by simpa [hchoice]
    have hle : ij.val.1 ≤ (terminal (n := n)).choose ij := by simpa [hchoice] using hid_le
    simpa [blockAllowed, mem_blockAllowed, hchoice] using And.intro hle hlt

lemma terminal_choose_eq (ij : blockPairsSubtype (n := n)) (k : Fin n) :
    (terminal (n := n)).choose ij = k ↔ ij.val.2 = (k : ℕ) + 1 := by
  classical
  cases' k with k hk
  constructor
  · intro h
    have hval := congrArg (fun x : Fin n => (x : ℕ)) h
    have hpos : 1 ≤ ij.val.2 :=
      le_trans (by decide : (1 : ℕ) ≤ 2)
        ((mem_blockPairs (n := n)).1 ij.property |>.2.1)
    have hchoice : ((terminal (n := n)).choose ij : ℕ) = ij.val.2 - 1 := rfl
    calc
      ij.val.2 = (ij.val.2 - 1) + 1 := Nat.sub_add_cancel hpos
      _ = (terminal (n := n)).choose ij + 1 := by simpa [hchoice]
      _ = k + 1 := by simpa using congrArg Nat.succ hval
  · intro h
    have hpos : 1 ≤ ij.val.2 :=
      le_trans (by decide : (1 : ℕ) ≤ 2)
        ((mem_blockPairs (n := n)).1 ij.property |>.2.1)
    have hval : ij.val.2 - 1 = k := by
      calc
        ij.val.2 - 1 = (k + 1) - 1 := by simpa [h, Nat.succ_eq_add_one]
        _ = k := Nat.add_sub_cancel _ _
    ext
    simp [terminal, hval]

lemma count_terminal (n : ℕ) (k : Fin n) :
    (terminal (n := n)).count k = (k : ℕ) := by
  classical
  unfold count
  have h₀ :
      (Finset.univ.filter fun ij : blockPairsSubtype (n := n) =>
          (terminal (n := n)).choose ij = k) =
        (blockPairs (n := n)).attach.filter fun ij => ij.1.2 = (k : ℕ) + 1 := by
    ext ij
    simp [univ_blockSubtype, terminal_choose_eq]
  have hcard := congrArg Finset.card h₀
  have hadd :
      ((blockPairs (n := n)).attach.filter fun ij => ij.1.2 = (k : ℕ) + 1).card =
        ((blockPairs (n := n)).filter fun ij => ij.2 = (k : ℕ) + 1).card := by
    simpa using
      (card_filter_attach
        (s := blockPairs (n := n))
        (p := fun ij : ℕ × ℕ => ij.2 = (k : ℕ) + 1))
  have hcount :
      (terminal (n := n)).count k =
        ((blockPairs (n := n)).filter fun ij => ij.2 = (k : ℕ) + 1).card := by
    simpa [count, h₀, hadd]
  by_cases hkzero : (k : ℕ) = 0
  · have hjzero :
        ((blockPairs (n := n)).filter fun ij : ℕ × ℕ => ij.2 = 1).card = 0 := by
      refine Finset.card_eq_zero.mpr ?_
      intro ij hij
      obtain ⟨hmem, hjval⟩ := Finset.mem_filter.mp hij
      obtain ⟨_, hij₂, _⟩ := (mem_blockPairs (n := n)).1 hmem
      have htwo : 2 ≤ ij.2 := le_trans (Nat.le_add_left _ _) hij₂
      have : 2 ≤ 1 := by simpa [hjval] using htwo
      exact (Nat.not_succ_le_self 1 this).elim
    simp [hcount, hkzero, hjzero]
  · have hkpos : 0 < (k : ℕ) := Nat.pos_of_ne_zero hkzero
    have hj₂ : 2 ≤ (k : ℕ) + 1 := Nat.succ_le_succ hkpos
    have hj_le : (k : ℕ) + 1 ≤ n := Nat.succ_le_of_lt k.2
    have hcard' :=
      card_blockPairs_snd (n := n) (j := (k : ℕ) + 1) hj₂ hj_le
    simpa [hcount, Nat.add_comm, Nat.add_left_comm, Nat.add_sub_cancel]
      using hcard'

lemma countMulti_terminal (n : ℕ) :
    countMulti (n := n) (terminal (n := n)) = vandTarget (n := n) := by
  classical
  ext k
  simp [countMulti_apply, count_terminal, vandTarget_apply]

lemma eq_terminal_of_countMulti
    (c : BlockChoice (n := n))
    (hc : countMulti (n := n) c = vandTarget (n := n)) :
    c.choose = (terminal (n := n)).choose := by
  classical
  have hcount : ∀ k : Fin n, c.count k = (k : ℕ) := by
    intro k
    simpa [countMulti_apply, vandTarget_apply] using congrArg (fun f => f k) hc
  have hmain :
      ∀ m, ∀ t ≤ m, ∀ ij : blockPairsSubtype (n := n),
          ij.val.2 + t = n → c.choose ij = (terminal (n := n)).choose ij := by
    refine Nat.rec ?base ?step
    · intro t ht ij hij
      have htzero : t = 0 := le_antisymm ht (Nat.zero_le _)
      subst htzero
      have hij₂ := (mem_blockPairs (n := n)).1 ij.property |>.2.1
      have hjtwo : 2 ≤ ij.val.2 := le_trans (Nat.le_add_left _ _) hij₂
      have hjn : ij.val.2 = n := by simpa using hij
      have hn_two : 2 ≤ n := by simpa [hjn]
      have hnpos : 0 < n := lt_of_le_of_lt (by decide : 0 < 2) hn_two
      let kfin : Fin n := ⟨n - 1, Nat.pred_lt (Nat.ne_of_gt hnpos)⟩
      let T := Finset.univ.filter fun x : blockPairsSubtype (n := n) => c.choose x = kfin
      let S := Finset.univ.filter fun x : blockPairsSubtype (n := n) => x.val.2 = n
      have hTcard : T.card = n - 1 := by
        dsimp [T]
        simpa [BlockChoice.count, kfin] using hcount kfin
      have hSattach :
          S = (blockPairs (n := n)).attach.filter fun ij => ij.1.2 = n := by
        ext x; simp [S, univ_blockSubtype]
      have hScard : S.card = n - 1 := by
        have hattach :=
          card_filter_attach
            (s := blockPairs (n := n))
            (p := fun ij : ℕ × ℕ => ij.2 = n)
        have hx := card_blockPairs_snd (n := n) (j := n) hn_two (Nat.le_of_eq rfl)
        simpa [hSattach] using hattach.trans hx
      have hsubset : T ⊆ S := by
        intro x hx
        have hxval : c.choose x = kfin := (Finset.mem_filter.mp hx).2
        have hxlt : (kfin : ℕ) < x.val.2 := by
          simpa [hxval] using BlockChoice.choose_lt_right (n := n) c x
        have hxge : n ≤ x.val.2 := Nat.succ_le_of_lt (by simpa [kfin] using hxlt)
        have hxle : x.val.2 ≤ n := (mem_blockPairs (n := n)).1 x.property |>.2.2
        have hxEq : x.val.2 = n := le_antisymm hxle hxge
        exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hx).1, hxEq⟩
      have hTS : T = S :=
        Finset.eq_of_subset_of_card_le hsubset (by simpa [hTcard, hScard])
      have : ij ∈ T := by
        have hij_in : ij ∈ S := by simp [S, hjn]
        simpa [hTS] using hij_in
      have hchoose : c.choose ij = kfin := (Finset.mem_filter.mp this).2
      have hterm : (terminal (n := n)).choose ij = kfin := by
        ext; simp [terminal, hjn, kfin]
      simpa [hterm] using hchoose
    · intro m IH t ht ij hij
      by_cases htm : t ≤ m
      · exact IH t htm ij hij
      · have hcase : t = m + 1 := by
          have := Nat.lt_or_eq_of_le ht
          rcases this with hlt | hEq
          · exact (htm (Nat.le_of_lt_succ hlt)).elim
          · simpa using hEq
        subst hcase
        have hm_le_n : m + 1 ≤ n := by
          have := Nat.le_add_left (m + 1) ij.val.2
          simpa [hij]
        set j := n - (m + 1)
        have hjle : j ≤ n := Nat.sub_le _ _
        have hjadd : j + (m + 1) = n := by
          simpa [j] using Nat.sub_add_cancel hm_le_n
        have hijval : ij.val.2 = j := by
          have := congrArg (fun x => x - (m + 1)) hij
          simpa [hjadd, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this
        have hij₂ := (mem_blockPairs (n := n)).1 ij.property |>.2.1
        have hjtwo : 2 ≤ j := by
          have htwo : 2 ≤ ij.val.2 := le_trans (Nat.le_add_left _ _) hij₂
          simpa [hijval] using htwo
        have hjpos : 0 < j := lt_of_le_of_lt (by decide : 0 < 2) hjtwo
        have hj_lt_n : j - 1 < n := by
          have hsucc : Nat.succ (j - 1) = j := Nat.succ_pred_eq_of_pos hjpos
          have : Nat.succ (j - 1) ≤ n := by simpa [hsucc] using hjle
          exact Nat.lt_of_succ_le this
        let kfin : Fin n := ⟨j - 1, hj_lt_n⟩
        let T := Finset.univ.filter fun x : blockPairsSubtype (n := n) => c.choose x = kfin
        let S := Finset.univ.filter fun x : blockPairsSubtype (n := n) => x.val.2 = j
        have hTcard : T.card = j - 1 := by
          dsimp [T]
          simpa [BlockChoice.count, kfin] using hcount kfin
        have hSattach :
            S = (blockPairs (n := n)).attach.filter fun x => x.1.2 = j := by
          ext x; simp [S, univ_blockSubtype]
        have hScard : S.card = j - 1 := by
          have hattach :=
            card_filter_attach
              (s := blockPairs (n := n))
              (p := fun ij : ℕ × ℕ => ij.2 = j)
          have hx := card_blockPairs_snd (n := n) (j := j) hjtwo hjle
          simpa [hSattach] using hattach.trans hx
        have hsubset : T ⊆ S := by
          intro x hx
          have hx_eq : c.choose x = kfin := (Finset.mem_filter.mp hx).2
          have hxlt : (kfin : ℕ) < x.val.2 := by
            simpa [hx_eq] using BlockChoice.choose_lt_right (n := n) c x
          have hxge : j ≤ x.val.2 := Nat.succ_le_of_lt (by simpa [kfin] using hxlt)
          have hxle : x.val.2 ≤ n := (mem_blockPairs (n := n)).1 x.property |>.2.2
          by_cases hx_eq_j : x.val.2 = j
          · exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hx).1, hx_eq_j⟩
          · have hxgt : j < x.val.2 := lt_of_le_of_ne hxge (by simpa [hx_eq_j])
            set t' := n - x.val.2
            have ht' : t' ≤ m := by
              have := Nat.sub_le_sub_left (Nat.succ_le_of_lt hxgt) n
              simpa [j, t'] using this
            have hsum : x.val.2 + t' = n := by
              have := Nat.add_sub_of_le hxle
              simpa [t'] using this.symm
            have hIH := IH t' ht' x hsum
            have hxterm : ((terminal (n := n)).choose x : ℕ) = x.val.2 - 1 := rfl
            have hkval : (kfin : ℕ) = j - 1 := rfl
            have hxge' : j ≤ x.val.2 - 1 := by
              have := Nat.succ_le_of_lt hxgt
              simpa [Nat.succ_eq_add_one] using this
            have hneq : (x.val.2 - 1) ≠ j - 1 := ne_of_gt hxge'
            have hxcontr : False := by
              have := congrArg (fun y : Fin n => (y : ℕ)) hIH
              simpa [hxterm, hkval, hneq] using this
            exact (hxcontr.elim)
        have hTS : T = S :=
          Finset.eq_of_subset_of_card_le hsubset (by simpa [hTcard, hScard])
        have hij_in : ij ∈ S := by
          simp [S, hijval]
        have : ij ∈ T := by simpa [hTS] using hij_in
        have hchoose : c.choose ij = kfin := (Finset.mem_filter.mp this).2
        have hterm : (terminal (n := n)).choose ij = kfin := by
          ext; simp [terminal, hijval, kfin]
        simpa [hterm] using hchoose
  funext ij
  have hle : ij.val.2 ≤ n := (mem_blockPairs (n := n)).1 ij.property |>.2.2
  have hsum : ij.val.2 + (n - ij.val.2) = n := Nat.add_sub_of_le hle
  have := hmain n (n - ij.val.2) (Nat.sub_le _ _) ij hsum
  simpa using this

lemma countMulti_eq_vandTarget_iff (c : BlockChoice (n := n)) :
    countMulti (n := n) c = vandTarget (n := n) ↔
      c = terminal (n := n) := by
  constructor
  · intro hc
    apply BlockChoice.ext
    simpa using eq_terminal_of_countMulti (n := n) c hc
  · intro hc
    simpa [hc] using countMulti_terminal (n := n)

lemma choose_mem_allowed (c : BlockChoice (n := n))
    (ij : blockPairsSubtype (n := n)) :
    c.choose ij ∈ blockAllowed (n := n) ij := c.valid ij

lemma choose_mem_pi (c : BlockChoice (n := n)) :
    c.choose ∈ Fintype.piFinset (fun ij : blockPairsSubtype (n := n) =>
      blockAllowed (n := n) ij) := by
  classical
  refine (Fintype.mem_piFinset).2 ?_
  intro ij
  exact choose_mem_allowed (n := n) c ij

def ofPiChoice
    (f : blockPairsSubtype (n := n) → Fin n)
    (hf : f ∈ Fintype.piFinset (fun ij : blockPairsSubtype (n := n) =>
      blockAllowed (n := n) ij)) : BlockChoice (n := n) :=
  { choose := f
    valid := by
      classical
      intro ij
      have := (Fintype.mem_piFinset).1 hf ij
      simpa [blockAllowed, Finset.mem_filter, Finset.mem_univ, mem_blockAllowed]
        using this }

lemma ofPiChoice_choose
    (f : blockPairsSubtype (n := n) → Fin n)
    (hf : f ∈ Fintype.piFinset (fun ij : blockPairsSubtype (n := n) =>
      blockAllowed (n := n) ij)) :
    (ofPiChoice (n := n) f hf).choose = f := rfl

section AnyRing

variable {R : Type*} [CommRing R]

namespace BlockChoice

def choicePoly (c : BlockChoice (n := n)) : MvPolynomial (Fin n) R :=
  ∏ ij : blockPairsSubtype (n := n), MvPolynomial.X (c.choose ij)

@[simp] lemma choicePoly_apply (c : BlockChoice (n := n)) :
    choicePoly (n := n) (R := R) c =
      ∏ ij : blockPairsSubtype (n := n), MvPolynomial.X (c.choose ij) := rfl

end BlockChoice

lemma prod_X_eq_monomial {β : Type*} [DecidableEq β]
    (s : Finset β) (f : β → Fin n) :
    (∏ b ∈ s, (MvPolynomial.X (f b) : MvPolynomial (Fin n) R)) =
      MvPolynomial.monomial
        (s.sum fun b => Finsupp.single (f b) 1)
        (1 : R) := by
  classical
  refine Finset.induction_on s ?base ?step
  · simp
  · intro a s ha hs
    simp [Finset.prod_insert, Finset.sum_insert, ha, hs,
      add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc]

lemma choicePoly_eq_monomial (c : BlockChoice (n := n)) :
    BlockChoice.choicePoly (n := n) (R := R) c =
      MvPolynomial.monomial (countMulti (n := n) c) (1 : R) := by
  classical
  simpa [BlockChoice.choicePoly, countMulti_eq_sum]
    using prod_X_eq_monomial
      (s := (Finset.univ : Finset (blockPairsSubtype (n := n))))
      (f := fun ij => c.choose ij)

lemma coeff_choicePoly (c : BlockChoice (n := n))
    (m : Fin n →₀ ℕ) :
    MvPolynomial.coeff m
        (BlockChoice.choicePoly (n := n) (R := R) c) =
      (if countMulti (n := n) c = m then (1 : R) else 0) := by
  classical
  simp [choicePoly_eq_monomial]

lemma coeff_choicePoly_blockTarget (c : BlockChoice (n := n)) :
    MvPolynomial.coeff (blockTarget (n := n))
        (BlockChoice.choicePoly (n := n) (R := R) c) =
      (if countMulti (n := n) c = blockTarget (n := n)
        then (1 : R) else 0) := by
  classical
  simpa [coeff_choicePoly]

lemma countMulti_eq_target_iff (c : BlockChoice (n := n)) :
    countMulti (n := n) c = blockTarget (n := n) ↔
      c = canonical (n := n) := by
  constructor
  · intro hc
    apply BlockChoice.ext
    exact BlockChoice.eq_canonical_of_countMulti (n := n) c hc
  · intro hc
    simpa [hc] using countMulti_canonical (n := n)

lemma coeff_blockPoly_target :
    MvPolynomial.coeff (blockTarget (n := n))
        (blockPoly (n := n) (R := R)) = (1 : R) := by
  classical
  have h := congrArg
      (MvPolynomial.coeff (blockTarget (n := n)))
      (blockPoly_eq_sum_blockChoice (n := n) (R := R))
  have hcoeff :
      MvPolynomial.coeff (blockTarget (n := n))
          (blockPoly (n := n) (R := R)) =
        ∑ c : BlockChoice (n := n),
          (if c = canonical (n := n) then (1 : R) else 0) := by
    simpa [coeff_choicePoly_blockTarget, countMulti_eq_target_iff]
      using h
  have hsum :
      (∑ c : BlockChoice (n := n),
        (if c = canonical (n := n) then (1 : R) else 0)) = (1 : R) := by
    classical
    refine Finset.sum_eq_single (canonical (n := n))
      (fun c _ hne => by simp [hne])
      (by simp)
  exact hcoeff.trans hsum

lemma coeff_vandPoly_target :
    MvPolynomial.coeff (vandTarget (n := n))
        (vandPoly (n := n) (R := R)) = (1 : R) := by
  classical
  have h := congrArg
      (MvPolynomial.coeff (vandTarget (n := n)))
      (vandPoly_eq_det (n := n) (R := R))
  have hcoeff :
      MvPolynomial.coeff (vandTarget (n := n))
          (vandPoly (n := n) (R := R)) =
        ∑ σ : Equiv.Perm (Fin n),
          (σ.sign : R) *
            (if σ = Equiv.refl _ then (1 : R) else 0) := by
    simpa [Matrix.det_apply, coeff_perm_term, Finset.mul_sum, Finset.sum_mul] using h
  have hsum :
      (∑ σ : Equiv.Perm (Fin n),
        (σ.sign : R) * (if σ = Equiv.refl _ then (1 : R) else 0)) = (1 : R) := by
    refine Finset.sum_eq_single (Equiv.refl (Fin n))
      (fun σ _ hσ => by simp [hσ])
      (by simp)
  exact hcoeff.trans hsum


lemma count_canonical (n : ℕ) (k : Fin n) :
    (canonical (n := n)).count k = blockTarget (n := n) k := by
  classical
  unfold count
  have h₀ :
      (Finset.univ.filter fun ij : blockPairsSubtype (n := n) =>
          (canonical (n := n)).choose ij = k) =
        (blockPairs (n := n)).attach.filter fun ij => ij.1 = (k : ℕ) := by
    ext ij
    simp [univ_blockSubtype, canonical_choose_eq]
  have h₁ := congrArg Finset.card h₀
  have h₂ :
      ((blockPairs (n := n)).attach.filter fun ij => ij.1 = (k : ℕ)).card =
        ((blockPairs (n := n)).filter fun ij => ij.1 = (k : ℕ)).card := by
    simpa using
      (card_filter_attach
        (s := blockPairs (n := n))
        (p := fun ij : ℕ × ℕ => ij.1 = (k : ℕ)))
  simpa [blockTarget_card_blockPairs, h₂] using h₁

lemma countMulti_canonical (n : ℕ) :
    countMulti (n := n) (canonical (n := n)) = blockTarget (n := n) := by
  classical
  ext k
  simp [countMulti_apply, count_canonical]

lemma eq_canonical_of_counts
    (c : BlockChoice (n := n)) (hc : ∀ k, c.count k = blockTarget (n := n) k) :
    c.choose = (canonical (n := n)).choose := by
  classical
  have hmain : ∀ i, ∀ ij : blockPairsSubtype (n := n), ij.val.1 = i →
      c.choose ij = (canonical (n := n)).choose ij := by
    refine fun i => Nat.strong_rec_on i ?_
    intro i IH ij hij
    have hi_lt : i < n := (mem_blockPairs (n := n)).1 ij.property |>.1
    set kfin : Fin n := ⟨i, hi_lt⟩
    let T := Finset.univ.filter fun x : blockPairsSubtype (n := n) => c.choose x = kfin
    let S := Finset.univ.filter fun x : blockPairsSubtype (n := n) => x.val.1 = i
    have hTcard : T.card = blockTarget (n := n) kfin := by
      dsimp [T]
      simpa [BlockChoice.count] using hc kfin
    have hScard : S.card = blockTarget (n := n) kfin := by
      dsimp [S]
      have h₀ :
          S = (blockPairs (n := n)).attach.filter fun ij => ij.1 = i := by
        ext x; simp [S, univ_blockSubtype]
      have hattach : S.card = ((blockPairs (n := n)).filter fun ij => ij.1 = i).card := by
        have hcard :=
          (card_filter_attach (s := blockPairs (n := n))
            (p := fun ij : ℕ × ℕ => ij.1 = i))
        have :
            S.card =
              ((blockPairs (n := n)).attach.filter fun ij => ij.1 = i).card := by
          simpa [h₀]
        exact this.trans hcard
      have htarget :
          ((blockPairs (n := n)).filter fun ij => ij.1 = i).card =
            blockTarget (n := n) kfin := by
        simpa [blockTarget_card_blockPairs, kfin]
      exact hattach.trans htarget
    have hsubset : T ⊆ S := by
      intro x hx
      have hx_eq : c.choose x = kfin := (Finset.mem_filter.mp hx).2
      have hx_le : x.val.1 ≤ i := by
        simpa [hx_eq] using BlockChoice.choose_le_right (n := n) c x
      have hx_not_lt : ¬ x.val.1 < i := by
        intro hxlt
        have hx_case := IH _ hxlt x rfl
        have hxcanon : (canonical (n := n)).choose x = kfin := by
          simpa [hx_case] using hx_eq
        have hxval : x.val.1 = i := by
          simpa [canonical, kfin] using congrArg Fin.val hxcanon
        have : i < i := by simpa [hxval] using hxlt
        exact (Nat.lt_irrefl _ this)
      have hx_eq_nat : x.val.1 = i :=
        le_antisymm hx_le (not_lt.mp hx_not_lt)
      simpa [S, hx_eq_nat]
    have hST : T = S :=
      Finset.eq_of_subset_of_card_le hsubset (by simpa [hTcard, hScard])
    have hmem : ij ∈ S := by
      simp [S, hij]
    have hij_in_T : ij ∈ T := by
      simpa [hST] using hmem
    have hij_eq : c.choose ij = kfin := (Finset.mem_filter.mp hij_in_T).2
    simpa [canonical, hij, kfin] using hij_eq
  funext ij
  exact hmain _ ij rfl

lemma eq_canonical_of_countMulti
    (c : BlockChoice (n := n))
    (hc : countMulti (n := n) c = blockTarget (n := n)) :
    c.choose = (canonical (n := n)).choose :=
  eq_canonical_of_counts (n := n) c (by
    intro k; simpa [countMulti_apply] using congrArg (fun α => α k) hc)

end BlockChoice

lemma coeff_blockFactor_single (ij : ℕ × ℕ) (k : Fin n) :
    MvPolynomial.coeff (Finsupp.single k 1)
        (blockFactor (n := n) (R := R) ij) =
      (if ij.1 ≤ (k : ℕ) ∧ (k : ℕ) < ij.2 then (1 : R) else 0) := by
  classical
  have :
      ∀ k', MvPolynomial.coeff (Finsupp.single k 1) (MvPolynomial.X k') =
          (if k' = k then (1 : R) else 0) := by
    intro k'
    by_cases hk' : k' = k
    · subst hk'
      simp
    · simp [hk']
  simp [blockFactor, Finset.mem_univ, this, apply_ite MvPolynomial.coeff]

lemma coeff_blockFactor_first (ij : ℕ × ℕ) (hi : ij.1 < n)
    (hij : ij ∈ blockPairs (n := n)) :
    MvPolynomial.coeff (Finsupp.single ⟨ij.1, hi⟩ 1)
        (blockFactor (n := n) (R := R) ij) = 1 := by
  classical
  obtain ⟨_, hij₂, _⟩ := (mem_blockPairs (n := n)).1 hij
  have hlt : (ij.1 : ℕ) < ij.2 := lt_of_lt_of_le
      (Nat.lt_add_of_pos_right (n := ij.1) (by decide : (0 : ℕ) < 2)) hij₂
  have hcond : ij.1 ≤ ((⟨ij.1, hi⟩ : Fin n) : ℕ) ∧
      ((⟨ij.1, hi⟩ : Fin n) : ℕ) < ij.2 := by
    simp [hi, hlt]
  simpa [coeff_blockFactor_single, hcond]

/-- Cardinality of the set of all block pairs. -/
lemma card_blockPairs (n : ℕ) : #(blockPairs (n := n)) = n * (n - 1) / 2 := by
  classical
  unfold blockPairs
  have h₁ :
      (∑ i ∈ Finset.range n, (n + 1 - (i + 2))) =
        ∑ i ∈ Finset.range n, (n - 1 - i) := by
    refine Finset.sum_congr rfl ?_
    intro i _
    have := Nat.add_sub_add_right n (i + 1) 1
    simp [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] at this
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this
  have h₂ :
      (∑ i ∈ Finset.range n, (n - 1 - i)) = ∑ i ∈ Finset.range n, i := by
    simpa using (Finset.sum_range_reflect (fun i => (i : ℕ)) n)
  have h₃ : ∑ i ∈ Finset.range n, i = n * (n - 1) / 2 := Finset.sum_range_id _
  simpa [Finset.card_map, Finset.card_sigma, Nat.card_Icc, h₁, h₂, h₃,
    Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]




/-- Factor corresponding to the block `(i, j)` with `j - i ≥ 2`. -/
def blockFactor (ij : ℕ × ℕ) : MvPolynomial (Fin n) R :=
  ∑ k ∈ (Finset.univ : Finset (Fin n)),
    if ij.1 ≤ (k : ℕ) ∧ (k : ℕ) < ij.2 then MvPolynomial.X k else 0

lemma blockFactor_eq_filter (ij : ℕ × ℕ) :
    blockFactor (n := n) (R := R) ij =
      ∑ k ∈ ((Finset.univ : Finset (Fin n)).filter fun k : Fin n =>
        ij.1 ≤ (k : ℕ) ∧ (k : ℕ) < ij.2),
        MvPolynomial.X k := by
  classical
  refine Finset.sum_congr rfl ?_
  intro k hk
  by_cases h : ij.1 ≤ (k : ℕ) ∧ (k : ℕ) < ij.2
  · simp [blockFactor, Finset.mem_univ, h]
  · simp [blockFactor, Finset.mem_univ, h]

lemma blockFactor_subtype
    (ij : blockPairsSubtype (n := n)) :
    blockFactor (n := n) (R := R) ij.val =
      ∑ k ∈ blockAllowed (n := n) ij, MvPolynomial.X k := by
  classical
  simpa [blockAllowed] using
    (blockFactor_eq_filter (n := n) (R := R) ij.val)

lemma blockPoly_eq_sum_pi :
    blockPoly (n := n) (R := R) =
      ∑ f ∈
        Fintype.piFinset (fun ij : blockPairsSubtype (n := n) =>
          blockAllowed (n := n) ij),
          ∏ ij : blockPairsSubtype (n := n),
            MvPolynomial.X (f ij) := by
  classical
  have hprod := blockPoly_eq_prodSubtype (n := n) (R := R)
  have hfac :
      (fun ij : blockPairsSubtype (n := n) => blockFactor (n := n) (R := R) ij.val) =
        fun ij => ∑ k ∈ blockAllowed (n := n) ij, MvPolynomial.X k := by
    funext ij; simpa [blockFactor_subtype (n := n) (R := R) ij]
  have h := (Finset.prod_univ_sum (t := fun ij : blockPairsSubtype (n := n) =>
      blockAllowed (n := n) ij)
      (f := fun ij k => MvPolynomial.X k))
  simpa [hprod, hfac] using h

lemma blockPoly_eq_sum_blockChoice :
    blockPoly (n := n) (R := R) =
      ∑ c : BlockChoice (n := n),
        BlockChoice.choicePoly (n := n) (R := R) c := by
  classical
  have h := blockPoly_eq_sum_pi (n := n) (R := R)
  refine h.trans ?_
  have hsum :
      (∑ f ∈ Fintype.piFinset
          (fun ij : blockPairsSubtype (n := n) => blockAllowed (n := n) ij),
            ∏ ij : blockPairsSubtype (n := n), MvPolynomial.X (f ij)) =
        ∑ c ∈ (Finset.univ : Finset (BlockChoice (n := n))),
          BlockChoice.choicePoly (n := n) (R := R) c := by
    refine Finset.sum_bij
      (fun f hf => ofPiChoice (n := n) f hf)
      (fun f hf => by simp)
      (fun f hf => by
        simp [BlockChoice.choicePoly, ofPiChoice_choose])
      (fun f₁ hf₁ f₂ hf₂ hfeq => by
        ext ij
        simpa [ofPiChoice_choose] using congrArg (fun c => c.choose ij) hfeq)
      (by
        intro c _
        refine ⟨c.choose, choose_mem_pi (n := n) c, ?_⟩
        ext ij
        simp [ofPiChoice_choose]))
  simpa using hsum

lemma blockPoly_eq_sum_monomial :
    blockPoly (n := n) (R := R) =
      ∑ c : BlockChoice (n := n),
        MvPolynomial.monomial (countMulti (n := n) c) (1 : R) := by
  classical
  simpa [BlockChoice.choicePoly_eq_monomial]
    using blockPoly_eq_sum_blockChoice (n := n) (R := R)

/-- Product of all block factors. -/
def blockPoly : MvPolynomial (Fin n) R :=
  ∏ ij ∈ blockPairs (n := n), blockFactor (n := n) (R := R) ij

lemma blockPoly_eq_prodSubtype :
    blockPoly (n := n) (R := R) =
      ∏ ij : blockPairsSubtype (n := n),
        blockFactor (n := n) (R := R) ij.val := by
  classical
  unfold blockPoly
  have := (Finset.prod_attach (s := blockPairs (n := n))
      fun ij => blockFactor (n := n) (R := R) ij).symm
  have hattach :
      (blockPairs (n := n)).attach =
        (Finset.univ : Finset (blockPairsSubtype (n := n))) := by
    ext ij
    simp [blockPairsSubtype]
  simpa [hattach]

/-- Vandermonde polynomial. -/
def vandPoly : MvPolynomial (Fin n) R :=
  ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (MvPolynomial.X j - MvPolynomial.X i)

lemma vandPoly_eq_det :
    vandPoly (n := n) (R := R) =
      (Matrix.vandermonde fun i : Fin n => MvPolynomial.X i).det := by
  classical
  simpa [vandPoly] using
    (Matrix.det_vandermonde (fun i : Fin n => MvPolynomial.X i)).symm

lemma vandPoly_eq_sum_perm :
    vandPoly (n := n) (R := R) =
      ∑ σ : Equiv.Perm (Fin n),
        (σ.sign : R) *
          MvPolynomial.monomial (vandPermMulti (n := n) σ) (1 : R) := by
  classical
  have h := vandPoly_eq_det (n := n) (R := R)
  refine h.trans ?_
  have := Matrix.det_apply (Matrix.vandermonde fun i : Fin n => MvPolynomial.X i)
  simpa [Matrix.det_apply, prod_perm_eq_monomial]

lemma obstructionPoly_eq_double_sum :
    obstructionPoly (n := n) (R := R) =
      ∑ c : BlockChoice (n := n),
        ∑ σ : Equiv.Perm (Fin n),
          (σ.sign : R) *
            MvPolynomial.monomial
              (countMulti (n := n) c + vandPermMulti (n := n) σ) (1 : R) := by
  classical
  simp [obstructionPoly, blockPoly_eq_sum_monomial (n := n) (R := R),
    vandPoly_eq_sum_perm, Finset.mul_sum, Finset.sum_mul,
    Finset.sum_sigma', add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc,
    MvPolynomial.monomial_mul]

/-- Combined obstruction polynomial. -/
def obstructionPoly : MvPolynomial (Fin n) R :=
  blockPoly (n := n) (R := R) * vandPoly (n := n) (R := R)

def vandPermMulti (σ : Equiv.Perm (Fin n)) : Fin n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun k : Fin n => (σ⁻¹ k : ℕ)

lemma vandPermMulti_apply (σ : Equiv.Perm (Fin n)) (k : Fin n) :
    vandPermMulti (n := n) σ k = (σ⁻¹ k : ℕ) := by
  classical
  simp [vandPermMulti]

lemma vandPermMulti_eq_vandTarget_iff (σ : Equiv.Perm (Fin n)) :
    vandPermMulti (n := n) σ = vandTarget (n := n) ↔ σ = Equiv.refl _ := by
  classical
  constructor
  · intro h
    have hfun := congrArg (fun f => Finsupp.equivFunOnFinite f) h
    have hval : ∀ k, (σ⁻¹ k : ℕ) = (k : ℕ) := by
      intro k
      have := congrArg (fun g => g k) hfun
      simpa [vandPermMulti, vandTarget] using this
    have hfin : ∀ k, σ⁻¹ k = k := fun k => Fin.ext (hval k)
    have hσ : ∀ k, σ k = k := by
      intro k
      have := congrArg σ (hfin (σ k))
      simpa using this
    ext k
    exact hσ k
  · intro h
    subst h
    ext k
    simp [vandPermMulti, vandTarget]

lemma sum_single_perm (σ : Equiv.Perm (Fin n)) :
    (Finset.univ : Finset (Fin n)).sum
        (fun i : Fin n => Finsupp.single (σ i) (i : ℕ)) =
      vandPermMulti (n := n) σ := by
  classical
  ext k
  have hs :
      ((Finset.univ : Finset (Fin n)).sum
          (fun i => Finsupp.single (σ i) (i : ℕ)) k) =
        ∑ i : Fin n, (if σ i = k then (i : ℕ) else 0) := by
    simp [Finset.sum_apply, Finsupp.single]
  have hσ :
      (∑ i : Fin n, (if σ i = k then (i : ℕ) else 0)) = (σ⁻¹ k : ℕ) := by
    refine Finset.sum_eq_single (σ⁻¹ k) ?_ ?_
    · intro i _ hi
      have hneq : σ i ≠ k := by
        intro hk
        apply hi
        have := congrArg σ⁻¹ hk
        simpa using this
      simp [hneq]
    · intro hnot
      exact (hnot (Finset.mem_univ _)).elim
    · simp
  simpa [hs, hσ, vandPermMulti]

lemma prod_perm_eq_monomial (σ : Equiv.Perm (Fin n)) :
    (∏ i : Fin n, (MvPolynomial.X (σ i) : MvPolynomial (Fin n) R) ^ (i : ℕ)) =
      MvPolynomial.monomial (vandPermMulti (n := n) σ) (1 : R) := by
  classical
  have := prod_X_pow_eq_monomial (s := (Finset.univ : Finset (Fin n)))
      (f := fun i : Fin n => σ i) (g := fun i => (i : ℕ))
  simpa [Finset.mem_univ, sum_single_perm, vandPermMulti]
    using this

lemma coeff_perm_term (σ : Equiv.Perm (Fin n)) :
    MvPolynomial.coeff (vandTarget (n := n))
        (∏ i : Fin n, (MvPolynomial.X (σ i) : MvPolynomial (Fin n) R) ^ (i : ℕ)) =
      (if σ = Equiv.refl _ then (1 : R) else 0) := by
  classical
  simp [prod_perm_eq_monomial, vandPermMulti_eq_vandTarget_iff,
    apply_ite MvPolynomial.coeff, MvPolynomial.coeff_monomial]

lemma prod_X_pow_eq_monomial {β : Type*} [DecidableEq β]
    (s : Finset β) (f : β → Fin n) (g : β → ℕ) :
    (∏ b ∈ s, (MvPolynomial.X (f b) : MvPolynomial (Fin n) R) ^ (g b)) =
      MvPolynomial.monomial
        (s.sum fun b => Finsupp.single (f b) (g b))
        (1 : R) := by
  classical
  refine Finset.induction_on s ?base ?step
  · simp
  · intro a s ha hs
    simp [Finset.prod_insert, Finset.sum_insert, ha, hs, monomial_mul,
      add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc,
      MvPolynomial.X_pow_eq_monomial]

lemma blockTarget_degree (n : ℕ) :
    (blockTarget (n := n) : Fin n →₀ ℕ).degree = n * (n - 1) / 2 := by
  classical
  cases n with
  | zero => simp [blockTarget]
  | succ n =>
    have hsum :
        (∑ k : Fin n.succ, blockTarget (n := n.succ) k) =
          ∑ k ∈ Finset.range n.succ, (n.succ - 1 - k) := by
      simpa [blockTarget_apply] using
        (Fin.sum_univ_eq_sum_range fun k : Fin n.succ => blockTarget (n := n.succ) k)
    have hswap :
        (∑ k ∈ Finset.range n.succ, (n.succ - 1 - k)) =
          ∑ k ∈ Finset.range n.succ, k := by
      simpa using (Finset.sum_range_reflect (fun k => (k : ℕ)) n.succ)
    have hsum' := hsum.trans (by simpa [hswap, Finset.sum_range_id] : _)
    simpa [Finsupp.degree_eq_sum, hsum', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

lemma vandTarget_degree (n : ℕ) :
    (vandTarget (n := n) : Fin n →₀ ℕ).degree = n * (n - 1) / 2 := by
  classical
  cases n with
  | zero => simp [vandTarget]
  | succ n =>
    have hsum :
        (∑ k : Fin n.succ, vandTarget (n := n.succ) k) =
          ∑ k ∈ Finset.range n.succ, k := by
      simpa [vandTarget_apply] using
        (Fin.sum_univ_eq_sum_range fun k : Fin n.succ => vandTarget (n := n.succ) k)
    simpa [Finsupp.degree_eq_sum, hsum, Finset.sum_range_id, Nat.add_comm, Nat.add_left_comm,
      Nat.add_assoc]

lemma target_degree (n : ℕ) :
    (target (n := n) : Fin n →₀ ℕ).degree = n * (n - 1) := by
  classical
  have hsum :
      (∑ k : Fin n, target (n := n) k) =
        (∑ k : Fin n, blockTarget (n := n) k) + ∑ k : Fin n, vandTarget (n := n) k := by
    simp [target, Finset.sum_add_distrib]
  have hb := blockTarget_degree (n := n)
  have hv := vandTarget_degree (n := n)
  have hsum_deg :
      (∑ k : Fin n, target (n := n) k) = (n * (n - 1) / 2) + (n * (n - 1) / 2) := by
    simp [hsum, hb, hv]
  simpa [Finsupp.degree_eq_sum, hsum, hb, hv, two_mul, Nat.mul_add, Nat.add_comm,
    Nat.add_left_comm, Nat.add_assoc] using hsum_deg

end AnyRing

end -- noncomputable section

end NullstellensatzSetup

end Solution

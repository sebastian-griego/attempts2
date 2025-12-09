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

/-- all pairs `(i, j)` with `0 ≤ i < j ≤ n` and `j - i ≥ 2`. -/
def blockPairs : Finset (ℕ × ℕ) :=
  (((Finset.range n).sigma fun i => Finset.Icc (i + 2) n).map (sigmaToProd))

lemma mem_blockPairs {i j : ℕ} (n : ℕ) :
    (i, j) ∈ blockPairs (n := n) ↔ i < n ∧ i + 2 ≤ j ∧ j ≤ n := by
  classical
  unfold blockPairs
  constructor
  · intro hij
    simp only [Finset.mem_map, Finset.mem_sigma, sigmaToProd, Function.Embedding.coeFn_mk,
      Prod.mk.injEq, exists_prop, true_and, heq_eq_eq, exists_exists_and_eq_and] at hij
    rcases hij with ⟨⟨i', j'⟩, hi', rfl, rfl⟩
    rcases hi' with ⟨hi, hj⟩
    exact ⟨by simpa using hi, hj.1, hj.2⟩
  · intro h
    rcases h with ⟨hi, hij, hj⟩
    refine ⟨⟨⟨i, hi⟩, ?_⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · simpa using hij
    · simpa using hj

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
    refine ⟨b, ⟨hb₁, hb₂⟩, ?_⟩
    simp [withFst]
  · intro h
    rcases Finset.mem_map.mp h with ⟨b, hb, hb'⟩
    cases hb'
    have hi : i < n :=
      lt_of_lt_of_le (Nat.lt_add_of_pos_right i (by decide : (0 < (2 : ℕ))))
        (le_trans hb.1 hb.2)
    refine Finset.mem_filter.mpr ?_
    refine ⟨(mem_blockPairs (n := n)).2 ⟨hi, hb.1, hb.2⟩, rfl⟩

lemma card_blockPairs_fst (n i : ℕ) :
    ((blockPairs (n := n)).filter fun ij : ℕ × ℕ => ij.1 = i).card = n - 1 - i := by
  classical
  simpa [filter_blockPairs_fst, Finset.card_map, Nat.card_Icc, Nat.add_comm, Nat.add_left_comm,
    Nat.add_assoc]

lemma blockTarget_card_blockPairs (n : ℕ) (k : Fin n) :
    blockTarget (n := n) k =
      ((blockPairs (n := n)).filter fun ij : ℕ × ℕ => ij.1 = (k : ℕ)).card := by
  classical
  simpa [blockTarget_apply] using
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

instance blockPairsSubtype.instFintype (n : ℕ) :
    Fintype (blockPairsSubtype (n := n)) :=
  (blockPairs (n := n)).fintypeSubtype

instance blockPairsSubtype.instDecidableEq (n : ℕ) :
    DecidableEq (blockPairsSubtype (n := n)) :=
  Classical.decEq _

structure BlockChoice (n : ℕ) where
  choose : blockPairsSubtype (n := n) → Fin n
  valid : ∀ ij, ij.val.1 ≤ (choose ij : ℕ) ∧ (choose ij : ℕ) < ij.val.2

noncomputable instance (n : ℕ) : Fintype (BlockChoice (n := n)) := by
  classical
  let X := {f : blockPairsSubtype (n := n) → Fin n //
    ∀ ij, ij.val.1 ≤ (f ij : ℕ) ∧ (f ij : ℕ) < ij.val.2}
  refine Fintype.ofEquiv X ?_
  refine
    { toFun := fun c => ⟨c.choose, c.valid⟩
      invFun := fun f => ⟨f.1, f.2⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro c; cases c; rfl
  · intro f; cases f; rfl

namespace BlockChoice

variable {n}

lemma univ_blockSubtype (n : ℕ) :
    (Finset.univ : Finset (blockPairsSubtype (n := n))) =
      (blockPairs (n := n)).attach := by
  classical
  ext ij
  simp [blockPairsSubtype]

lemma filter_attach (s : Finset (ℕ × ℕ)) (p : (ℕ × ℕ) → Prop)
    [DecidablePred p] :
    s.attach.filter (fun ij => p ij.1) = (s.filter p).attach := by
  classical
  ext ij
  simp [Finset.mem_filter, Finset.mem_attach]

def canonical (n : ℕ) : BlockChoice (n := n) := by
  classical
  refine ⟨?_, ?_⟩
  · intro ij
    exact ⟨ij.val.1, (mem_blockPairs (n := n)).1 ij.property |>.1⟩
  · intro ij
    obtain ⟨_, hij, _⟩ := (mem_blockPairs (n := n)).1 ij.property
    refine ⟨?_, ?_⟩
    · exact le_of_eq rfl
    · exact lt_of_lt_of_le
        (Nat.lt_add_of_pos_right _ (by decide : (0 < (2 : ℕ)))) hij

lemma canonical_choose_eq (ij : blockPairsSubtype (n := n)) (k : Fin n) :
    (canonical (n := n)).choose ij = k ↔ ij.val.1 = (k : ℕ) := by
  classical
  cases k
  simp [canonical]

# align  -- help the elaborator grasp the type
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

lemma count_eq_sum_indicator (c : BlockChoice (n := n)) (k : Fin n) :
    c.count k =
      ∑ ij : blockPairsSubtype (n := n),
        (if c.choose ij = k then (1 : ℕ) else 0) := by
  classical
  have h₁ :
      c.count k =
        ∑ ij ∈ Finset.univ.filter fun ij : blockPairsSubtype (n := n) => c.choose ij = k,
            (1 : ℕ) := by
    simp [count, Finset.card_eq_sum_ones]
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
  simp [countMulti_apply, count_eq_sum_indicator, Finset.sum_apply]

lemma choose_mem_allowed (c : BlockChoice (n := n))
    (ij : blockPairsSubtype (n := n)) :
    c.choose ij ∈ blockAllowed (n := n) ij := by
  classical
  have h := (c.valid ij)
  simpa [blockAllowed, Finset.mem_filter, Finset.mem_univ, mem_blockAllowed]
    using h

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
    simpa [filter_attach] using
      (Finset.card_attach ((blockPairs (n := n)).filter fun ij => ij.1 = (k : ℕ)))
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
        simpa [h₀, filter_attach]
          using (Finset.card_attach ((blockPairs (n := n)).filter fun ij => ij.1 = i))
      have htarget :
          ((blockPairs (n := n)).filter fun ij => ij.1 = i).card =
            blockTarget (n := n) kfin := by
        simpa [blockTarget_card_blockPairs, kfin]
      exact hattach.trans htarget
    have hsubset : T ⊆ S := by
      intro x hx
      have hx_eq : c.choose x = kfin := (Finset.mem_filter.mp hx).2
      have hx_le : x.val.1 ≤ i := by
        simpa [hx_eq] using (c.valid x).1
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
      (Nat.lt_add_of_pos_right ij.1 (by decide : (0 < (2 : ℕ)))) hij₂
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


section AnyRing

variable {R : Type*} [CommRing R]

namespace BlockChoice

@[simp] lemma choicePoly_apply (c : BlockChoice (n := n)) :
    choicePoly (n := n) (R := R) c =
      ∏ ij : blockPairsSubtype (n := n), MvPolynomial.X (c.choose ij) := rfl

def choicePoly (c : BlockChoice (n := n)) : MvPolynomial (Fin n) R :=
  ∏ ij : blockPairsSubtype (n := n), MvPolynomial.X (c.choose ij)

end BlockChoice

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

/-- target multi-index for the block part. -/
def blockTarget : Fin n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun k : Fin n => n - 1 - (k : ℕ)

/-- target multi-index for the Vandermonde part. -/
def vandTarget : Fin n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun k : Fin n => (k : ℕ)

/-- target exponent for the entire polynomial. -/
def target : Fin n →₀ ℕ := blockTarget (n := n) + vandTarget (n := n)

@[simp] lemma blockTarget_apply (n : ℕ) (k : Fin n) :
    blockTarget (n := n) k = n - 1 - (k : ℕ) := by
  classical
  rfl

@[simp] lemma vandTarget_apply (n : ℕ) (k : Fin n) :
    vandTarget (n := n) k = (k : ℕ) := by
  classical
  rfl

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

lemma target_apply (n : ℕ) (k : Fin n) :
    target (n := n) k = n - 1 := by
  classical
  simp [target, blockTarget_apply, vandTarget_apply]

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

end NullstellensatzSetup

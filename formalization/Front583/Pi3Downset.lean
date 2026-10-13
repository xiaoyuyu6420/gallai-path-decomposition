import Front583.Pi3L2b

/-! # Front583.Pi3Downset — the general-form downset theorem for L2(b)
(a plain, fully tactic-proved theorem)

**Scope** (lemma 1 "downset property" of the packing-table account, task (2)
of the follow-up module plan): the downset lemma "every immediate predecessor
of a feasible point is feasible" (paper side: a two-line restriction argument;
machine-checked over 120 x 330 x 2 points with zero violations; carried as a
table-domain native_decide certificate in Pi3Uni.lean) is upgraded here to a
**fully proved theorem in general form**:

    pkg_downset: for arbitrary (S, s, side, d, d', i), if slot d i >= 1 and
    d' = d with slot i decremented (all other slots equal), then
    pkg S sc ban d = true -> pkg S sc ban d' = true

Proof structure (plain tactics throughout; no native_decide, no sorry):
bit tools (testBit_add_two_pow: if bit k is clear, adding 2^k flips only bit
k) -> pkgGo_mono (success is preserved when the occupancy masks shrink, in the
pointwise Bitsub sense) -> pkgGo_agree (identical slot values on the block
list give identical behaviour) -> pkgGo_fuel_mono (fuel monotonicity) ->
pkgGo_ds (the main induction: the success-transfer for a single-slot
decrement, with the head-block-i boundary case handled by "unfold one step +
agree + mono + fuel monotonicity") -> pkg_downset (assembly: filter equality
of block lists + mutual induction with the zero-demand-block deletion lemma
pkgGo_drop0).

Trust note: the axiom profile is [propext, Classical.choice, Quot.sound] —
Lean's three standard logical axioms — with **no sorryAx and no
Lean.ofReduceBool**; this is a plain proof (in contrast to the
native_decide machine-certificate grade of Pi3L2b/Pi3Uni). Coverage: the
universally quantified form over arbitrary (S, sc, ban, d, d', i), not
restricted to the 120-orbit / Sigma d <= 7 table domain. Provenance: the
semantics of labA174._pkg -> Pi3L2b.pkg (the Lean reimplementation) -> this
file. -/


/-! ## Bit tools -/

/-- If bit k of n is clear, adding 2^k flips only bit k. -/
theorem testBit_add_two_pow (n k : Nat) (h : n.testBit k = false) :
    (n + 2 ^ k).testBit k = true ∧ ∀ i, i ≠ k → (n + 2 ^ k).testBit i = n.testBit i := by
  induction k generalizing n with
  | zero =>
    have h0 : n % 2 = 0 := by
      simpa [Nat.testBit_zero] using h
    refine ⟨?_, ?_⟩
    · simp only [Nat.testBit_zero]
      have : (n + 1) % 2 = 1 := by omega
      simp [this]
    · intro i hi
      rcases Nat.eq_zero_or_pos i with hz | hp
      · omega
      · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
        simp only [Nat.testBit_succ]
        have hdiv : (n + 1) / 2 = n / 2 := by omega
        simp only [hdiv]
  | succ k ih =>
    have hshift : (n / 2).testBit k = false := by rw [← Nat.testBit_succ n k]; exact h
    obtain ⟨h1, h2⟩ := ih (n / 2) hshift
    have hpow : n + 2 ^ (k + 1) = n + 2 * 2 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
    have hsplit : n + 2 * 2 ^ k = 2 * (n / 2 + 2 ^ k) + n % 2 := by
      have := Nat.div_add_mod n 2; omega
    have hdiv : (n + 2 * 2 ^ k) / 2 = n / 2 + 2 ^ k := by omega
    refine ⟨?_, ?_⟩
    · rw [hpow, Nat.testBit_succ, hdiv]
      exact h1
    · intro i hi
      rcases Nat.eq_zero_or_pos i with hz | hp
      · subst hz
        rw [hpow, hsplit, Nat.testBit_zero, Nat.testBit_zero]
        have hmod : (2 * (n / 2 + 2 ^ k) + n % 2) % 2 = n % 2 := by omega
        simp [hmod]
      · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
        rw [hpow, Nat.testBit_succ, hdiv, Nat.testBit_succ]
        rcases Nat.lt_or_ge j k with hlt | hge
        · exact h2 j (by omega)
        · rcases Nat.eq_or_lt_of_le hge with he | hgt
          · exact absurd hi (by omega)
          · exact h2 j (by omega)

/-- Pointwise bit-containment. -/
def Bitsub (a b : Nat) : Prop := ∀ i, a.testBit i = true → b.testBit i = true

theorem bitsub_refl (a : Nat) : Bitsub a a := fun _ hi => hi

theorem bitsub_clear (a b k : Nat) (h : Bitsub a b) (h2 : b.testBit k = false) :
    a.testBit k = false := by
  cases ha : a.testBit k with
  | false => rfl
  | true => rw [h k ha] at h2; exact absurd h2 (by simp)

theorem bitsub_add (a b k : Nat) (hc : b.testBit k = false) (h : Bitsub a b) :
    Bitsub a (b + 2 ^ k) := by
  intro i hi
  by_cases he : i = k
  · subst he
    exact (testBit_add_two_pow b i hc).1
  · rw [(testBit_add_two_pow b k hc).2 i he]; exact h i hi

theorem bitsub_add_both (a b k : Nat) (ha : a.testBit k = false) (hb : b.testBit k = false)
    (h : Bitsub a b) : Bitsub (a + 2 ^ k) (b + 2 ^ k) := by
  intro i hi
  by_cases he : i = k
  · subst he
    exact (testBit_add_two_pow b i hb).1
  · rw [(testBit_add_two_pow a k ha).2 i he] at hi
    rw [(testBit_add_two_pow b k hb).2 i he]
    exact h i hi

/-- testBit bridge: the `== 0` bit test inside pkgGo equals the negation of testBit. -/
theorem bit0 (n k : Nat) : (((n >>> k) &&& 1 : Nat) == 0) = !(n.testBit k) := by
  have h1 : (n >>> k) &&& 1 = (n >>> k) % 2 := Nat.and_one_is_mod _
  have h2 : n.testBit k = decide ((n >>> k) % 2 = 1) := by simp [Nat.testBit]
  rw [h1, h2]
  by_cases hm : (n >>> k) % 2 = 0
  · simp [hm]
  · have h3 : (n >>> k) % 2 = 1 := by omega
    simp [h3]

/-! ## Structural lemmas on pkgGo -/

/-- Fuel monotonicity: success at a larger fuel persists. -/
theorem pkgGo_fuel_mono (S sc : Nat) (ban : Bool) (d : Nat) :
    ∀ f B uc uk y cnt, pkgGo f S sc ban d B uc uk y cnt = true →
      ∀ f', f ≤ f' → pkgGo f' S sc ban d B uc uk y cnt = true := by
  intro f
  induction f with
  | zero =>
    intro B uc uk y cnt h _'
    exact absurd h (by simp [pkgGo])
  | succ g ih =>
    intro B uc uk y cnt h f' hf'
    cases f' with
    | zero => omega
    | succ g' =>
      have hgle : g ≤ g' := by omega
      cases B with
      | nil => exact h
      | cons j B' =>
        simp only [pkgGo] at h ⊢
        by_cases hc : (cnt == slot d j) = true
        · rw [if_pos hc] at h ⊢
          exact ih B' uc uk 0 0 h g' hgle
        · rw [if_neg hc] at h ⊢
          by_cases hy : 7 ≤ y
          · rw [if_pos hy] at h
            exact absurd h (by simp)
          · rw [if_neg hy] at h ⊢
            rcases Bool.or_eq_true_iff.mp h with hcell | hskip
            · rcases Bool.and_eq_true_iff.mp hcell with ⟨hCK, hrec⟩
              exact Bool.or_eq_true_iff.mpr
                (Or.inl (Bool.and_eq_true_iff.mpr ⟨hCK,
                  ih (j :: B') (uc + 2 ^ y) (uk + 2 ^ ((y + 7 - slot sc j % 7) % 7))
                    (y + 1) (cnt + 1) hrec g' hgle⟩))
            · exact Bool.or_eq_true_iff.mpr
                (Or.inr (ih (j :: B') uc uk (y + 1) cnt hskip g' hgle))

/-- Monotonicity: success is preserved when the occupancy masks shrink (pointwise). -/
theorem pkgGo_mono (S sc : Nat) (ban : Bool) (d : Nat) :
    ∀ f B uc1 uk1 uc2 uk2 y cnt,
      Bitsub uc2 uc1 → Bitsub uk2 uk1 →
      pkgGo f S sc ban d B uc1 uk1 y cnt = true →
      pkgGo f S sc ban d B uc2 uk2 y cnt = true := by
  intro f
  induction f with
  | zero =>
    intro B uc1 uk1 uc2 uk2 y cnt _ _ h
    exact absurd h (by simp [pkgGo])
  | succ g ih =>
    intro B uc1 uk1 uc2 uk2 y cnt hsub hsubk h
    cases B with
    | nil => exact h
    | cons j B' =>
      simp only [pkgGo] at h ⊢
      by_cases hc : (cnt == slot d j) = true
      · rw [if_pos hc] at h ⊢
        exact ih B' uc1 uk1 uc2 uk2 0 0 hsub hsubk h
      rw [if_neg hc] at h ⊢
      by_cases hy : 7 ≤ y
      · rw [if_pos hy] at h
        exact absurd h (by simp)
      rw [if_neg hy] at h ⊢
      rcases Bool.or_eq_true_iff.mp h with hcell | hskip
      · rcases Bool.and_eq_true_iff.mp hcell with ⟨hCK, hrec⟩
        rw [bit0, bit0] at hCK
        obtain ⟨hL, hR⟩ := Bool.and_eq_true_iff.mp hCK
        obtain ⟨hLL, hBan⟩ := Bool.and_eq_true_iff.mp hL
        obtain ⟨hS, hU⟩ := Bool.and_eq_true_iff.mp hLL
        obtain ⟨hK, hK0⟩ := Bool.and_eq_true_iff.mp hR
        have hU' : uc1.testBit y = false := by
          cases hh : uc1.testBit y with
          | false => rfl
          | true => rw [hh] at hU; exact absurd hU (by simp)
        have hK' : uk1.testBit ((y + 7 - slot sc j % 7) % 7) = false := by
          cases hh : uk1.testBit ((y + 7 - slot sc j % 7) % 7) with
          | false => rfl
          | true => rw [hh] at hK; exact absurd hK (by simp)
        have hbU2 : uc2.testBit y = false := bitsub_clear uc2 uc1 y hsub hU'
        have hbK2 : uk2.testBit ((y + 7 - slot sc j % 7) % 7) = false :=
          bitsub_clear uk2 uk1 ((y + 7 - slot sc j % 7) % 7) hsubk hK'
        have hCK2c : ((((S >>> y) &&& 1) == 1 && !(uc1.testBit y)) &&
              !(ban && y == slot sc j)) &&
            ((!uk1.testBit ((y + 7 - slot sc j % 7) % 7)) &&
              !(ban && (y + 7 - slot sc j % 7) % 7 == 0)) = true := by
          rw [hS, hU, hBan, hK, hK0]
          rfl
        have hsuby : Bitsub (uc2 + 2 ^ y) (uc1 + 2 ^ y) :=
          bitsub_add_both uc2 uc1 y hbU2 hU' hsub
        have hsubx : Bitsub (uk2 + 2 ^ ((y + 7 - slot sc j % 7) % 7))
            (uk1 + 2 ^ ((y + 7 - slot sc j % 7) % 7)) :=
          bitsub_add_both uk2 uk1 ((y + 7 - slot sc j % 7) % 7) hbK2 hK' hsubk
        have hrec2 := ih (j :: B') (uc1 + 2 ^ y) (uk1 + 2 ^ ((y + 7 - slot sc j % 7) % 7))
          (uc2 + 2 ^ y) (uk2 + 2 ^ ((y + 7 - slot sc j % 7) % 7)) (y + 1) (cnt + 1)
          hsuby hsubx hrec
        rw [bit0, bit0]
        refine Bool.or_eq_true_iff.mpr (Or.inl (Bool.and_eq_true_iff.mpr ⟨?_, hrec2⟩))
        rw [hS, hbU2, hBan, hbK2, hK0]
        rfl
      · exact Bool.or_eq_true_iff.mpr
          (Or.inr (ih (j :: B') uc1 uk1 uc2 uk2 (y + 1) cnt hsub hsubk hskip))

/-- Agreement lemma: identical slot values on the block list give identical behaviour. -/
theorem pkgGo_agree (S sc : Nat) (ban : Bool) (d d' : Nat) :
    ∀ f B uc uk y cnt, (∀ j ∈ B, slot d j = slot d' j) →
      pkgGo f S sc ban d B uc uk y cnt = pkgGo f S sc ban d' B uc uk y cnt := by
  intro f
  induction f with
  | zero => intro B uc uk y cnt _; rfl
  | succ g ih =>
    intro B uc uk y cnt hag
    cases B with
    | nil => rfl
    | cons j B' =>
      have hj : slot d j = slot d' j := hag j (by simp)
      have hB : ∀ m ∈ B', slot d m = slot d' m := fun m hm =>
        hag m (List.mem_cons_of_mem _ hm)
      simp only [pkgGo, hj]
      rw [ih B' uc uk 0 0 hB]
      rw [ih (j :: B') (uc + 2 ^ y) (uk + 2 ^ ((y + 7 - slot sc j % 7) % 7)) (y + 1) (cnt + 1) hag]
      rw [ih (j :: B') uc uk (y + 1) cnt hag]

/-- Zero-demand-block wander-failure lemma: a zero-demand block fails whenever cnt is non-zero. -/
theorem pkgGo_wander_fail (S sc : Nat) (ban : Bool) (d j : Nat) (h0 : slot d j = 0) :
    ∀ f B uc uk y cnt, cnt ≠ 0 → pkgGo f S sc ban d (j :: B) uc uk y cnt = false := by
  intro f
  induction f with
  | zero => intro B uc uk y cnt _; rfl
  | succ g ih =>
    intro B uc uk y cnt hcnt
    simp only [pkgGo, h0]
    rw [if_neg (by intro hc2; exact hcnt (by simpa using hc2))]
    by_cases hy : 7 ≤ y
    · rw [if_pos hy]
    · rw [if_neg hy]
      rw [ih B (uc + 2 ^ y) (uk + 2 ^ ((y + 7 - slot sc j % 7) % 7)) (y + 1) (cnt + 1)
        (by omega), ih B uc uk (y + 1) cnt (by omega), Bool.and_false, Bool.or_false]

/-- **Zero-demand-block deletion**: when slot d i = 0, the block i can be
removed from the block list wholesale.
P0 = the main assertion at the (0,0) entry state; P1 = the intra-block
recursion invariant for a head block other than i (mutual induction). -/
theorem pkgGo_drop0 (S sc : Nat) (ban : Bool) (d i : Nat) (h0 : slot d i = 0) :
    ∀ f, (∀ B uc uk, pkgGo f S sc ban d B uc uk 0 0 = true →
            pkgGo f S sc ban d (B.filter (fun j => !(j == i))) uc uk 0 0 = true) ∧
          (∀ B uc uk y cnt, (match B with
                              | [] => True
                              | j :: _ => (j == i) = false) →
             pkgGo f S sc ban d B uc uk y cnt = true →
             pkgGo f S sc ban d (B.filter (fun j => !(j == i))) uc uk y cnt = true) := by
  intro f
  induction f with
  | zero =>
    constructor
    · intro B uc uk h
      exact absurd h (by simp [pkgGo])
    · intro B uc uk y cnt _ h
      exact absurd h (by simp [pkgGo])
  | succ g ih =>
    obtain ⟨ih0, ih1⟩ := ih
    constructor
    · -- P0(g+1)
      intro B uc uk h
      cases B with
      | nil => exact h
      | cons j B' =>
        simp only [pkgGo] at h
        by_cases hj : (j == i) = true
        · have hj0 : slot d j = 0 := by
            rw [show j = i from by simpa using hj]
            exact h0
          have hc : ((0 == slot d j) = true) := by rw [hj0]; simp
          rw [if_pos hc] at h
          rw [List.filter_cons_of_neg (by simpa using hj)]
          exact pkgGo_fuel_mono S sc ban d g
            (B'.filter (fun j => !(j == i))) uc uk 0 0 (ih0 B' uc uk h) (g + 1) (by omega)
        · rw [List.filter_cons_of_pos (by simpa using hj)]
          simp only [pkgGo]
          by_cases hc : ((0 == slot d j) = true)
          · rw [if_pos hc] at h ⊢
            exact ih0 B' uc uk h
          · rw [if_neg hc, if_neg (show ¬(7 ≤ 0) from by omega)] at h ⊢
            rcases Bool.or_eq_true_iff.mp h with hcell | hskip
            · rcases Bool.and_eq_true_iff.mp hcell with ⟨hCK, hrec⟩
              have hrec2 := ih1 (j :: B') (uc + 2 ^ 0)
                (uk + 2 ^ ((0 + 7 - slot sc j % 7) % 7)) (0 + 1) (0 + 1) (by simp [hj]) hrec
              rw [List.filter_cons_of_pos (by simpa using hj)] at hrec2
              exact Bool.or_eq_true_iff.mpr (Or.inl (Bool.and_eq_true_iff.mpr ⟨hCK, hrec2⟩))
            · have hskip2 := ih1 (j :: B') uc uk (0 + 1) 0 (by simp [hj]) hskip
              rw [List.filter_cons_of_pos (by simpa using hj)] at hskip2
              exact Bool.or_eq_true_iff.mpr (Or.inr hskip2)
    · -- P1(g+1)
      intro B uc uk y cnt hhead h
      cases B with
      | nil => exact h
      | cons j B' =>
        have hj : (j == i) = false := by simpa using hhead
        rw [List.filter_cons_of_pos (by simpa using hj)]
        simp only [pkgGo] at h ⊢
        by_cases hc : (cnt == slot d j) = true
        · rw [if_pos hc] at h ⊢
          exact ih0 B' uc uk h
        · rw [if_neg hc] at h ⊢
          by_cases hy : 7 ≤ y
          · rw [if_pos hy] at h
            exact absurd h (by simp)
          rw [if_neg hy] at h ⊢
          rcases Bool.or_eq_true_iff.mp h with hcell | hskip
          · rcases Bool.and_eq_true_iff.mp hcell with ⟨hCK, hrec⟩
            have hrec2 := ih1 (j :: B') (uc + 2 ^ y)
              (uk + 2 ^ ((y + 7 - slot sc j % 7) % 7)) (y + 1) (cnt + 1) (by simp [hj]) hrec
            rw [List.filter_cons_of_pos (by simpa using hj)] at hrec2
            exact Bool.or_eq_true_iff.mpr (Or.inl (Bool.and_eq_true_iff.mpr ⟨hCK, hrec2⟩))
          · have hskip2 := ih1 (j :: B') uc uk (y + 1) cnt (by simp [hj]) hskip
            rw [List.filter_cons_of_pos (by simpa using hj)] at hskip2
            exact Bool.or_eq_true_iff.mpr (Or.inr hskip2)
/-! ## The main induction: success transfer under a single-slot decrement -/

theorem pkgGo_ds (S sc : Nat) (ban : Bool) (d d' i : Nat)
    (h1 : slot d' i + 1 = slot d i)
    (h2 : ∀ j, j ≠ i → slot d' j = slot d j) :
    ∀ f B uc uk y cnt,
      (∀ j ∈ B, 1 ≤ slot d j) →
      ((B.filter (fun j => j == i)).length ≤ 1) →
      (match B with
       | [] => True
       | j :: _ => cnt + 1 ≤ slot d j ∨ j ≠ i) →
      pkgGo f S sc ban d B uc uk y cnt = true →
      pkgGo f S sc ban d' B uc uk y cnt = true := by
  intro f
  induction f with
  | zero =>
    intro B uc uk y cnt _ _ _ h
    exact absurd h (by simp [pkgGo])
  | succ g ih =>
    intro B uc uk y cnt hpos hlen hentry h
    cases B with
    | nil => exact h
    | cons j B' =>
      have hjpos : 1 ≤ slot d j := hpos j (by simp)
      have hpos' : ∀ m ∈ B', 1 ≤ slot d m := fun m hm =>
        hpos m (List.mem_cons_of_mem _ hm)
      by_cases hij : j = i
      · subst hij
        rcases hentry with hcnt | hne'
        · -- cnt + 1 <= slot d j, and j not in B' (main path)
          have hnotin : j ∉ B' := by
            intro hmem
            have hf : ((j :: B').filter (fun k => k == j)) =
                j :: (B'.filter (fun k => k == j)) :=
              List.filter_cons_of_pos (by simp)
            have h2x := hlen
            rw [hf] at h2x
            cases hf2 : B'.filter (fun k => k == j) with
            | nil =>
              have h5' : j ∈ B'.filter (fun k => k == j) :=
                List.mem_filter.mpr ⟨hmem, by simp⟩
              rw [hf2] at h5'
              exact absurd h5' (by simp)
            | cons a l =>
              rw [hf2] at h2x
              simp at h2x
          have hagree : ∀ m ∈ B', slot d m = slot d' m := fun m hm =>
            (h2 m (fun hc => hnotin (hc ▸ hm))).symm
          have hlen' : (B'.filter (fun k => k == j)).length ≤ 1 := by
            have h2x := hlen
            rw [List.filter_cons_of_pos (by simp)] at h2x
            have h3x : (j :: (B'.filter (fun k => k == j))).length =
                (B'.filter (fun k => k == j)).length + 1 := rfl
            omega
          simp only [pkgGo] at h ⊢
          by_cases hc1 : (cnt == slot d j) = true
          · simp at hc1
            omega
          · rw [if_neg hc1] at h
            by_cases hy : 7 ≤ y
            · rw [if_pos hy] at h
              exact absurd h (by simp)
            rw [if_neg hy] at h
            rcases Nat.lt_or_ge (cnt + 1) (slot d j) with hclt | hcge
            · -- Deep case: cnt < slot d' j
              have hc1' : ¬((cnt == slot d' j) = true) := by
                have hcx : cnt ≠ slot d' j := by omega
                simp [hcx]
              rw [if_neg hc1', if_neg hy]
              rcases Bool.or_eq_true_iff.mp h with hcell | hskip
              · rcases Bool.and_eq_true_iff.mp hcell with ⟨hCK, hrec⟩
                have hrec2 := ih (j :: B') (uc + 2 ^ y)
                  (uk + 2 ^ ((y + 7 - slot sc j % 7) % 7)) (y + 1) (cnt + 1)
                  hpos hlen (Or.inl (by omega)) hrec
                exact Bool.or_eq_true_iff.mpr (Or.inl (Bool.and_eq_true_iff.mpr ⟨hCK, hrec2⟩))
              · have hskip2 := ih (j :: B') uc uk (y + 1) cnt hpos hlen (Or.inl hcnt) hskip
                exact Bool.or_eq_true_iff.mpr (Or.inr hskip2)
            · -- Boundary: cnt = slot d' j; the cell branch unfolds one step then agree+mono, the skip branch uses the IH
              have hc1'e : ((cnt == slot d' j) = true) := by simp; omega
              rw [if_pos hc1'e]
              rcases Bool.or_eq_true_iff.mp h with hcell | hskip
              · rcases Bool.and_eq_true_iff.mp hcell with ⟨hCK, hrec⟩
                cases g with
                | zero => exact absurd hrec (by simp [pkgGo])
                | succ g' =>
                  simp only [pkgGo] at hrec
                  have hc3 : ((cnt + 1 == slot d j) = true) := by simp; omega
                  rw [if_pos hc3] at hrec
                  have h1x := pkgGo_agree S sc ban d d' g' B' (uc + 2 ^ y)
                    (uk + 2 ^ ((y + 7 - slot sc j % 7) % 7)) 0 0 hagree
                  rw [h1x] at hrec
                  rw [bit0, bit0] at hCK
                  obtain ⟨hL, hR⟩ := Bool.and_eq_true_iff.mp hCK
                  obtain ⟨hLL, hBan⟩ := Bool.and_eq_true_iff.mp hL
                  obtain ⟨hS, hU⟩ := Bool.and_eq_true_iff.mp hLL
                  obtain ⟨hK, hK0⟩ := Bool.and_eq_true_iff.mp hR
                  have hU' : uc.testBit y = false := by
                    cases hh : uc.testBit y with
                    | false => rfl
                    | true => rw [hh] at hU; exact absurd hU (by simp)
                  have hK' : uk.testBit ((y + 7 - slot sc j % 7) % 7) = false := by
                    cases hh : uk.testBit ((y + 7 - slot sc j % 7) % 7) with
                    | false => rfl
                    | true => rw [hh] at hK; exact absurd hK (by simp)
                  exact pkgGo_fuel_mono S sc ban d' g' B' uc uk 0 0
                    (pkgGo_mono S sc ban d' g' B' (uc + 2 ^ y)
                      (uk + 2 ^ ((y + 7 - slot sc j % 7) % 7)) uc uk 0 0
                      (bitsub_add uc uc y hU' (bitsub_refl uc))
                      (bitsub_add uk uk ((y + 7 - slot sc j % 7) % 7) hK' (bitsub_refl uk))
                      hrec) (g' + 1) (by omega)
              · -- Skip branch: exit via the IH, then fuel_mono
                cases g with
                | zero => exact absurd hskip (by simp [pkgGo])
                | succ g' =>
                  have hskip2 := ih (j :: B') uc uk (y + 1) cnt hpos hlen (Or.inl hcnt) hskip
                  simp only [pkgGo] at hskip2
                  rw [if_pos hc1'e] at hskip2
                  exact pkgGo_fuel_mono S sc ban d' g' B' uc uk 0 0 hskip2 (g' + 1) (by omega)
        · exact absurd hne' (by simp)
      · -- j != i: the head block is identical on both sides; the recursion is delegated to the IH
        have hj2 : slot d' j = slot d j := h2 j hij
        have hlen' : ((j :: B').filter (fun j_1 => j_1 == i)).length ≤ 1 := by
          exact hlen
        have hlen'' : (B'.filter (fun j_1 => j_1 == i)).length ≤ 1 := by
          rw [List.filter_cons_of_neg (by simpa using hij)] at hlen'
          exact hlen'
        have hentryB' : (match B' with
            | [] => True
            | j' :: _ => 0 + 1 ≤ slot d j' ∨ j' ≠ i) := by
          cases B' with
          | nil => trivial
          | cons j2 _ =>
            refine Or.inl ?_
            have hx := hpos j2 (by simp)
            omega
        simp only [pkgGo] at h ⊢
        rw [hj2]
        by_cases hc : (cnt == slot d j) = true
        · rw [if_pos hc] at h ⊢
          refine ih B' uc uk 0 0 hpos' hlen'' ?_ h
          cases B' with
          | nil => trivial
          | cons j2 _ =>
            refine Or.inl ?_
            have hx := hpos j2 (by simp)
            omega
        · rw [if_neg hc] at h ⊢
          by_cases hy : 7 ≤ y
          · rw [if_pos hy] at h
            exact absurd h (by simp)
          rw [if_neg hy] at h ⊢
          rcases Bool.or_eq_true_iff.mp h with hcell | hskip
          · rcases Bool.and_eq_true_iff.mp hcell with ⟨hCK, hrec⟩
            have hrec2 := ih (j :: B') (uc + 2 ^ y)
              (uk + 2 ^ ((y + 7 - slot sc j % 7) % 7)) (y + 1) (cnt + 1)
              hpos hlen (Or.inr hij) hrec
            exact Bool.or_eq_true_iff.mpr (Or.inl (Bool.and_eq_true_iff.mpr ⟨hCK, hrec2⟩))
          · have hskip2 := ih (j :: B') uc uk (y + 1) cnt hpos hlen (Or.inr hij) hskip
            exact Bool.or_eq_true_iff.mpr (Or.inr hskip2)

/-! ## Main theorem: the downset property (slot-value form) -/

/-- Filtering the 4-element literal list by "equal to i" leaves at most one element (decidability of the literal beq). -/
theorem filter4_len (p : Nat → Bool) (i : Nat) :
    ([0, 1, 2, 3].filter (fun a => (a == i) && p a)).length ≤ 1 := by
  simp only [List.filter_cons]
  split <;> split <;> split <;> split <;> simp_all <;> omega

/-- **The general downset theorem**: a single-slot decrement preserves
feasibility (arbitrary (S, s, side, demand)).
The Lean proof of "every immediate predecessor of a feasible point is
feasible" (a DFS-shaped formalization of the two-line restriction argument;
no native_decide, no sorry). -/
theorem pkg_downset (S sc : Nat) (ban : Bool) (d d' i : Nat)
    (hi : 1 ≤ slot d i)
    (h1 : slot d' i + 1 = slot d i)
    (h2 : ∀ j, j ≠ i → slot d' j = slot d j)
    (h : pkg S sc ban d = true) :
    pkg S sc ban d' = true := by
  unfold pkg at h ⊢
  by_cases hi4 : i ∈ [0, 1, 2, 3]
  · -- Main path: i is an actual block
    have hBpos : ∀ j ∈ [0, 1, 2, 3].filter (fun j => slot d j > 0), 1 ≤ slot d j := by
      intro j hj
      have hj2 := (List.mem_filter.mp hj).2
      simp at hj2
      omega
    have iB : i ∈ [0, 1, 2, 3].filter (fun j => slot d j > 0) :=
      List.mem_filter.mpr ⟨hi4, by simp [show 0 < slot d i from by omega]⟩
    obtain ⟨j0, B0, hBcons⟩ :
        ∃ j0 B0, [0, 1, 2, 3].filter (fun j => slot d j > 0) = j0 :: B0 := by
      cases hb : [0, 1, 2, 3].filter (fun j => slot d j > 0) with
      | nil => rw [hb] at iB; exact absurd iB (by simp)
      | cons a b => exact ⟨a, b, rfl⟩
    have h4 : i < 4 := by
      simp only [List.mem_cons, List.mem_cons, List.mem_cons, List.mem_singleton] at hi4
      rcases hi4 with h | h | h | h
      · omega
      · omega
      · omega
      · simp at h; omega
    have hlen : (([0, 1, 2, 3].filter (fun j => slot d j > 0)).filter
        (fun j => j == i)).length ≤ 1 := by
      rw [List.filter_filter]
      exact filter4_len (fun a => decide (slot d a > 0)) i
    have hentry : (match [0, 1, 2, 3].filter (fun j => slot d j > 0) with
        | [] => True
        | j :: _ => 0 + 1 ≤ slot d j ∨ j ≠ i) := by
      cases hb2 : [0, 1, 2, 3].filter (fun j => slot d j > 0) with
      | nil => exact trivial
      | cons j2 _ =>
        refine Or.inl ?_
        have hx := hBpos j2 (by rw [hb2]; simp)
        omega
    have hds := pkgGo_ds S sc ban d d' i h1 h2 512
      ([0, 1, 2, 3].filter (fun j => slot d j > 0)) 0 0 0 0 hBpos hlen hentry h
    rcases Nat.lt_or_ge (slot d i) 2 with hlt2 | hge2
    · -- slot d i = 1: block i drops out of the block list
      have h0' : slot d' i = 0 := by omega
      have hBeq : [0, 1, 2, 3].filter (fun j => slot d' j > 0) =
          ([0, 1, 2, 3].filter (fun j => slot d j > 0)).filter (fun j => !(j == i)) := by
        rw [List.filter_filter]
        apply List.filter_congr
        intro j _
        by_cases hj : j = i
        · subst hj
          simp [h0']
        · rw [h2 j hj]
          simp [hj]
      rw [hBeq]
      exact (pkgGo_drop0 S sc ban d' i h0' 512).1
        ([0, 1, 2, 3].filter (fun j => slot d j > 0)) 0 0 hds
    · -- slot d i >= 2: the block list is unchanged
      have hBeq : [0, 1, 2, 3].filter (fun j => slot d' j > 0) =
          [0, 1, 2, 3].filter (fun j => slot d j > 0) := by
        apply List.filter_congr
        intro j _
        by_cases hj : j = i
        · subst hj
          have hA : 0 < slot d j := by omega
          have hB : 0 < slot d' j := by omega
          simp [hA, hB]
        · rw [h2 j hj]
      rw [hBeq]
      exact hds
  · -- i >= 4: d and d' agree slotwise on the block list, so the agreement lemma applies
    have hBeq : [0, 1, 2, 3].filter (fun j => slot d' j > 0) =
        [0, 1, 2, 3].filter (fun j => slot d j > 0) := by
      apply List.filter_congr
      intro j hj4
      simp [h2 j (fun hc => hi4 (hc ▸ hj4))]
    have hagree : ∀ j ∈ [0, 1, 2, 3].filter (fun j => slot d j > 0),
        slot d j = slot d' j := by
      intro j hj4
      have hjb : j ∈ [0, 1, 2, 3] := (List.mem_filter.mp hj4).1
      exact (h2 j (fun hc => hi4 (hc ▸ hjb))).symm
    rw [hBeq]
    have hx := pkgGo_agree S sc ban d d' 512
      ([0, 1, 2, 3].filter (fun j => slot d j > 0)) 0 0 0 0 hagree
    rw [hx] at h
    exact h

/-! ## Machine evidence with zero uncovered points -/
#print axioms pkg_downset
#print axioms pkgGo_ds
#print axioms pkgGo_mono
#print axioms pkgGo_agree
#print axioms pkgGo_drop0

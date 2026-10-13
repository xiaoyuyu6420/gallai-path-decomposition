import Front583.Pi3L2b

/-! # Front583.Pi3Downset — Π3·L2(b) 下集性一般定理（纸面级 fully-prove）

**承接对象**（deep_A334_pi3.md §2.1 引理 1「下集性」+ deep_A366 任务②）：
A334 的下集性引理「可行点的一切直接前驱仍可行」（纸面=两行限制论证，
A334 机检 120×330×2 全核 0 违例；Pi3Uni.lean 以表域 native_decide 证书承载）
在本件升格为**一般形式的全证明定理**：

    pkg_downset：任意 (S, s, 侧, d, d', i)，slot d i ≥ 1、d' = d 槽 i 减一
    （其余槽同）⟹ pkg S sc ban d = true → pkg S sc ban d' = true

证明结构（全部纸面 tactic，无 native_decide/无 sorry）：
位运算工具（testBit_add_two_pow：位清零时加 2^k 只翻位 k）→
pkgGo_mono（占用掩码变小成功性保持，Bitsub 点位式子集）→
pkgGo_agree（块表槽值全同则行为恒等）→ pkgGo_fuel_mono（燃料单调）→
pkgGo_ds（主归纳：单槽减一的成功性转移，头块 i 的边界情形
「展开一步 + agree + mono + 燃料单调」）→ pkg_downset（装配：
块表 filter 全等 + 零需求块删除 pkgGo_drop0 互归纳）。

诚实落款：axioms 依赖 [propext, Classical.choice, Quot.sound]——Lean 三大
标准逻辑公理（与 Fan.lean/Cert12 系定理同档），**无 sorryAx、无
Lean.ofReduceBool**，为纸面级证明（区别于 Pi3L2b/Pi3Uni 的
native_decide 机器证书级）。覆盖域：任意 (S, sc, ban, d, d', i) 全称形式，
不受 120 轨道代表/Σd≤7 域限制。溯源链：labA174._pkg 语义 →
Pi3L2b.pkg（A360 逐式重实现）→ 本件。-/


/-! ## 位运算工具 -/

/-- 加 2^k 在位 k 清零时只翻位 k。 -/
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

/-- 点位式位含关系。 -/
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

/-- testBit 桥：pkgGo 中 `== 0` 的位判断 = 非 testBit。 -/
theorem bit0 (n k : Nat) : (((n >>> k) &&& 1 : Nat) == 0) = !(n.testBit k) := by
  have h1 : (n >>> k) &&& 1 = (n >>> k) % 2 := Nat.and_one_is_mod _
  have h2 : n.testBit k = decide ((n >>> k) % 2 = 1) := by simp [Nat.testBit]
  rw [h1, h2]
  by_cases hm : (n >>> k) % 2 = 0
  · simp [hm]
  · have h3 : (n >>> k) % 2 = 1 := by omega
    simp [h3]

/-! ## pkgGo 的结构引理 -/

/-- 燃料单调：大燃料下成功性保持。 -/
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

/-- 单调性：占用掩码变小（点位式），成功性保持。 -/
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

/-- 同意引理：块表上槽值全同则行为恒等。 -/
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

/-- 零需求块 wander 失败引理：零需求块在 cnt ≠ 0 时必失败。 -/
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

/-- **零需求块删除**：slot d i = 0 时，块表中的 i 块可整体删除。
P0 = (0,0) 入口态主断言；P1 = 头块 ≠ i 的块内递归不变式（互归纳）。 -/
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
/-! ## 主归纳：单槽减一的成功性转移 -/

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
        · -- cnt + 1 ≤ slot d j；j ∉ B'（主路径）
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
            · -- 深层：cnt < slot d' j
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
            · -- 边界：cnt = slot d' j，cell 分支展开一步后 agree+mono，skip 分支 IH
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
              · -- skip 分支：IH 后出口 + fuel_mono
                cases g with
                | zero => exact absurd hskip (by simp [pkgGo])
                | succ g' =>
                  have hskip2 := ih (j :: B') uc uk (y + 1) cnt hpos hlen (Or.inl hcnt) hskip
                  simp only [pkgGo] at hskip2
                  rw [if_pos hc1'e] at hskip2
                  exact pkgGo_fuel_mono S sc ban d' g' B' uc uk 0 0 hskip2 (g' + 1) (by omega)
        · exact absurd hne' (by simp)
      · -- j ≠ i：头块两侧同构，递归交给 IH
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

/-! ## 主定理：下集性（槽值形式） -/

/-- 4 元素字面列表按「等于 i」过滤后长度至多 1（字面 beq 可判定性）。 -/
theorem filter4_len (p : Nat → Bool) (i : Nat) :
    ([0, 1, 2, 3].filter (fun a => (a == i) && p a)).length ≤ 1 := by
  simp only [List.filter_cons]
  split <;> split <;> split <;> split <;> simp_all <;> omega

/-- **下集性一般定理**：单槽减一不破坏可行性（任意 (S, s, 侧, 需求)）。
「可行点的一切直接前驱仍可行」的 Lean 纸面证明（deep_A334 两行限制论证的
逐 DFS 形式化；不依赖 native_decide/sorry）。 -/
theorem pkg_downset (S sc : Nat) (ban : Bool) (d d' i : Nat)
    (hi : 1 ≤ slot d i)
    (h1 : slot d' i + 1 = slot d i)
    (h2 : ∀ j, j ≠ i → slot d' j = slot d j)
    (h : pkg S sc ban d = true) :
    pkg S sc ban d' = true := by
  unfold pkg at h ⊢
  by_cases hi4 : i ∈ [0, 1, 2, 3]
  · -- 主路径：i 是真实块
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
    · -- slot d i = 1：i 从块表脱落
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
    · -- slot d i ≥ 2：块表不变
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
  · -- i ≥ 4：块表上 d/d' 槽值全同 → agree
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

/-! ## 零洞机器证据 -/
#print axioms pkg_downset
#print axioms pkgGo_ds
#print axioms pkgGo_mono
#print axioms pkgGo_agree
#print axioms pkgGo_drop0

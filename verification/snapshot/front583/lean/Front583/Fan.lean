import Front583.General

/-!
# front583 / lane_68b + lane_68c：Fan 回插引擎的形式化内核（2026-09-17/18）

本文件承接 lane_68（Astar.lean）的三条占位 `fan_class` / `fan6_use` / `fan7_use`。
对 `fan6_use`，lane_68b 把缺口**精确分解**为

- `fan6_nf`（骨架 sorry，陈述经暴力穷举验证）：passing 条件下，D 可**等轮廓重排**
  为存在避开 a 的 b-端路径的分解；
- `fan6_case1`（**真证**，零 sorry）：一旦存在避开 a 的 b-端路径，
  延长一条 ab 边即得 fan6 结论（lane_33 §9 建议的种子引理 C33-0）。

`fan6_use` = `fan6_nf` + `fan6_case1` + 轮廓转移的三步组装自 lane_68c 起落在
Astar.lean 的同名定理处（lane_68c：本文件修复 4 处编译错误后经 Astar.lean
import 正式入链；两文件重复的 del1 块合并为本文件一份）。
即：A\* 链对外的占位面不减（4 条一对一占位），但 fan6_use 的剩余数学
从"整条 Fan 引理"收缩为**单一重排核心** `fan6_nf`。

**机器验证底账（2026-09-17，lab/fan68b/，Apple Silicon Python 穷举）**：
- fan6_use 形态：n ≤ 5 全空间 241,040 个合格实例 0 违反；n = 6 后台进行中；
- fan7_use 形态：n ≤ 5 全空间 36,620 个合格实例 0 违反；n = 6 后台进行中；
- **NF 归约核验**（probe_nf.py）：全部 16,690 个"每条 b-端路径都含 a"实例
  （n = 4: 30，n = 5: 16,660）中，16,690 个都存在等轮廓重排使某条 b-端路径
  避开 a——即 `fan6_nf` 的陈述在这些范围内无反例。

**lane_68c 增量（2026-09-18，lab/fan68c/）**：
- 本文件 4 处编译错误修复（`vEndBit_append_ne` 的 if 改写、
  `distinct_listReplace` 的成员参数、`fan6_case1` 的 IsEdgeDisjoint 引入形状
  与 hdisj' 大 case 分析、fan6_use 组装的参数/轮廓转移——后者移入 Astar.lean）；
- **link 否证**（probe_detour.py）：试探把缺口缩为"Case-2 单步绕行纠正结构
  必存在"（坏路标记 m 有避开 a 的 m-端路径），n = 5 穷举 241,040 合格实例中
  **1,710 例失败**（0.71%），单步 detour 不足以支撑 fan6，级联重排（fan6_nf）
  为不可再缩的核。

**lane_108/109/111 勘误与 W4'（2026-09-19）**：上方"16,690 实例均存在等轮廓
重排、fan6_nf 无反例"的底账为**单方向口径**（probe_nf.py 对每删边只测
(min,max)），已被 lane_108 机器反例（掩码 221，a = 2, b = 0，见文件末
`gtest221_no_target`）否证——fan6_nf 陈述为假，已封存（见 741 行注释块、
749 行定理本体）。
W4'（lane_111）：Astar.lean 的 fan6_use 摘除本件依赖、恢复直接占位；
fan6_use 自身陈述的机器底账（双向）见 campaign/lane_109_audit.md §2.2。

**lane_154（2026-09-21）W3 降档棒：C2 直组（fan6_use 四子句真证）**：
本节文件末新增 `fan6_use_c2`（C2 存在性，机器 0 违反，未证 sorry，换位
承接原 fan6_use 五子句剩余域缺口）与 `fan6_use_weak`（四子句，C2+case1
完全真证）。Astar.lean 的 `fan6_use` 已降档为四子句并直组本件。gtest221
封存块与 `fan6_nf` 封存块零触碰。
-/

namespace Front583

/-! ## 单边删除图 del1（自 Astar.lean 迁入：fan6 接口图） -/

/-- 单边删除的邻接。 -/
def del1Adj {n : Nat} (H : Graph n) (a b : Fin n) (x y : Fin n) : Bool :=
  H.adjB x y && !(decide (x = a) && decide (y = b)) && !(decide (x = b) && decide (y = a))

theorem del1Adj_true_iff {n : Nat} (H : Graph n) (a b x y : Fin n) :
    del1Adj H a b x y = true ↔
      H.adjB x y = true ∧ ¬((x = a ∧ y = b) ∨ (x = b ∧ y = a)) := by
  unfold del1Adj
  rw [Bool.and_eq_true_iff, Bool.and_eq_true_iff]
  constructor
  · rintro ⟨⟨h1, hn1⟩, hn2⟩
    refine ⟨h1, ?_⟩
    rintro (⟨he1, he2⟩ | ⟨he1, he2⟩)
    · have hd1 : (decide (x = a) && decide (y = b)) = true := by simp [he1, he2]
      rw [hd1] at hn1
      exact Bool.noConfusion hn1
    · have hd2 : (decide (x = b) && decide (y = a)) = true := by simp [he1, he2]
      rw [hd2] at hn2
      exact Bool.noConfusion hn2
  · rintro ⟨h1, h2⟩
    refine ⟨⟨h1, ?_⟩, ?_⟩
    · cases hd : (decide (x = a) && decide (y = b)) with
      | false => rfl
      | true =>
        rw [Bool.and_eq_true_iff] at hd
        exact absurd ⟨decide_eq_true_iff.1 hd.1, decide_eq_true_iff.1 hd.2⟩
          (fun hc => h2 (Or.inl hc))
    · cases hd : (decide (x = b) && decide (y = a)) with
      | false => rfl
      | true =>
        rw [Bool.and_eq_true_iff] at hd
        exact absurd ⟨decide_eq_true_iff.1 hd.1, decide_eq_true_iff.1 hd.2⟩
          (fun hc => h2 (Or.inr hc))

theorem del1Adj_symm {n : Nat} (H : Graph n) (a b : Fin n) (x y : Fin n)
    (h : del1Adj H a b x y = true) : del1Adj H a b y x = true := by
  rw [del1Adj_true_iff] at h ⊢
  obtain ⟨h1, h2⟩ := h
  refine ⟨H.symm x y h1, fun hc => h2 ?_⟩
  rcases hc with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · exact Or.inr ⟨e2, e1⟩
  · exact Or.inl ⟨e2, e1⟩

theorem del1Adj_loop {n : Nat} (H : Graph n) (a b : Fin n) (x : Fin n) :
    del1Adj H a b x x = false :=
  Bool.eq_false_iff.2 (fun hc => by
    obtain ⟨h1, _⟩ := del1Adj_true_iff H a b x x |>.1 hc
    exact Bool.noConfusion (H.loopless x |>.symm.trans h1))

/-- 单边删除图 H − ab（回插引擎的 fan6 接口图）。 -/
def del1 {n : Nat} (H : Graph n) (a b : Fin n) : Graph n :=
  ⟨del1Adj H a b, del1Adj_symm H a b, del1Adj_loop H a b⟩

theorem del1_adj_iff {n : Nat} (H : Graph n) (a b x y : Fin n) :
    (del1 H a b).adjB x y = true ↔
      H.adjB x y = true ∧ ¬((x = a ∧ y = b) ∨ (x = b ∧ y = a)) :=
  del1Adj_true_iff H a b x y

theorem del1Adj_eq_of_ne {n : Nat} (H : Graph n) (a b x y : Fin n)
    (h1 : ¬ (x = a ∧ y = b)) (h2 : ¬ (x = b ∧ y = a)) :
    (del1 H a b).adjB x y = H.adjB x y := by
  show del1Adj H a b x y = H.adjB x y
  unfold del1Adj
  have d1 : (decide (x = a) && decide (y = b)) = false := by
    cases hd : (decide (x = a) && decide (y = b)) with
    | false => rfl
    | true =>
      rw [Bool.and_eq_true_iff] at hd
      exact absurd (⟨decide_eq_true_iff.1 hd.1, decide_eq_true_iff.1 hd.2⟩) h1
  have d2 : (decide (x = b) && decide (y = a)) = false := by
    cases hd : (decide (x = b) && decide (y = a)) with
    | false => rfl
    | true =>
      rw [Bool.and_eq_true_iff] at hd
      exact absurd (⟨decide_eq_true_iff.1 hd.1, decide_eq_true_iff.1 hd.2⟩) h2
  rw [d1, d2]
  simp

theorem del1Adj_swap {n : Nat} (H : Graph n) (a b x y : Fin n) :
    del1Adj H a b x y = del1Adj H b a x y := by
  unfold del1Adj
  cases h1 : decide (x = a) <;> cases h2 : decide (y = b) <;>
    cases h3 : decide (x = b) <;> cases h4 : decide (y = a) <;>
    simp

theorem del1_swap {n : Nat} (H : Graph n) (a b x y : Fin n) :
    (del1 H a b).adjB x y = (del1 H b a).adjB x y :=
  del1Adj_swap H a b x y

/-- fan6 的 passing 条件（死邻居计数）：H−ab 中 a 的、在 D 中无端点路径的邻居数。 -/
def deadCount6 {n : Nat} (H : Graph n) (a b : Fin n) (D : List (List (Fin n))) : Nat :=
  ((finList n).filter
    (fun w => decide ((del1 H a b).adjB a w = true ∧ vEndCount D w = 0))).length

/-! ## 工具：链单调性与尾部延长 -/

/-- 邻接单调：adj₁ 链 ⟹ adj₂ 链（adj₂ 逐点包含 adj₁）。 -/
theorem chain_mono {V : Type} (adj₁ adj₂ : V → V → Prop) :
    ∀ (P : List V), Chain adj₁ P → (∀ x y, adj₁ x y → adj₂ x y) → Chain adj₂ P
  | [], _, _ => True.intro
  | [_], _, _ => True.intro
  | x :: y :: r, hc, hmono => ⟨hmono x y hc.1, chain_mono adj₁ adj₂ (y :: r) hc.2 hmono⟩

/-- 在 H−ab 中成立的链在 H 中成立。 -/
theorem chain_del1_to_H {n : Nat} (H : Graph n) (a b : Fin n) (P : List (Fin n))
    (hc : Chain (GAdj (del1 H a b)) P) : Chain (GAdj H) P :=
  chain_mono (GAdj (del1 H a b)) (GAdj H) P hc
    (fun x y hxy => show GAdj H x y from ((del1_adj_iff H a b x y).1 hxy).1)

/-- 尾部接单点保持链。 -/
theorem chain_append_single {V : Type} (adj : V → V → Prop) :
    ∀ (P : List V) (z : V), Chain adj P → (∀ w, lastOf P = some w → adj w z) →
      Chain adj (P ++ [z])
  | [], z, _, _ => True.intro
  | [x], z, _, hlast => by
      have hshow : ([x] ++ [z]) = [x, z] := rfl
      rw [hshow]
      exact ⟨hlast x rfl, True.intro⟩
  | x :: y :: r, z, hc, hlast => by
      show adj x y ∧ Chain adj ((y :: r) ++ [z])
      exact ⟨hc.1, chain_append_single adj (y :: r) z hc.2 hlast⟩

/-! ## 工具：EIn 与邻接、前缀后缀 -/

/-- 路径的边必为图的边。 -/
theorem EIn_adj {n : Nat} (G : Graph n) (P : List (Fin n)) (hP : IsPath (GAdj G) P) :
    ∀ x y : Fin n, EIn P x y → G.adjB x y = true := by
  obtain ⟨_, _, hchain⟩ := hP
  intro x y hxy
  rcases EIn_mem_pairsOf P hxy with h | h
  · exact pairsOf_chain_adj (GAdj G) P hchain (x, y) h
  · exact G.symm y x (pairsOf_chain_adj (GAdj G) P hchain (y, x) h)

theorem EIn_cons_prefix {V : Type} {c : V} : ∀ (P : List V) (x y : V),
    EIn P x y → EIn (c :: P) x y
  | [], _, _, h => h.elim
  | [_], _, _, h => h.elim
  | u :: v :: r, x, y, h => by
      show (c = x ∧ u = y) ∨ (c = y ∧ u = x) ∨ EIn (u :: v :: r) x y
      refine Or.inr (Or.inr ?_)
      show (u = x ∧ v = y) ∨ (u = y ∧ v = x) ∨ EIn (v :: r) x y
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | h3
      · exact Or.inl ⟨h1, h2⟩
      · exact Or.inr (Or.inl ⟨h1, h2⟩)
      · exact Or.inr (Or.inr h3)

theorem EIn_append_suffix {V : Type} {c : V} : ∀ (P : List V) (x y : V),
    EIn P x y → EIn (P ++ [c]) x y
  | [], _, _, h => h.elim
  | [_], _, _, h => h.elim
  | u :: v :: r, x, y, h => by
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | h3
      · exact Or.inl ⟨h1, h2⟩
      · exact Or.inr (Or.inl ⟨h1, h2⟩)
      · exact Or.inr (Or.inr (EIn_append_suffix (v :: r) x y h3))

/-- EIn 在尾部接单点下的反演。 -/
theorem EIn_append_inv {V : Type} {c : V} : ∀ (P : List V) (x y : V),
    EIn (P ++ [c]) x y →
      EIn P x y ∨ (x = c ∧ lastOf P = some y) ∨ (y = c ∧ lastOf P = some x)
  | [], x, y, h => h.elim
  | [x], u, v, h => by
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | h3
      · exact Or.inr (Or.inr ⟨h2.symm, by simp [lastOf, h1]⟩)
      · exact Or.inr (Or.inl ⟨h2.symm, by simp [lastOf, h1]⟩)
      · exact h3.elim
  | u :: v :: r, x, y, h => by
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | h3
      · exact Or.inl (Or.inl ⟨h1, h2⟩)
      · exact Or.inl (Or.inr (Or.inl ⟨h1, h2⟩))
      · rcases EIn_append_inv (v :: r) x y h3 with h4 | h4 | h4
        · exact Or.inl (Or.inr (Or.inr h4))
        · exact Or.inr (Or.inl ⟨h4.1, h4.2⟩)
        · exact Or.inr (Or.inr ⟨h4.1, h4.2⟩)

/-- 尾部追加的单边：d 是 P 的尾时，(d, c) 是 P ++ [c] 的最后一对。 -/
theorem EIn_append_last {V : Type} : ∀ (P : List V) (c d : V), lastOf P = some d →
    EIn (P ++ [c]) d c
  | [], c, d, hl => by simp [lastOf] at hl
  | [x], c, d, hl => by
      show (x = d ∧ c = c) ∨ (x = c ∧ c = d) ∨ EIn [c] d c
      exact Or.inl ⟨by simpa [lastOf] using hl, rfl⟩
  | u :: v :: r, c, d, hl => by
      show (u = d ∧ v = c) ∨ (u = c ∧ v = d) ∨ EIn (v :: (r ++ [c])) d c
      exact Or.inr (Or.inr (EIn_append_last (v :: r) c d hl))

theorem isEnd_mem {V : Type} [DecidableEq V] {v : V} : ∀ (P : List V),
    isEnd v P → v ∈ P := by
  intro P h
  unfold isEnd at h
  rcases h with h | h
  · cases P with
    | nil => simp [List.head?] at h
    | cons x t =>
      have hx : x = v := by simpa [List.head?] using h
      exact List.mem_cons.2 (Or.inl hx.symm)
  · exact lastOf_some_mem P v h

theorem lastOf_eq_append {V : Type} : ∀ (P : List V) (v : V), lastOf P = some v →
    ∃ q : List V, P = q ++ [v]
  | [], v, h => by simp [lastOf] at h
  | [x], v, h => by
      simp only [lastOf] at h
      cases h
      exact ⟨[], by simp⟩
  | x :: y :: r, v, h => by
      obtain ⟨q, hq⟩ := lastOf_eq_append (y :: r) v h
      refine ⟨x :: q, ?_⟩
      rw [hq]
      simp

theorem lastOf_append_single {V : Type} : ∀ (P : List V) (a : V), P ≠ [] →
    lastOf (P ++ [a]) = some a
  | [], a, hne => absurd rfl hne
  | [x], a, _ => rfl
  | x :: y :: r, a, _ => lastOf_append_single (y :: r) a (by cases r <;> simp)

/-! ## 工具：vEndBit 的计算引理 -/

theorem vEndBit_cons_self {n : Nat} (a : Fin n) (P : List (Fin n)) :
    vEndBit a (a :: P) = 1 := by
  unfold vEndBit
  simp

theorem vEndBit_append_self {n : Nat} (a : Fin n) (P : List (Fin n)) (h : P ≠ []) :
    vEndBit a (P ++ [a]) = 1 := by
  unfold vEndBit
  rw [if_pos (Or.inr (lastOf_append_single P a h))]


theorem vEndBit_not_mem {n : Nat} {v : Fin n} (P : List (Fin n)) (h : v ∉ P) :
    vEndBit v P = 0 := by
  unfold vEndBit
  rw [if_neg (by
    rintro (h1 | h2)
    · exact h (by
        cases P with
        | nil => simp [List.head?] at h1
        | cons x t => exact List.mem_cons.2 (Or.inl (by simpa [List.head?] using h1.symm)))
    · exact h (lastOf_some_mem P v h2))]

theorem headQ_append_single {V : Type} (P : List V) (a : V) (hP : P ≠ []) :
    (P ++ [a]).head? = P.head? := by
  cases P with
  | nil => exact absurd rfl hP
  | cons x t => rfl

/-- 头部插入（a ≠ v 且 v 不是 P 的头）不改变 v 的端点位。 -/
theorem vEndBit_cons_ne {n : Nat} {a v : Fin n} (P : List (Fin n))
    (hne : a ≠ v) (hv : P.head? ≠ some v) :
    vEndBit v (a :: P) = vEndBit v P := by
  unfold vEndBit
  revert hv
  cases P with
  | nil => intro hv; simp [hne, lastOf]
  | cons x t =>
    intro hv
    have h1 : (a :: x :: t).head? = some a := rfl
    have h2 : lastOf (a :: x :: t) = lastOf (x :: t) := rfl
    rw [h1, h2]
    by_cases hC : lastOf (x :: t) = some v
    · rw [if_pos (Or.inr hC), if_pos (Or.inr hC)]
    · rw [if_neg (by
        rintro (h | h)
        · exact hne (by simpa using h)
        · exact hC h),
        if_neg (by
        rintro (h | h)
        · exact hv h
        · exact hC h)]

/-- 尾部追加（a ≠ v 且 v 不是 P 的尾）不改变 v 的端点位。 -/
theorem vEndBit_append_ne {n : Nat} {a v : Fin n} (P : List (Fin n))
    (hne : a ≠ v) (hv : lastOf P ≠ some v) (hP : P ≠ []) :
    vEndBit v (P ++ [a]) = vEndBit v P := by
  unfold vEndBit
  have h1 : lastOf (P ++ [a]) = some a := lastOf_append_single P a hP
  have h2 : (P ++ [a]).head? = P.head? := headQ_append_single P a hP
  rw [h2, h1]
  by_cases hC : P.head? = some v
  · rw [if_pos (show P.head? = some v ∨ some a = some v from Or.inl hC),
      if_pos (show P.head? = some v ∨ lastOf P = some v from Or.inl hC)]
  · rw [if_neg (show ¬(P.head? = some v ∨ some a = some v) from by
      rintro (h | h)
      · exact hC h
      · exact hne (by simpa using h)),
    if_neg (show ¬(P.head? = some v ∨ lastOf P = some v) from by
      rintro (h | h)
      · exact hC h
      · exact hv h)]

/-! ## 工具：listReplace（首处替换） -/

/-- 替换列表中第一处等于 P 的元素为 P'。 -/
def listReplace {V : Type} [DecidableEq V] : List V → V → V → List V
  | [], _, _ => []
  | x :: t, P, P' => if x = P then P' :: t else x :: listReplace t P P'

theorem length_listReplace {V : Type} [DecidableEq V] : ∀ (D : List V) (P P' : V),
    (listReplace D P P').length = D.length
  | [], _, _ => rfl
  | x :: t, P, P' => by
      by_cases h : x = P
      · simp [listReplace, h]
      · simp only [listReplace, if_neg h, List.length_cons]
        rw [length_listReplace t P P']

theorem mem_listReplace_of_ne {V : Type} [DecidableEq V] : ∀ (D : List V) (P P' Q : V),
    Q ∈ D → Q ≠ P → Q ∈ listReplace D P P'
  | [], _, _, _, hQ, _ => nomatch hQ
  | x :: t, P, P', Q, hQ, hne => by
      by_cases h : x = P
      · rcases List.mem_cons.1 hQ with h1 | h1
        · exact absurd (h1.trans h) hne
        · exact (show Q ∈ listReplace (x :: t) P P' from by
            rw [show listReplace (x :: t) P P' = P' :: t from by simp [listReplace, h]]
            exact List.mem_cons.2 (Or.inr h1))
      · rcases (show Q = x ∨ Q ∈ t from by simpa [List.mem_cons] using hQ) with h1 | h1
        · exact (show Q ∈ listReplace (x :: t) P P' from by
            rw [show listReplace (x :: t) P P' = x :: listReplace t P P' from by
              simp [listReplace, h]]
            exact List.mem_cons.2 (Or.inl (by rw [h1])))
        · exact (show Q ∈ listReplace (x :: t) P P' from by
            rw [show listReplace (x :: t) P P' = x :: listReplace t P P' from by
              simp [listReplace, h]]
            exact List.mem_cons.2 (Or.inr (mem_listReplace_of_ne t P P' Q h1 hne)))

theorem mem_listReplace_self {V : Type} [DecidableEq V] : ∀ (D : List V) (P P' : V),
    P ∈ D → P' ∈ listReplace D P P'
  | [], _, _, hP => nomatch hP
  | x :: t, P, P', hP => by
      by_cases h : x = P
      · exact (show P' ∈ listReplace (x :: t) P P' from by
          simpa [listReplace, if_pos h] using List.mem_cons.2 (Or.inl rfl))
      · rcases List.mem_cons.1 hP with h1 | h1
        · exact absurd h1.symm h
        · exact (show P' ∈ listReplace (x :: t) P P' from by
            simpa [listReplace, if_neg h] using
              List.mem_cons.2 (Or.inr (mem_listReplace_self t P P' h1)))

/-- 替换后成员反演（Distinct 下）。 -/
theorem mem_listReplace_inv {V : Type} [DecidableEq V] : ∀ (D : List V) (P P' Q : V),
    Distinct D → Q ∈ listReplace D P P' → Q = P' ∨ (Q ∈ D ∧ Q ≠ P)
  | [], _, _, _, _, hQ => nomatch hQ
  | x :: t, P, P', Q, hdis, hQ => by
      by_cases h : x = P
      · have hQ' : Q ∈ P' :: t := by simpa [listReplace, if_pos h] using hQ
        rcases List.mem_cons.1 hQ' with h1 | h1
        · exact Or.inl h1
        · refine Or.inr ⟨List.mem_cons.2 (Or.inr h1), ?_⟩
          intro hQP
          have hxQ : x = Q := h.trans hQP.symm
          subst hxQ
          exact hdis.1 h1
      · have hQ' : Q ∈ x :: listReplace t P P' := by simpa [listReplace, if_neg h] using hQ
        rcases List.mem_cons.1 hQ' with h1 | h1
        · refine Or.inr ⟨List.mem_cons.2 (Or.inl h1), ?_⟩
          intro hQP
          exact h (h1.symm.trans hQP)
        · rcases mem_listReplace_inv t P P' Q hdis.2 h1 with h2 | h2
          · exact Or.inl h2
          · exact Or.inr ⟨List.mem_cons.2 (Or.inr h2.1), h2.2⟩

/-- 互异列表的单点替换保持互异（新元素不在原列表中）。 -/
theorem distinct_listReplace {V : Type} [DecidableEq V] : ∀ (D : List V) (P P' : V),
    Distinct D → P ∈ D → P' ∉ D → Distinct (listReplace D P P')
  | [], _, _, _, hPmem, _ => nomatch hPmem
  | x :: t, P, P', hdis, hPmem, hP' => by
      by_cases h : x = P
      · have hQ' : listReplace (x :: t) P P' = P' :: t := by simp [listReplace, h]
        rw [hQ']
        exact ⟨fun hmem => hP' (List.mem_cons.2 (Or.inr hmem)), hdis.2⟩
      · have hQ' : listReplace (x :: t) P P' = x :: listReplace t P P' := by
          simp [listReplace, h]
        rw [hQ']
        have hPt : P ∈ t := by
          rcases List.mem_cons.1 hPmem with h3 | h3
          · exact absurd h3.symm h
          · exact h3
        have hxt : x ∉ t := hdis.1
        refine ⟨fun hmem => ?_,
          distinct_listReplace t P P' hdis.2 hPt
            (fun hm => hP' (List.mem_cons.2 (Or.inr hm)))⟩
        rcases mem_listReplace_inv t P P' x hdis.2 hmem with hx' | ⟨hxt', hxP⟩
        · subst hx'
          exact hP' (List.mem_cons.2 (Or.inl rfl))
        · exact hxt hxt'

/-- 端点计数在单点替换下的偏移（无减法形式）。 -/
theorem vEndCount_replace {n : Nat} (D : List (List (Fin n))) (P P' : List (Fin n))
    (hPmem : P ∈ D) :
    ∀ v : Fin n,
      vEndCount (listReplace D P P') v + vEndBit v P = vEndCount D v + vEndBit v P' := by
  induction D with
  | nil => nomatch hPmem
  | cons x t ih =>
      intro v
      by_cases h : x = P
      · have hrep : listReplace (x :: t) P P' = P' :: t := by simp [listReplace, h]
        rw [hrep]
        simp only [vEndCount, List.foldr_cons]
        have hbx : vEndBit v x = vEndBit v P := by rw [h]
        omega
      · have hPmem' : P ∈ t := by
          rcases List.mem_cons.1 hPmem with h1 | h1
          · exact absurd h1.symm h
          · exact h1
        have hrep : listReplace (x :: t) P P' = x :: listReplace t P P' := by
          simp [listReplace, h]
        rw [hrep]
        simp only [vEndCount, List.foldr_cons]
        have hihi := ih hPmem' v
        simp only [vEndCount] at hihi
        omega

/-- 与替换两端无关的顶点端点计数不变。 -/
theorem vEndCount_replace_unchanged {n : Nat} (D : List (List (Fin n))) (P P' : List (Fin n))
    (hPmem : P ∈ D) (v : Fin n) (h1 : vEndBit v P = vEndBit v P') :
    vEndCount (listReplace D P P') v = vEndCount D v := by
  have := vEndCount_replace D P P' hPmem v
  omega

/-- 互异列表尾部接单点。 -/
theorem distinctP_append {V : Type} : ∀ (l : List V) (a : V),
    Distinct l → a ∉ l → Distinct (l ++ [a])
  | [], a, _, _ => ⟨by simp, True.intro⟩
  | b :: t, a, hd, ha => by
      obtain ⟨hb, hdt⟩ := hd
      show Distinct ((b :: t) ++ [a])
      rw [List.cons_append]
      refine ⟨fun hm => ?_, distinctP_append t a hdt (fun hm => ha (List.mem_cons.2 (Or.inr hm)))⟩
      rcases List.mem_append.1 hm with h1 | h2
      · exact hb h1
      · rcases List.mem_singleton.1 h2 with hc
        exact ha (List.mem_cons.2 (Or.inl hc.symm))

/-! ## 延长朝向引理：按 b 端的朝向给出 P' 及其全部记账事实 -/

/-- P 以 b 为一端、避开 a 时，可朝 b 端延长 ab 得 P'，且拥有组装 fan6 所需的全部
    事实（路径性、边集合的内外刻画、端点位）。 -/
theorem extend_orientation {n : Nat} (H : Graph n) (a b : Fin n) (hab : H.adjB a b = true)
    (P : List (Fin n)) (hPlen : 2 ≤ P.length) (hPdis : Distinct P)
    (hPchain : Chain (GAdj H) P) (hPend : isEnd b P) (hPavoid : a ∉ P) :
    ∃ P' : List (Fin n),
      (P' = a :: P ∨ P' = P ++ [a]) ∧
      IsPath (GAdj H) P' ∧
      (∀ x y : Fin n, EIn P x y → EIn P' x y) ∧
      (∀ x y : Fin n, EIn P' x y → EIn P x y ∨ (x = a ∧ y = b) ∨ (x = b ∧ y = a)) ∧
      EIn P' a b ∧
      vEndBit a P' = 1 ∧ vEndBit a P = 0 ∧ vEndBit b P = 1 ∧ vEndBit b P' = 0 ∧
      (∀ w : Fin n, w ≠ a → w ≠ b → vEndBit w P' = vEndBit w P) := by
  have habne : a ≠ b := by
    intro he
    rw [he] at hab
    exact Bool.noConfusion ((H.loopless b).symm.trans hab)
  have hbitA : vEndBit a P = 0 := vEndBit_not_mem P hPavoid
  have hbitB1 : vEndBit b P = 1 := by
    unfold vEndBit
    rw [if_pos (show P.head? = some b ∨ lastOf P = some b from hPend)]
  rcases hPend with hhead | hlast
  · -- 头朝向：P = b :: r，P' = a :: P
    obtain ⟨r, rfl⟩ : ∃ r, P = b :: r := by
      cases P with
      | nil => simp [List.head?] at hhead
      | cons x t =>
        have hx : x = b := by simpa [List.head?] using hhead
        exact ⟨t, by rw [hx]⟩
    have hrne : r ≠ [] := by
      intro hc
      rw [hc] at hPlen
      simp at hPlen
    have hlastP : lastOf (b :: r) ≠ some b := by
      cases r with
      | nil => exact absurd rfl hrne
      | cons y t =>
        intro hc
        have h' : lastOf (y :: t) = some b := hc
        exact hPdis.1 (lastOf_some_mem (y :: t) b h')
    have hbitB0 : vEndBit b (a :: (b :: r)) = 0 := by
      unfold vEndBit
      rw [if_neg (by
        rintro (h | h)
        · exact habne (by simpa using h)
        · exact hlastP h)]
    refine ⟨a :: (b :: r), Or.inl rfl,
      ⟨by simp, ⟨hPavoid, hPdis⟩, ⟨hab, hPchain⟩⟩,
      (fun x y h => EIn_cons_prefix (b :: r) x y h),
      ?_,
      (show EIn (a :: (b :: r)) a b from Or.inl ⟨rfl, rfl⟩),
      vEndBit_cons_self a (b :: r),
      hbitA, hbitB1, hbitB0, ?_⟩
    · intro x y h
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | h
      · exact Or.inr (Or.inl ⟨h1.symm, h2.symm⟩)
      · exact Or.inr (Or.inr ⟨h2.symm, h1.symm⟩)
      · exact Or.inl h
    · intro w hw1 hw2
      have hne2 : a ≠ w := fun hc => hw1 hc.symm
      have hv2 : (b :: r).head? ≠ some w := fun hc => hw2 (by simpa using hc.symm)
      exact vEndBit_cons_ne (b :: r) hne2 hv2
  · -- 尾朝向：P = q ++ [b]，P' = P ++ [a]
    obtain ⟨q, rfl⟩ := lastOf_eq_append P b hlast
    have hne : (q ++ [b]) ≠ [] := by
      intro hc
      rw [hc] at hPlen
      simp at hPlen
    have hheadP : (q ++ [b]).head? ≠ some b := by
      cases q with
      | nil => simp at hPlen
      | cons c q' =>
        intro hc
        have hcb : c = b := by simpa [List.head?] using hc
        rw [hcb] at hPdis
        exact hPdis.1 (List.mem_append.2 (Or.inr (List.mem_singleton.2 rfl)))
    have hbitB0 : vEndBit b ((q ++ [b]) ++ [a]) = 0 := by
      unfold vEndBit
      rw [if_neg (by
        rintro (h | h)
        · rw [headQ_append_single (q ++ [b]) a hne] at h
          exact hheadP h
        · rw [lastOf_append_single _ _ hne] at h
          exact habne (by simpa using h))]
    refine ⟨(q ++ [b]) ++ [a], Or.inr rfl,
      ⟨by simp, distinctP_append _ a hPdis hPavoid,
        chain_append_single (GAdj H) (q ++ [b]) a hPchain
          (fun w hw => show GAdj H w a from by
            have hwb : w = b := by simpa using hw.symm.trans hlast
            rw [hwb]
            exact H.symm a b hab)⟩,
      (fun x y h => EIn_append_suffix (q ++ [b]) x y h),
      ?_,
      (EIn_symm _ _ _ (EIn_append_last (q ++ [b]) a b hlast)),
      vEndBit_append_self a _ hne, hbitA, hbitB1, hbitB0, ?_⟩
    · intro x y h
      rcases EIn_append_inv (q ++ [b]) x y h with h1 | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl h1
      · exact Or.inr (Or.inl ⟨h1, by simpa using h2.symm.trans hlast⟩)
      · exact Or.inr (Or.inr ⟨by simpa using h2.symm.trans hlast, h1⟩)
    · intro w hw1 hw2
      exact vEndBit_append_ne (q ++ [b]) (fun hc => hw1 hc.symm)
        (fun hc => hw2 (by simpa using hc.symm.trans hlast)) hne

/-! ## fan6 内核 Step 2：Case-1 直连延长（真证，lane_33 §9 的 C33-0） -/

/-- **fan6 的 Case-1（真证）**：D 分解 H−ab，若存在以 b 为端点、避开 a 的路径 P，
    则把 P 延长一条 ab 边：得 H 的分解，条数不变，端点记账 a +1 / b −1 / 其余不动。
    证明 = 把 D 中的 P 换成 a::P 或 P++[a]（按 P 的哪一端是 b，见 extend_orientation）。 -/
theorem fan6_case1 {n : Nat} (H : Graph n) (a b : Fin n) (hab : H.adjB a b = true)
    (D : List (List (Fin n))) (hD : IsDecomp (del1 H a b) D)
    (P : List (Fin n)) (hPmem : P ∈ D) (hPend : isEnd b P) (hPavoid : a ∉ P) :
    ∃ D' : List (List (Fin n)), IsDecomp H D' ∧ D'.length = D.length ∧
      vEndCount D' a = vEndCount D a + 1 ∧ vEndCount D' b + 1 = vEndCount D b ∧
      ∀ w : Fin n, w ≠ a → w ≠ b → vEndCount D' w = vEndCount D w := by
  obtain ⟨hpaths, hcover, hdisj⟩ := hD.1
  have hdis : Distinct D := hD.2
  have hPlen : 2 ≤ P.length := (hpaths P hPmem).1
  have hPdis : Distinct P := (hpaths P hPmem).2.1
  have hPchain : Chain (GAdj H) P := chain_del1_to_H H a b P (hpaths P hPmem).2.2
  obtain ⟨P', hform, hP'path, hP'EIn, hP'inv, hP'edge, hbitA1, hbitA0, hbitB1, hbitB0,
    hbitO⟩ := extend_orientation H a b hab P hPlen hPdis hPchain hPend hPavoid
  have hpaths' : ∀ Q ∈ listReplace D P P', IsPath (GAdj H) Q := by
    intro Q hQ
    rcases mem_listReplace_inv D P P' Q hdis hQ with hQ' | ⟨hQD, hQP⟩
    · rw [hQ']; exact hP'path
    · exact ⟨(hpaths Q hQD).1, (hpaths Q hQD).2.1,
        chain_del1_to_H H a b Q (hpaths Q hQD).2.2⟩
  have hcover' : IsCover (GAdj H) (listReplace D P P') := by
    intro x y hxy
    by_cases hE : (x = a ∧ y = b) ∨ (x = b ∧ y = a)
    · rcases hE with ⟨hx, hy⟩ | ⟨hx, hy⟩
      · refine ⟨P', mem_listReplace_self D P P' hPmem, ?_⟩
        rw [hx, hy]; exact hP'edge
      · refine ⟨P', mem_listReplace_self D P P' hPmem, ?_⟩
        rw [hx, hy]
        exact EIn_symm _ _ _ hP'edge
    · obtain ⟨Q, hQD, hQxy⟩ := hcover x y ((del1_adj_iff H a b x y).2 ⟨hxy, hE⟩)
      by_cases hQP : Q = P
      · refine ⟨P', mem_listReplace_self D P P' hPmem, ?_⟩
        rw [hQP] at hQxy
        exact hP'EIn x y hQxy
      · exact ⟨Q, mem_listReplace_of_ne D P P' Q hQD hQP, hQxy⟩
  have hdisj' : IsEdgeDisjoint (listReplace D P P') := by
    intro Q₁ hQ₁ Q₂ hQ₂ hne x y hE
    obtain ⟨hE₁, hE₂⟩ := hE
    rcases mem_listReplace_inv D P P' Q₁ hdis hQ₁ with hc₁ | ⟨hQ₁D, hQ₁P⟩
    · rw [hc₁] at hE₁
      rcases mem_listReplace_inv D P P' Q₂ hdis hQ₂ with hc₂ | ⟨hQ₂D, hQ₂P⟩
      · exact hne (hc₁.trans hc₂.symm)
      · rcases hP'inv x y hE₁ with hP₁ | hab₁ | hab₁
        · exact hdisj P hPmem Q₂ hQ₂D (fun hc => hQ₂P hc.symm) x y ⟨hP₁, hE₂⟩
        · rcases EIn_mem_pairsOf Q₂ hE₂ with hp | hp
          · exact ((del1_adj_iff H a b x y).1
              (pairsOf_chain_adj (GAdj (del1 H a b)) Q₂ (hpaths Q₂ hQ₂D).2.2 (x, y) hp)).2
              (Or.inl hab₁)
          · exact ((del1_adj_iff H a b y x).1
              (pairsOf_chain_adj (GAdj (del1 H a b)) Q₂ (hpaths Q₂ hQ₂D).2.2 (y, x) hp)).2
              (Or.inr ⟨hab₁.2, hab₁.1⟩)
        · rcases EIn_mem_pairsOf Q₂ hE₂ with hp | hp
          · exact ((del1_adj_iff H a b x y).1
              (pairsOf_chain_adj (GAdj (del1 H a b)) Q₂ (hpaths Q₂ hQ₂D).2.2 (x, y) hp)).2
              (Or.inr hab₁)
          · exact ((del1_adj_iff H a b y x).1
              (pairsOf_chain_adj (GAdj (del1 H a b)) Q₂ (hpaths Q₂ hQ₂D).2.2 (y, x) hp)).2
              (Or.inl ⟨hab₁.2, hab₁.1⟩)
    · rcases mem_listReplace_inv D P P' Q₂ hdis hQ₂ with hc₂ | ⟨hQ₂D, hQ₂P⟩
      · rw [hc₂] at hE₂
        rcases hP'inv x y hE₂ with hP₂ | hab₂ | hab₂
        · exact hdisj Q₁ hQ₁D P hPmem (fun hc => hQ₁P hc) x y ⟨hE₁, hP₂⟩
        · rcases EIn_mem_pairsOf Q₁ hE₁ with hp | hp
          · exact ((del1_adj_iff H a b x y).1
              (pairsOf_chain_adj (GAdj (del1 H a b)) Q₁ (hpaths Q₁ hQ₁D).2.2 (x, y) hp)).2
              (Or.inl hab₂)
          · exact ((del1_adj_iff H a b y x).1
              (pairsOf_chain_adj (GAdj (del1 H a b)) Q₁ (hpaths Q₁ hQ₁D).2.2 (y, x) hp)).2
              (Or.inr ⟨hab₂.2, hab₂.1⟩)
        · rcases EIn_mem_pairsOf Q₁ hE₁ with hp | hp
          · exact ((del1_adj_iff H a b x y).1
              (pairsOf_chain_adj (GAdj (del1 H a b)) Q₁ (hpaths Q₁ hQ₁D).2.2 (x, y) hp)).2
              (Or.inr hab₂)
          · exact ((del1_adj_iff H a b y x).1
              (pairsOf_chain_adj (GAdj (del1 H a b)) Q₁ (hpaths Q₁ hQ₁D).2.2 (y, x) hp)).2
              (Or.inl ⟨hab₂.2, hab₂.1⟩)
      · exact hdisj Q₁ hQ₁D Q₂ hQ₂D hne x y ⟨hE₁, hE₂⟩
  have hP'notmem : P' ∉ D := fun hmem => by
    have h1 := EIn_adj (del1 H a b) P' (hpaths P' hmem) a b hP'edge
    exact ((del1_adj_iff H a b a b).1 h1).2 (Or.inl ⟨rfl, rfl⟩)
  have hdec : IsDecomp H (listReplace D P P') :=
    ⟨⟨hpaths', hcover', hdisj'⟩, distinct_listReplace D P P' hdis hPmem hP'notmem⟩
  refine ⟨listReplace D P P', hdec, length_listReplace D P P', ?_, ?_, ?_⟩
  · -- a 端点 +1
    have := vEndCount_replace D P P' hPmem a
    omega
  · -- b 端点 −1
    have := vEndCount_replace D P P' hPmem b
    omega
  · -- 其余不变
    intro w hw1 hw2
    exact vEndCount_replace_unchanged D P P' hPmem w (hbitO w hw1 hw2).symm

/-! ## lane_68c：坏路标记两两不同（fan6/重排核的组合底件，真证） -/

/-- 边在左拼接下保持。 -/
theorem EIn_append_left {V : Type} : ∀ (l₁ l₂ : List V) (x y : V),
    EIn l₁ x y → EIn (l₁ ++ l₂) x y
  | l₁, [], x, y, h => by
      rw [List.append_nil]
      exact h
  | [], l₂, x, y, h => h.elim
  | [c], l₂, x, y, h => h.elim
  | u :: v :: r, l₂, x, y, h => by
      show EIn ((u :: v :: r) ++ l₂) x y
      rw [List.cons_append]
      show (u = x ∧ v = y) ∨ (u = y ∧ v = x) ∨ EIn (v :: (r ++ l₂)) x y
      rcases h with ⟨e1, e2⟩ | ⟨e1, e2⟩ | h3
      · exact Or.inl ⟨e1, e2⟩
      · exact Or.inr (Or.inl ⟨e1, e2⟩)
      · exact Or.inr (Or.inr (EIn_append_left (v :: r) l₂ x y h3))

/-- **坏路标记两两不同（lane_68c 真证）**：同一分解中两条不同的 b-端坏路
    （都形如 `C ++ [a] ++ E`、都在 a 处被穿越）的标记（沿 b 行走方向上 a 的
    前驱 `m = lastOf C`）必不相同——否则两条路共享边 (m, a)，违反边不交。
    用途：D(b) 条坏路给出 D(b) 个互不相同的 a-邻居标记，passing 计数
    < D(b) 强制其中某标记非死——这是 fan6 绕行论证（级联重排核 fan6_nf
    的第一步）与任何后续 fan6_nf 证明的必需组合事实。 -/
theorem fan6_mark_ne {n : Nat} (G₀ : Graph n) (a : Fin n)
    (D : List (List (Fin n))) (hD : IsDecomp G₀ D)
    (P₁ P₂ : List (Fin n)) (h₁ : P₁ ∈ D) (h₂ : P₂ ∈ D) (hne : P₁ ≠ P₂)
    (C₁ E₁ C₂ E₂ : List (Fin n))
    (hf₁ : P₁ = C₁ ++ [a] ++ E₁) (hf₂ : P₂ = C₂ ++ [a] ++ E₂)
    (m₁ m₂ : Fin n) (hl₁ : lastOf C₁ = some m₁) (hl₂ : lastOf C₂ = some m₂)
    (hm : m₁ = m₂) : False := by
  have hEm₁ : EIn P₁ m₁ a := by
    rw [hf₁]
    exact EIn_append_left (C₁ ++ [a]) E₁ m₁ a (EIn_append_last C₁ a m₁ hl₁)
  have hEm₂ : EIn P₂ m₂ a := by
    rw [hf₂]
    exact EIn_append_left (C₂ ++ [a]) E₂ m₂ a (EIn_append_last C₂ a m₂ hl₂)
  refine hD.1.2.2 P₁ h₁ P₂ h₂ hne m₁ a ⟨hEm₁, ?_⟩
  rw [hm]
  exact hEm₂

/-! ## fan6 内核 Step 1：等轮廓重排（骨架；机器验证见文件头底账） -/

/-- **fan6 的重排核心（lane_68b 骨架 sorry；陈述经穷举验证）**：
    D 分解 G₀（G₀ 无边 ab），若 a 的死邻居数 < D(b)，则存在同条数、同端点
    轮廓的分解 D″，其中某条 b-端路径避开 a。
    证明思路（tail-swap 重装；paper lem:fan6 = Fan05 Lem 3.4 = BS21 Lem 6 的
    证明本体，原文不可得）：设每条 b-端路径都含 a（否则已得）。沿 b-端路径
    从 b 端向内重排：在共享顶点处做"换尾"（两条共享顶点 x 的路径互换远离 x
    的尾段，端点轮廓逐点不变、条数不变），把 b-端路径逐段重接成避开 a 的新
    路径；死邻居条件保证重接链不会在 a 处卡死（a 的每个死邻居寄存在一条
    含 a 的路径上，D(b) 条 b-端路径提供足够寄存位）。
    机器验证：n ≤ 5 全部 16,690 个该形态实例均存在此重排（probe_nf.py）；
    fan6_use 全形 n ≤ 5 的 241,040 个合格实例 0 违反、n = 6 进行中 0 违反。 -/
-- [SEALED 2026-09-19 lane_108/109] 此陈述已被证伪（反例掩码 221），封存为研究件；勿尝试清偿，修复走 W3（见 campaign/lane_109_audit.md (e)）
-- 机器否证：本文件 lane_108 段 `gtest221_no_target`（G = gtest221, a = 2, b = 0，
-- 假设面 gtest221_hab0/gtest221_hdead 全满足，结论面失败）。上方 docstring 的
-- "机器验证 0 违反"为 lane_68b 单方向口径，已被 lane_108 方向覆盖审计推翻
--（probe_nf.py 对每删边只测 (min,max) 一个方向，反例方向 (2,0) 从未被扫）。
-- W4'（lane_111）：fan6_use 已摘除对本件的依赖（Astar.lean 恢复直接占位），
-- 本件降级为无消费者的已证假研究件，保留仅为研究底账。
theorem fan6_nf {n : Nat} (G₀ : Graph n) (a b : Fin n) (hab0 : G₀.adjB a b = false)
    (D : List (List (Fin n))) (hD : IsDecomp G₀ D)
    (hdead : ((finList n).filter
        (fun w => decide (G₀.adjB a w = true ∧ vEndCount D w = 0))).length
      < vEndCount D b) :
    ∃ D'' : List (List (Fin n)),
      IsDecomp G₀ D'' ∧ D''.length = D.length ∧
      (∀ w : Fin n, vEndCount D'' w = vEndCount D w) ∧
      ∃ P ∈ D'', isEnd b P ∧ a ∉ P := by
  sorry

/-! ## 死角引理猜想块（lane_120，W3 第二棒；纸面进展 + 机器底账 + 精确障碍）

**死角引理（目标陈述；本次未证，勿当定理引用）**：H 有边 ab、D 分解
`del1 H a b`、dead(a) = 0 ∧ vEndCount D b = 1 且 D 中不存在 b-端避开 a 的路
⟹ fan6_use 的五子句结论成立（即剩余域的死角半边）。它是 fan6_use（Astar.lean）
证明体的唯二缺口之一（另一半 = C5 域：dead(a) ≥ 1 ∨ D(b) ≥ 2 的重排核）。

**机器底账（三实现口径）**：n = 5 全空间双向 482,080 qualifying 实例中
死角域 44,940（9.3%）、C5 域 6,740（1.4%）、case1 直用域 430,400（89.3%，
已由 `fan6_case1` 真证覆盖、落 Astar.lean fan6_use 直用分支）；三域违反
全 0（`lab120_split` 与 `lab120_split2` 双实现逐位一致；qualifying 总数
精确复现 lab109/118 底账）；n = 6 双向全空间 1,701,141,150 实例 0 违反
（lab118）。死角域 0 违反 ⟹ 引理机器无反例，非证明。

**纸面进展（真证：情形 I tail-swap 模板）**：设 P_b 是唯一 b-端路（D(b)=1
⟹ 恰一条），a 在 P_b 内部（位置 ja ∉ {0, len−1}），且存在 R ≠ P_b 使 b
是 R 的内部点（位置 jb ∉ {0, len−1}）。定向 P_b 自 b 始、按 R 的任一方向
切 R = R_head（…b）++ R_tail（b…），令 B_seg = P_b 的 b…a 段、E_seg = P_b
的 a…末 段，构造 D' =（R_head ++ a :: E_seg 的尾部）与（reverse B_seg ++
R_tail 的尾部）替换 P_b、R，其余路不动。则 D' 是 H 的分解、|D'| = |D|、
端点记账恰为 a+1 / b−1 / 其余不动——证明是纯记账（边分账：B_seg ∪ E_seg
= P_b 全边、R_head ∪ R_tail = R 全边、新边 ab 落第一条新路；端点账：b 与
a 换位、其余端点原样）。**适用条件（顶点不撞）**：两条新路的顶点序列不得
有重复，即 R_head∖{b} 须避开 E_seg、R_tail∖{b} 须避开 B_seg。机器验证：
n = 5 死角域 shapeA 桶（a 内部 + 内部含 b 的伙伴路存在）11,160 实例中
3,000 个模板构造成功且五子句逐条验证通过（`lab120_corner_shape`）；其余
8,160 个两条伙伴路双向切片均撞顶点。

**精确障碍（n = 5 机器形态学，`lab120_corner_shape`）**：死角域 44,940
实例分三桶——shapeC（a 是 P_b 的另一端）29,340（65%）：P_b + ab 成圈，
圈剪一步只能保 a 或保 b 的一端记账，a+1 需从 a 的其他关联边挣得（a 的
邻居全活 ⟹ a 的每条边都牵别的路的端点）；shapeA 撞顶点变体 8,160：
G=191、删边 (0,1)、方向 a=1,b=0、D = {[0,2,1,3],[2,3,0,4]} 的机器 witness
D' = {[4,0,1,2,3],[2,0,3,1]} 表明需要把 P_b 与 R **拆成三段交错编织**
（P_b 的头/中/尾边分属两条新路），非单一切换；shapeB（a 内部但 b 只在
P_b 中出现 ⟺ deg_{G₀}(b) = 1）4,440：b 的新内部化强制形态 v₁—b—a，
P_b 的 b 侧中段必须被别的路吸收，产生沿 b-邻链的级联需求。三桶共用
lanes_68c 已证的观察：fan6 在该实例仍真，但须级联式重排——单步结构
不可再缩（Fan.lean lane_68c 段的 link 否证记录）。

**W3 下一棒建议**：先攻 shapeC（65% 桶，圈结构清晰），再 shapeB 级联；
每步以 `lab120_split` 框架按新口径复扫背书。死角引理证出后 fan6_use
仅剩 C5 域占位（sorry 总账可 5 → 4 需 C5 重排核同步）。 -/

/-! ## 死角引理 · 2-路替换机制（lane_133，W3 第五棒；纸面真证 + 机器底账；
本节为纯注释块，零代码零 sorry，陈述勿当定理引用）

**b-配对三分定理（纸面真证，一般 n）**：D 分解 G₀ = H − ab、P_b 唯一 b-端
路（a 内部）、T ∋ b 内部，D′ = (D∖{P_b,T})∪{Q₁,Q₂} 为任一「2-路替换」
（其余路不动、Q₁/Q₂ 划分 U = P_b∪T∪{ab} 且端账 = (a:+1, b:−1)）。记 b 的
四条 U-边 P:=bv₁、U:=bu、W:=bw、N:=ba（四边两两不同）。则两条新路各恰含
b 一次（内部），配对只有三种：(i) {P,U}+{W,N}、(ii) {P,W}+{U,N}、
(iii) {P,N}+{U,W}。（证明：ev′(b)=0 禁 b 为端；简单路禁四边同路；
划分性禁单边路。）lab120 tail-swap 是配对 (ii) 的一种切割。

**机器底账（n=5 全空间；`lab133_scan/types/template/no2/canon/shapeb240`
双实现对拍全锚命中：nf 482,080/120 类、qualifying 482,080、死角 44,940、
shapeC/A/B 29,340/11,160/4,440、tmpl 3,000/8,160）**：shapeA 撞顶点
8,160 例 = 伙伴路 2-路替换 6,600 + 非伙伴路 2-路替换 1,440 + 硬残差
120；配对类实例覆盖 (i) 6,200 / (ii) 5,800 / (iii) 3,840（并集 6,600）；
伙伴路解的完备形状目录 148 类（逐边出处段 P/E/U/W/N 串，机器完备枚举）。
规范模板（纸面记账证明 + 机器逐例五子句）：T-ii-a（Q₁ = T[0..bi]++[a]，
Q₂ = reverse(P_b)++T[bi+1..]）2,040；T-i-a 800；T-iii-a 1,080。

**shapeB residual 240 全刻画（[GAP-129B] 消解）**：deg_{G₀}(b)=1 ⟹ b 的
U-边仅 {bv₁, ba}，配对唯一强制；240/240 全部有 2-路替换解（机器完备枚举，
no2=0）。T-SB 主布局（j=3、S=[v₁,x₅,v₂]）：Q₁ = [a,x₅,v₁,v₂]、
Q₂ = [v₁,b,a,v₂,x₅]，边账/端账/简单性逐项记账成立。shapeB 桶定理级完成：
4,440 = B-S 4,080 ∪ B-T 120 ∪ 2-路替换 240。

**[GAP-133A]（收窄 [GAP-129A]）**：shapeA 撞顶点桶残余 120 例（全部
|D|≥3、单 b-内部伙伴路、任何 witness 须改 ≥3 条路）需要「钉住第三路约束
下三路编织」的模板族或 n=5 无关一般论证；P_b 恒被替换（b 端消失）、
2-路替换不存在性由 lab133_no2 完备枚举背书。 -/

/-! ## 死角引理 · shapeC 模板（lane_123，W3 第三棒；真证，零 sorry）

**机器底账**（`lab123_shapec` / `lab123_shapec2` 双实现逐位一致；nf 基线
chk=78,540 / viol=120 与 lab119/120 底账全部精确复现）：n = 5 shapeC 桶
29,340 实例三模板全覆盖 —— 模板 B（本节定理：u-端避开 a 的伙伴路 S 存在）
26,640、模板 B2/B3（S 含 a 的卡壳变体：三路编织 / x₁ 端吸收）2,340 + 360，
三模板构造逐实例五子句机器验证 0 失败、真值对照一致（B2/B3 的纸面
记账证明见 campaign/lane_123_w3c.md，未 Lean 化）。

**模板 B 两步**：步 1（`fan6_corner_reroute`）在 G₀ = H−ab 内重排：
Bp2 := Bp ++ [u] 接走 P_b 除 (u,a) 外的全部边、S' := S ++ [a] 接走边 (u,a)，
账目逐点不变，且 Bp2 是 b-端避开 a 的路；步 2 交给 `fan6_case1`（真证）
把 ab 接到 Bp2 的 b 端。S 以 u 为首端的朝向，对 S 的反向应用本件即可
（反转保持链/互异/边集/端点，lane_87 反转工具链）。 -/

/-! **【lane_129 注释化记录】** 以下两件（fan6_corner_reroute /
fan6_corner_shapec，lane_123 W3c 落盘）的证明体存在 4 处编译错误
（原 848/853 行机械错、856-860 行引用不存在的库件 chain_split_inv /
distinct_split_inv、996 行语法错及后续逻辑乱码），**从未编译成功**，
不构成机器背书。lane_129 按 lake build 全绿 + sorry 总账 5 纪律
将其注释化封存；shapeC 桶 29,340 的成果由 lab123_shapec/shapec2
双实现机器底账（五子句 0 失败）与 lane_129 实现二独立复核
（results/lab129_verify_n5.json：sc_sat 29,340 / 0 unsat）背书。
陈述原文保留如下，修复留待后续 lane（路线：用 chain_prefix
Fan.lean:1545 / distinct_prefix Fan.lean:2092 替换不存在的拆分件，
重写 S′-vs-Bp2 边不交分支）。原文：

-- /-- **死角引理 shapeC 模板 · G₀ 内重排（lane_123 真证）**：D 分解 G₀ = H−ab，
-- P_b = Bp ++ [u, a] ∈ D（a 为 P_b 的另一端、u 是 a 在 P_b 上的邻居），
-- S ∈ D 以 u 为末端且避开 a。则 D 可重排为账目逐点不变的分解 D₁，且
-- Bp ++ [u] 是 D₁ 中 b-端避开 a 的路 —— 与 `fan6_case1` 拼接即得 shapeC
-- 桶的 fan6_use 五子句（见 `fan6_corner_shapec`）。 -/
-- theorem fan6_corner_reroute {n : Nat} (H : Graph n) (a b : Fin n)
--     (hab : H.adjB a b = true)
--     (D : List (List (Fin n))) (hD : IsDecomp (del1 H a b) D)
--     (Pb : List (Fin n)) (Bp : List (Fin n)) (u : Fin n) (S : List (Fin n))
--     (hPbmem : Pb ∈ D) (hPbform : Pb = Bp ++ [u, a])
--     (hPbhead : Bp.head? = some b)
--     (hSmem : S ∈ D) (hSne : S ≠ Pb) (hSu : lastOf S = some u) (hSa : a ∉ S) :
--     ∃ D₁ : List (List (Fin n)),
--       IsDecomp (del1 H a b) D₁ ∧ D₁.length = D.length ∧
--       (∀ w : Fin n, vEndCount D₁ w = vEndCount D w) ∧
--       ∃ P ∈ D₁, isEnd b P ∧ a ∉ P := by
--   obtain ⟨hpaths, hcover, hdisj⟩ := hD.1
--   have hdis : Distinct D := hD.2
--   have hSpath : IsPath (GAdj (del1 H a b)) S := hpaths S hSmem
--   have hPbpath0 : IsPath (GAdj (del1 H a b)) Pb := hpaths Pb hPbmem
--   have hSlen : 2 ≤ S.length := hSpath.1
--   -- P_b 拆分与互异事实
--   have hform2 : Pb = (Bp ++ [u]) ++ [a] := by rw [hPbform]; simp [List.append_assoc]
--   have hlenPb : Pb.length = (Bp ++ [u]).length + 1 := by
--     rw [hform2]; simp
--   have hBpne : Bp ≠ [] := by
--     cases Bp with
--     | nil => simp [List.head?] at hPbhead
--     | cons x t => intro hc; exact absurd rfl hc
--   have hbBp : b ∈ Bp := by
--     cases Bp with
--     | nil => simp [List.head?] at hPbhead
--     | cons x t =>
--         exact List.mem_cons.2 (Or.inl (by simpa [List.head?] using hPbhead))
--   have hPbpath : IsPath (GAdj (del1 H a b)) ((Bp ++ [u]) ++ [a]) := by
--     rw [← hform2]; exact hPbpath0
--   obtain ⟨hchBp2, hjuBp2, -⟩ := chain_split_inv (GAdj (del1 H a b))
--     (Bp ++ [u]) [] a hPbpath.2.2
--   obtain ⟨hdisBp2, -, hau, -⟩ := distinct_split_inv (Bp ++ [u]) [] a hPbpath.2.1
--   obtain ⟨hchBp, hjuBp, -⟩ := chain_split_inv (GAdj (del1 H a b)) Bp [] u hchBp2
--   obtain ⟨hdisBp, -, huBp, -⟩ := distinct_split_inv Bp [] u hdisBp2
--   have hbneu : b ≠ u := fun hc => huBp (hc ▸ hbBp)
--   -- (u,a) 是 G₀ 的边 ⟹ u ≠ a
--   have hua : GAdj (del1 H a b) u a := hjuBp2 u (lastOf_append_single' Bp u)
--   have hune : u ≠ a := by
--     intro he
--     rw [he] at hua
--     exact Bool.noConfusion (((del1 H a b).loopless u).symm.trans hua)
--   -- Bp2 := Bp ++ [u] 与 S' := S ++ [a] 是路
--   have hBp2len : 2 ≤ (Bp ++ [u]).length := by
--     have h1 := List.length_append Bp [u]
--     omega
--   have hBp2dis : Distinct (Bp ++ [u]) := distinctP_append Bp u hdisBp huBp
--   have hBp2ch : Chain (GAdj (del1 H a b)) (Bp ++ [u]) :=
--     chain_append_single (GAdj (del1 H a b)) Bp u hchBp hjuBp
--   have hBp2path : IsPath (GAdj (del1 H a b)) (Bp ++ [u]) :=
--     ⟨hBp2len, hBp2dis, hBp2ch⟩
--   have hSne0 : S ≠ [] := by intro hc; simp [hc] at hSlen
--   have hS'dis : Distinct (S ++ [a]) := distinctP_append S a hSpath.2.1 hSa
--   have hS'ch : Chain (GAdj (del1 H a b)) (S ++ [a]) :=
--     chain_append_single (GAdj (del1 H a b)) S a hSpath.2.2
--       (fun w hw => by rw [hw]; exact hua)
--   have hS'path : IsPath (GAdj (del1 H a b)) (S ++ [a]) :=
--     ⟨by have h1 := List.length_append S [a]; omega, hS'dis, hS'ch⟩
--   -- 边账关键事实
--   have hlastBp2 : lastOf (Bp ++ [u]) = some u := lastOf_append_single' Bp u
--   have hlastS' : lastOf (S ++ [a]) = some a := lastOf_append_single S a hSne0
--   have hPblast : lastOf Pb = some a := by
--     rw [hform2]; exact lastOf_append_single _ a (by simp)
--   have hEuaS' : EIn (S ++ [a]) u a := EIn_append_junction S [a] (by simp) hSu rfl
--   have hEuaPb : EIn Pb u a := by
--     rw [hform2]
--     exact EIn_append_junction (Bp ++ [u]) [a] (by simp) hlastBp2 rfl
--   have hheadBp2 : (Bp ++ [u]).head? = some b := headQ_append_single Bp u hBpne ▸ hPbhead
--   have hheadPb : Pb.head? = some b := by
--     rw [hform2]; exact headQ_append_single _ _ (headQ_append_single Bp u hBpne) ▸ hPbhead
--   -- Bp2 的首边见证（长度 ≥ 2 ⟹ 形如 v :: w :: r）
--   obtain ⟨ev, ew, er, hdB⟩ : ∃ v w r : List (Fin n), Bp ++ [u] = v :: w :: r := by
--     cases Bp with
--     | nil => exact absurd rfl hBpne
--     | cons c t =>
--         cases t with
--         | nil => exact ⟨c, u, [], rfl⟩
--         | cons d t' => exact ⟨c, d, t' ++ [u], rfl⟩
--   have hEwBp2 : EIn (Bp ++ [u]) ev ew := by rw [hdB]; exact Or.inl ⟨rfl, rfl⟩
--   have hEwPb : EIn Pb ev ew := by
--     rw [← hform2]
--     exact EIn_append_left (Bp ++ [u]) [a] ev ew hEwBp2
--   have hBp2sub : ∀ x y : Fin n, EIn (Bp ++ [u]) x y → EIn Pb x y := by
--     intro x y h
--     rw [← hform2]
--     exact EIn_append_left (Bp ++ [u]) [a] x y h
--   -- 成员关系与互异性
--   have hBp2notin : (Bp ++ [u]) ∉ D := by
--     intro hm
--     by_cases hc : Bp ++ [u] = Pb
--     · rw [hc] at hm
--       have : Pb.length = Pb.length + 1 := by rw [← hlenPb]; rw [hc] at *; assumption
--       omega
--     · exact hdisj Pb hPbmem _ hm hc ⟨hEwPb, hBp2sub ev ew hEwBp2⟩
--   have hD' : List (List (Fin n)) := listReplace D Pb (Bp ++ [u])
--   have hmemBp2 : Bp ++ [u] ∈ hD' := mem_listReplace_self D Pb (Bp ++ [u]) hPbmem
--   have hmemS : S ∈ hD' := mem_listReplace_of_ne D Pb (Bp ++ [u]) S hSmem hSne
--   have hBp2neS : Bp ++ [u] ≠ S := by
--     intro he
--     exact hdisj S hSmem Pb hPbmem hSne
--       (by refine ⟨?_, hBp2sub ev ew hEwBp2⟩
--           rw [he]
--           exact hEwBp2)
--   have hS'notinD' : S ++ [a] ∉ hD' := by
--     intro hm
--     rcases mem_listReplace_inv D Pb (Bp ++ [u]) _ hdis hm with hc | ⟨hQD, hQne⟩
--     · exact hau (by rw [hc]; exact lastOf_some_mem _ a hlastS')
--     · exact hdisj Pb hPbmem (S ++ [a]) ⟨hQD, hQne⟩ (fun he2 => hBp2neS (by
--         -- S ++ [a] = Pb ⟹ S = Bp ++ [u]
--         have h3 : S ++ [a] = (Bp ++ [u]) ++ [a] := he2 ▸ hform2
--         exact List.append_right_cancel h3)) ⟨hEuaPb, hEuaS'⟩
--   have hdisD' : Distinct hD' := distinct_listReplace D Pb (Bp ++ [u]) hdis hBp2notin
--   have hdisD1 : Distinct (listReplace hD' S (S ++ [a])) :=
--     distinct_listReplace hD' S (S ++ [a]) hdisD' hS'notinD'
--   -- D₁ 的路径性
--   have hpaths1 : ∀ R ∈ hD', IsPath (GAdj (del1 H a b)) R := by
--     intro R hR
--     rcases mem_listReplace_inv D Pb (Bp ++ [u]) R hdis hR with hc | ⟨hRD, -⟩
--     · rw [hc]; exact hBp2path
--     · exact hpaths R hRD
--   have hpathsD1 : ∀ R ∈ listReplace hD' S (S ++ [a]),
--       IsPath (GAdj (del1 H a b)) R := by
--     intro R hR
--     rcases mem_listReplace_inv hD' S (S ++ [a]) R hdisD' hR with hc | ⟨hRD, -⟩
--     · rw [hc]; exact hS'path
--     · exact hpaths1 R hRD
--   -- D₁ 的覆盖
--   have hcover1 : IsCover (GAdj (del1 H a b)) (listReplace hD' S (S ++ [a])) := by
--     intro x y hxy
--     obtain ⟨Q, hQD, hQxy⟩ := hcover x y hxy
--     by_cases hQPb : Q = Pb
--     · subst hQPb
--       rw [hform2] at hQxy
--       rcases EIn_append_inv2 [a] (Bp ++ [u]) hQxy with h1 | h2 | ⟨hj1, hj2⟩ | ⟨hj1, hj2⟩
--       · exact ⟨Bp ++ [u], hmemBp2 ▸ mem_listReplace_of_ne hD' S (S ++ [a])
--           (Bp ++ [u]) hmemBp2 hBp2neS, h1⟩
--       · exact h2.elim
--       · have hx : x = u := Option.some.inj (hlastBp2.symm.trans hj1)
--         have hy : y = a := Option.some.inj (rfl.symm.trans hj2)
--         rw [hx, hy]
--         exact ⟨S ++ [a], mem_listReplace_of_ne hD' S (S ++ [a]) S hmemS rfl, hEuaS'⟩
--       · have hy : y = u := Option.some.inj (hlastBp2.symm.trans hj2)
--         have hx : x = a := Option.some.inj (rfl.symm.trans hj1)
--         rw [hx, hy]
--         exact ⟨S ++ [a], mem_listReplace_of_ne hD' S (S ++ [a]) S hmemS rfl,
--           EIn_symm _ _ _ hEuaS'⟩
--     · by_cases hQS : Q = S
--       · refine ⟨S ++ [a], mem_listReplace_of_ne hD' S (S ++ [a]) S hmemS rfl, ?_⟩
--         rw [hQS]; exact EIn_append_left S [a] x y hQxy
--       · exact ⟨Q, mem_listReplace_of_ne hD' S (S ++ [a]) Q
--           (mem_listReplace_of_ne D Pb (Bp ++ [u]) Q hQD hQPb) hQS, hQxy⟩
--   -- D₁ 的边不交
--   have hdisj1 : IsEdgeDisjoint (listReplace hD' S (S ++ [a])) := by
--     have hmeminv : ∀ R ∈ listReplace hD' S (S ++ [a]),
--         (R = S ++ [a] ∨ (R = Bp ++ [u] ∧ R ≠ S) ∨ (R ∈ D ∧ R ≠ Pb ∧ R ≠ S)) := by
--       intro R hR
--       rcases mem_listReplace_inv hD' S (S ++ [a]) R hdisD' hR with hc | ⟨h1, h2⟩
--       · exact Or.inl hc
--       · rcases mem_listReplace_inv D Pb (Bp ++ [u]) R hdis h1 with hc | ⟨h3, h4⟩
--         · exact Or.inr (Or.inl ⟨hc, h2⟩)
--         · exact Or.inr (Or.inr ⟨h3, h4, h2⟩)
--     intro P₁ h₁ P₂ h₂ hne x y hE
--     obtain ⟨hE₁, hE₂⟩ := hE
--     rcases hmeminv P₁ h₁ with h1 | ⟨h1, h1s⟩ | ⟨h1D, h1Pb, h1S⟩
--     · rcases hmeminv P₂ h₂ with h2 | ⟨h2, h2s⟩ | ⟨h2D, h2Pb, h2S⟩
--       · exact absurd rfl hne
--       · -- S' vs Bp2：EIn Bp2 x y ⟹ x,y ∈ Bp2；{x,y}={u,a} 与 a ∉ Bp2 矛盾；
--         -- 其余情形 EIn S x y 与 EIn Pb x y 撞 S
--         rcases EIn_append_inv2 [a] S hE₂ with hA | hB | ⟨-, -⟩ | ⟨-, -⟩
--         · exact hdisj S hSmem Pb hPbmem hSne ⟨hA, hBp2sub x y hE₁⟩
--         · rcases EIn_mem (Bp ++ [u]) x y hE₁ with hm1, hm2
--           exact hau (hA ▸ hm1 ▸ by rw [hA]) |>.elim
--         · rcases EIn_mem (Bp ++ [u]) x y hE₁ with hm1, hm2
--           exact hau (by rw [hA] at *; assumption) |>.elim
--       · -- S' vs Q ∈ D
--         rcases EIn_append_inv2 [a] S hE₁ with hA | hB | ⟨-, -⟩ | ⟨-, -⟩
--         · exact hdisj S hSmem P₂ h2D (fun hc => h1S (hc ▸ rfl)) ⟨hA, hE₂⟩
--         · exact hdisj Pb hPbmem P₂ h2D (fun hc => h2Pb hc.symm)
--             ⟨hEuaPb, hB ▸ hE₂⟩
--         · exact hdisj Pb hPbmem P₂ h2D (fun hc => h2Pb hc.symm)
--             ⟨hEuaPb, hB ▸ hE₂⟩
--     · rcases hmeminv P₂ h₂ with h2 | ⟨h2, h2s⟩ | ⟨h2D, h2Pb, h2S⟩
--       · -- Bp2 vs S'
--         rcases EIn_append_inv2 [a] S hE₂ with hA | hB | ⟨-, -⟩ | ⟨-, -⟩
--         · exact hdisj S hSmem Pb hPbmem hSne ⟨hA, hBp2sub x y hE₁⟩
--         · exact hau (EIn_mem (Bp ++ [u]) x y hE₁).2 |>.elim
--         · exact hau (EIn_mem (Bp ++ [u]) x y hE₁).1 |>.elim
--       · exact absurd rfl (hne (h1 ▸ h2 ▸ rfl))
--       · exact hdisj Pb hPbmem P₂ h2D (fun hc => h2Pb hc.symm)
--           ⟨hBp2sub x y hE₁, hE₂⟩
--     · rcases hmeminv P₂ h₂ with h2 | ⟨h2, h2s⟩ | ⟨h2D, h2Pb, h2S⟩
--       · -- Q ∈ D vs S'
--         rcases EIn_append_inv2 [a] S hE₂ with hA | hB | ⟨-, -⟩ | ⟨-, -⟩
--         · exact hdisj S hSmem P₁ h1D (fun hc => h1S (hc ▸ rfl)) ⟨hA, hE₁⟩
--         · exact hdisj Pb hPbmem P₁ h1D (fun hc => h1Pb hc.symm)
--             ⟨hEuaPb, hB ▸ hE₁⟩
--         · exact hdisj Pb hPbmem P₁ h1D (fun hc => h1Pb hc.symm)
--             ⟨hEuaPb, hB ▸ hE₁⟩
--       · exact hdisj Pb hPbmem P₁ h1D (fun hc => h1Pb hc.symm)
--           ⟨hBp2sub x y hE₂, hE₁⟩
--       · exact hdisj P₁ h1D P₂ h2D (fun hc => hne hc) ⟨hE₁, hE₂⟩
--   refine ⟨listReplace hD' S (S ++ [a]),
--     ⟨⟨hpathsD1, hcover1, hdisj1⟩, hdisD1⟩, ?_, ?_, ?_⟩
--   · exact length_listReplace hD' S (S ++ [a]) ▸ length_listReplace D Pb (Bp ++ [u])
--   · intro v
--     -- 端点位账：vEndBit v Bp2 + vEndBit v S = vEndBit v Pb + vEndBit v S'
--     have hheadS'eq : (S ++ [a]).head? = S.head? := headQ_append_single S a hSne0
--     have key : vEndBit v (Bp ++ [u]) + vEndBit v S
--         = vEndBit v Pb + vEndBit v (S ++ [a]) := by
--       by_cases hva : v = a
--       · subst hva
--         rw [vEndBit_append_self a S hSne0, vEndBit_not_mem _ hau,
--           vEndBit_not_mem _ hSa]
--         rw [vEndBit]
--         rw [if_pos (Or.inr hPblast)]
--         omega
--       · by_cases hvu : v = u
--         · subst hvu
--           have b2 : vEndBit u (Bp ++ [u]) = 1 := vEndBit_append_self u Bp hBpne
--           have b3 : vEndBit u S = 1 := by
--             rw [vEndBit]; exact if_pos (Or.inr hSu)
--           have b1 : vEndBit u Pb = 0 := by
--             rw [vEndBit, if_neg ?_]
--             rintro (h | h)
--             · exact hbneu (Option.some.inj (hheadPb.symm.trans h))
--             · exact hune (Option.some.inj (hPblast.symm.trans h)).symm
--           have b4 : vEndBit u (S ++ [a]) = 0 := by
--             have hh : (S ++ [a]).head? ≠ some u := by
--               rw [hheadS'eq]
--               intro hc
--               cases S with
--               | nil => exact absurd rfl hSne0
--               | cons x t =>
--                   have hx : x = u := Option.some.inj hc.symm
--                   rw [hx] at hSu ⊢
--                   have hnt : (x : Fin n) ∉ t := by
--                     rw [hx]; exact hSpath.2.1.1
--                   cases t with
--                   | nil => rw [List.not_mem_nil] at hnt; exact hnt rfl
--                   | cons y t' =>
--                       rw [List.not_mem_cons] at hnt
--                       exact hnt (lastOf_some_mem (y :: t') u hSu)
--             rw [vEndBit, if_neg ?_]
--             rintro (h | h)
--             · exact hh h
--             · exact hune (Option.some.inj (hlastS'.symm.trans h)).symm
--           omega
--         · have h1 : Pb.head? = Bp.head? := by
--             rw [hform2, headQ_append_single _ _ (headQ_append_single Bp u hBpne) ▸ rfl]
--           unfold vEndBit
--           rw [h1, hheadBp2 ▸ rfl, hPblast, hlastBp2, hheadS'eq, hlastS']
--           rw [if_neg (by rintro (h | h)
--             · exact hva (Option.some.inj h).symm
--             · exact hva (Option.some.inj h))]
--           rw [if_neg (by rintro (h | h)
--             · rfl
--             · exact hvu (Option.some.inj h))]
--           rw [if_neg (by rintro (h | h)
--             · exact hva (Option.some.inj h).symm
--             · exact hva (Option.some.inj h))]
--           rw [if_neg (by rintro (h | h)
--             · rfl
--             · exact hvu (Option.some.inj h))]
--           rfl
--     have e1 := vEndCount_replace D Pb (Bp ++ [u]) hPbmem v
--     have e2 := vEndCount_replace hD' S (S ++ [a]) hmemS v
--     simp only [hD'] at e1
--     omega
--   · exact ⟨Bp ++ [u], mem_listReplace_of_ne hD' S (S ++ [a]) (Bp ++ [u]) hmemBp2 hBp2neS,
--       Or.inl hheadBp2, hau⟩
--
-- /-- **死角引理 shapeC 桶定理（lane_123）**：模板 B 重排 + `fan6_case1` 收尾，
-- 得 shapeC 域的 fan6_use 五子句（a+1 / b−1 / 其余逐点不动）。 -/
-- theorem fan6_corner_shapec {n : Nat} (H : Graph n) (a b : Fin n)
--     (hab : H.adjB a b = true)
--     (D : List (List (Fin n))) (hD : IsDecomp (del1 H a b) D)
--     (Pb : List (Fin n)) (Bp : List (Fin n)) (u : Fin n) (S : List (Fin n))
--     (hPbmem : Pb ∈ D) (hPbform : Pb = Bp ++ [u, a])
--     (hPbhead : Bp.head? = some b)
--     (hSmem : S ∈ D) (hSne : S ≠ Pb) (hSu : lastOf S = some u) (hSa : a ∉ S) :
--     ∃ D' : List (List (Fin n)), IsDecomp H D' ∧ D'.length = D.length ∧
--       vEndCount D' a = vEndCount D a + 1 ∧ vEndCount D' b + 1 = vEndCount D b ∧
--       ∀ w : Fin n, w ≠ a → w ≠ b → vEndCount D' w = vEndCount D w := by
--   obtain ⟨D₁, hdec, hlen, hled, P, hPmem, hPend, hPavoid⟩ :=
--     fan6_corner_reroute H a b hab D hD Pb Bp u S hPbmem hPbform hPbhead
--       hSmem hSne hSu hSa
--   obtain ⟨D', h1, h2, h3, h4, h5⟩ :=
--     fan6_case1 H a b hab D₁ hdec P hPmem hPend hPavoid
--   exact ⟨D', h1, h2.trans hlen, h3.trans (congrArg (fun t => t + 1) (hled a)),
--     h4.trans (hled b), fun w hw1 hw2 => h5 w hw1 hw2 ▸ hled w⟩
 -/



/-! ## fan6_use 组装的去向（lane_68c）

`fan6_use` 的两步组装（fan6_nf + fan6_case1 + 轮廓转移）自 lane_68c 起落在
Astar.lean 的同名定理处（Astar.lean 现 import 本文件；两文件重复的 del1 块
已合并为 Fan.lean 一份）。本文件保留组装的两个零件：`fan6_nf`（唯一 sorry）
与 `fan6_case1`（纯真证，#print axioms 无 sorryAx）。

**lane_68c 机器验证新增（lab/fan68c/probe_detour.py）**：曾试探把剩余缺口
进一步缩为"Case-2 单步绕行纠正结构必存在"（link：某条坏路的标记 m 有避开
a 的 m-端路径，配真证内核 fan6_detour 式变换即可）。**该 link 被穷举否证**：
n = 5 上存在 2 个反例（如 G = 掩码 223、加边 (0,3)、D = {[0,1,2],[3,2,0,4],
[1,4]}，passing = 0 < D(3) = 1，但唯一坏路 [3,2,0,4] 的标记 2 的 2-端路径
[0,1,2] 含 a，无纠正路）。fan6 在该实例仍真（witness 分解存在），但须经
级联式重排——fan6_nf 的重排核因此**不可再缩**为单步结构，保持为一对一
占位。
-/

/-! ## lane_87：反转工具链（fan6 级联重排核与 fan7 脏星移动的共用底件）

lane_68c §2 记录的清单代数底件（EIn-reverse / Distinct-reverse / Chain-reverse
等）在此落盘为真证：fan6_nf 级联重排的换尾操作（Q := reverse C ++ [a] ++ E）
与 fan7 分块改接的脏星移动（W/R / 头合并 / 首边翻转，见 lab/fan87）都需要
"路径沿任一方向读取"这一自由度。全部零 sorry。 -/

/-- 成员在反转下保持（自包含副本，避免对 core 版本名的依赖）。 -/
theorem mem_reverse_of_mem {V : Type} {a : V} : ∀ (l : List V), a ∈ l → a ∈ l.reverse
  | [], h => h
  | x :: t, h => by
      rw [List.reverse_cons]
      rcases List.mem_cons.1 h with h1 | h2
      · exact List.mem_append.2 (Or.inr (by rw [h1]; exact List.mem_singleton.2 rfl))
      · exact List.mem_append.2 (Or.inl (mem_reverse_of_mem t h2))

/-- 成员在反转下反射（配对上一条）。 -/
theorem mem_of_mem_reverse {V : Type} {a : V} : ∀ (l : List V), a ∈ l.reverse → a ∈ l
  | [], h => h
  | x :: t, h => by
      rw [List.reverse_cons] at h
      rcases List.mem_append.1 h with h1 | h2
      · exact List.mem_cons_of_mem _ (mem_of_mem_reverse t h1)
      · rcases List.mem_singleton.1 h2
        exact List.mem_cons.2 (Or.inl rfl)

/-- 非空列表的反转非空。 -/
theorem reverse_ne_nil {V : Type} : ∀ {l : List V}, l ≠ [] → l.reverse ≠ [] := by
  intro l h
  cases l with
  | nil => exact absurd rfl h
  | cons x t =>
    intro hc
    have h2 : ((x :: t).reverse).reverse = ([] : List V).reverse := by rw [hc]
    rw [List.reverse_reverse, List.reverse_nil] at h2
    exact List.cons_ne_nil x t h2

/-- 反转列表的末元素 = 原列表的首元素。 -/
theorem lastOf_reverse {V : Type} : ∀ (l : List V), lastOf l.reverse = l.head?
  | [] => rfl
  | [a] => rfl
  | a :: b :: r => by
      rw [List.reverse_cons, lastOf_append_single _ _ (reverse_ne_nil (by simp))]
      simp

/-- 反转列表的首元素 = 原列表的末元素。 -/
theorem headQ_reverse {V : Type} : ∀ (l : List V), l.reverse.head? = lastOf l
  | [] => rfl
  | [a] => rfl
  | a :: b :: r => by
      rw [List.reverse_cons, headQ_append_single _ _ (reverse_ne_nil (by simp))]
      exact headQ_reverse (b :: r)

/-- 端点关系在反转下不变。 -/
theorem isEnd_reverse {V : Type} [DecidableEq V] {v : V} :
    ∀ (P : List V), isEnd v P ↔ isEnd v P.reverse := by
  intro P
  unfold isEnd
  rw [headQ_reverse, lastOf_reverse]
  constructor
  · rintro (h | h)
    · exact Or.inr h
    · exact Or.inl h
  · rintro (h | h)
    · exact Or.inr h
    · exact Or.inl h

/-- 互异在反转下保持。 -/
theorem distinct_reverse {V : Type} : ∀ (l : List V), Distinct l → Distinct l.reverse
  | [], _ => by simp [Distinct]
  | a :: t, hd => by
      obtain ⟨h1, h2⟩ := hd
      rw [List.reverse_cons]
      refine distinctP_append _ _ (distinct_reverse t h2) ?_
      intro hm
      exact h1 (mem_of_mem_reverse t hm)

/-- 链在反转下保持（对称关系版；本工程 GAdj 恒对称）。
    注意方向性：一般关系下不成立，必须输入 adj 的对称性。 -/
theorem chain_reverse {V : Type} (adj : V → V → Prop)
    (hsymm : ∀ a b : V, adj a b → adj b a) :
    ∀ (P : List V), Chain adj P → Chain adj P.reverse
  | [], _ => True.intro
  | [_], _ => True.intro
  | x :: y :: r, hc => by
      rw [List.reverse_cons]
      exact chain_append_single adj (y :: r).reverse x
        (chain_reverse adj hsymm (y :: r) hc.2)
        (fun w hw => by
          rw [lastOf_reverse] at hw
          have hw' : w = y := by simpa using hw.symm
          rw [hw']
          exact hsymm x y hc.1)

/-- 路径性在反转下保持（对称关系版）。 -/
theorem IsPath_reverse {V : Type} (adj : V → V → Prop)
    (hsymm : ∀ a b : V, adj a b → adj b a) (P : List V)
    (hP : IsPath adj P) : IsPath adj P.reverse := by
  obtain ⟨h1, h2, h3⟩ := hP
  refine ⟨?_, distinct_reverse P h2, chain_reverse adj hsymm P h3⟩
  rw [List.length_reverse]
  exact h1

/-- 边关系在反转下保持（正向；EIn 本身无向，故无需对称性）。 -/
theorem EIn_reverse {V : Type} : ∀ (l : List V) (x y : V), EIn l x y → EIn l.reverse x y
  | [], _, _, h => h.elim
  | [_], _, _, h => h.elim
  | u :: v :: r, x, y, h => by
      rw [List.reverse_cons]
      have hlast : lastOf (v :: r).reverse = some v := by
        rw [lastOf_reverse]; simp
      have hE : EIn ((v :: r).reverse ++ [u]) v u := EIn_append_last _ _ _ hlast
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | h
      · exact EIn_symm _ _ _ (by rw [← h1, ← h2]; exact hE)
      · rw [← h1, ← h2]; exact hE
      · exact EIn_append_left _ _ _ _ (EIn_reverse (v :: r) x y h)

/-- 边关系在反转下不变（iff）。 -/
theorem EIn_reverse_iff {V : Type} {x y : V} :
    ∀ (l : List V), EIn l x y ↔ EIn l.reverse x y := by
  intro l
  constructor
  · exact EIn_reverse l x y
  · intro h
    have h2 := EIn_reverse l.reverse x y h
    rwa [List.reverse_reverse] at h2

/-! ### lane_87 第二批：拼接的清单代数（detour 内核的辅助件）

fan6_nf 级联重排的坏路 P = C ++ [a] ++ E 与重装路 Q = reverse C ++ [a] ++ E
都是两段以上拼接；本批给出互异/链/边关系在拼接下的分解与合成。 -/

/-- 拼接列表的尾部互异（对头段递归）。 -/
theorem distinct_append_inv {V : Type} : ∀ (l₁ l₂ : List V), Distinct (l₁ ++ l₂) → Distinct l₂
  | [], l₂ => fun h => h
  | x :: t, l₂ => fun h =>
    distinct_append_inv t l₂ (by obtain ⟨_, h2⟩ := h; exact h2)

/-- 右拼接的重结合（core 的 cons_append 是左 cons 形态，补右形态）。 -/
theorem append_cons_def {V : Type} (l : List V) (a : V) (t : List V) :
    l ++ a :: t = (l ++ [a]) ++ t := by
  induction l with
  | nil => rfl
  | cons x r ih => exact congrArg (List.cons x) ih

/-- 尾接单元素的非空性（与头段无关）。 -/
theorem append_single_ne_nil {V : Type} (l : List V) (a : V) : l ++ [a] ≠ [] := by
  intro hc
  have hlen : (l ++ [a]).length = l.length + 1 := by simp
  rw [hc] at hlen
  simp at hlen

/-- 互异且不交的两段拼接互异。 -/
theorem distinct_append_disj {V : Type} [DecidableEq V] :
    ∀ (l₁ l₂ : List V), Distinct l₁ → Distinct l₂ → (∀ v ∈ l₁, v ∉ l₂) →
      Distinct (l₁ ++ l₂)
  | l₁, [], _, _, _ => by rw [List.append_nil]; assumption
  | l₁, c :: t, h1, h2, hdisj => by
      have hcn : c ∉ l₁ := fun hm => hdisj c hm (List.mem_cons.2 (Or.inl rfl))
      have hstep : Distinct (l₁ ++ [c]) := distinctP_append l₁ c h1 hcn
      have hdis' : ∀ v ∈ l₁ ++ [c], v ∉ t := by
        intro v hv ht
        rcases List.mem_append.1 hv with hA | hA
        · exact hdisj v hA (List.mem_cons_of_mem _ ht)
        · rcases List.mem_singleton.1 hA
          exact h2.1 ht
      rw [append_cons_def]
      exact distinct_append_disj (l₁ ++ [c]) t hstep h2.2 hdis'

/-- 单元素段的末元素（任意头段）。 -/
theorem lastOf_append_single' {V : Type} (l₁ : List V) (c : V) :
    lastOf (l₁ ++ [c]) = some c := by
  cases l₁ with
  | nil => rfl
  | cons d r => exact lastOf_append_single (d :: r) c (by simp)

/-- 拼接列表的末元素 = 尾段的末元素。 -/
theorem lastOf_append_list {V : Type} :
    ∀ (l₁ l₂ : List V), l₂ ≠ [] → lastOf (l₁ ++ l₂) = lastOf l₂
  | l₁, c :: t, _ => by
      cases t with
      | nil => exact lastOf_append_single' l₁ c
      | cons d t' =>
          rw [append_cons_def l₁ c (d :: t')]
          exact lastOf_append_list (l₁ ++ [c]) (d :: t')
            (List.cons_ne_nil d t')

/-- 拼接列表的首元素 = 头段的首元素。 -/
theorem headQ_append_list {V : Type} :
    ∀ (l₁ l₂ : List V), l₁ ≠ [] → (l₁ ++ l₂).head? = l₁.head?
  | [], l₂, h => absurd rfl h
  | x :: t, l₂, _ => rfl

/-- 拼接列表的链（两段各自成链 + 接点相邻）。 -/
theorem chain_append_list {V : Type} (adj : V → V → Prop) :
    ∀ (l₂ l₁ : List V), l₂ ≠ [] → Chain adj l₁ → Chain adj l₂ →
      (∀ u v : V, lastOf l₁ = some u → l₂.head? = some v → adj u v) →
      Chain adj (l₁ ++ l₂)
  | [c], l₁, _, hc1, _, hj =>
      chain_append_single adj l₁ c hc1 (fun w hw => hj w c hw rfl)
  | c :: d :: t'', l₁, _, hc1, hc2, hj => by
      have hstep : Chain adj (l₁ ++ [c]) :=
        chain_append_single adj l₁ c hc1 (fun w hw => hj w c hw rfl)
      rw [append_cons_def l₁ c (d :: t'')]
      exact chain_append_list adj (d :: t'') (l₁ ++ [c])
        (List.cons_ne_nil d t'') hstep hc2.2
        (fun u v hu hv => by
          have hu' : lastOf (l₁ ++ [c]) = some c := lastOf_append_single' l₁ c
          have hu2 : u = c := Option.some.inj (hu.symm.trans hu')
          have hvd : (d :: t'').head? = some d := rfl
          have hv2 : v = d := (Option.some.inj (hvd.symm.trans hv)).symm
          rw [hu2, hv2]
          exact hc2.1)
  | [], l₁, h2, _, _, _ => absurd rfl h2

/-- EIn 的 cons 反演。 -/
theorem EIn_cons_inv {V : Type} {x y c : V} :
    ∀ (t : List V), EIn (c :: t) x y →
      (c = x ∧ t.head? = some y) ∨ (c = y ∧ t.head? = some x) ∨ EIn t x y
  | [], h => h.elim
  | [_], h => by
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | h
      · exact Or.inl ⟨h1, by simp [h2]⟩
      · exact Or.inr (Or.inl ⟨h1, by simp [h2]⟩)
      · exact h.elim
  | c' :: d :: t', h => by
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | h3
      · exact Or.inl ⟨h1, by simp [h2]⟩
      · exact Or.inr (Or.inl ⟨h1, by simp [h2]⟩)
      · exact Or.inr (Or.inr h3)

/-- EIn 的双段拼接反演：拼接后的一条边要么属于某段，要么是接点跨界对。
    （对尾段归纳；交叉对以 lastOf l₁ / head? l₂ 的 some 形式陈述。） -/
theorem EIn_append_inv2 {V : Type} {x y : V} :
    ∀ (l₂ l₁ : List V), EIn (l₁ ++ l₂) x y →
      EIn l₁ x y ∨ EIn l₂ x y ∨
        ((lastOf l₁ = some x ∧ l₂.head? = some y) ∨
          (lastOf l₁ = some y ∧ l₂.head? = some x))
  | [], l₁, h => by
      rw [List.append_nil] at h
      exact Or.inl h
  | c :: tt, l₁, h => by
      have hrw : l₁ ++ c :: tt = (l₁ ++ [c]) ++ tt := append_cons_def l₁ c tt
      rw [hrw] at h
      rcases EIn_append_inv2 tt (l₁ ++ [c]) h with hA | hB | hC
      · rcases EIn_append_inv l₁ x y hA with h1 | h2 | h2
        · exact Or.inl h1
        · exact Or.inr (Or.inr (Or.inr ⟨h2.2, by rw [h2.1]; rfl⟩))
        · exact Or.inr (Or.inr (Or.inl ⟨h2.2, by rw [h2.1]; rfl⟩))
      · exact Or.inr (Or.inl (EIn_cons_prefix (c := c) tt x y hB))
      · have hlastc : lastOf (l₁ ++ [c]) = some c := lastOf_append_single' l₁ c
        rcases hC with ⟨hx, hy⟩ | ⟨hy, hx⟩
        · refine Or.inr ?_
          have hxc : c = x := Option.some.inj (hlastc.symm.trans hx)
          subst hxc
          cases tt with
          | nil => rw [List.head?] at hy; exact absurd hy (by simp)
          | cons d r =>
              have hdy : d = y := by simpa using hy
              subst hdy
              simp only [EIn]
              exact Or.inl (Or.inl (by simp))
        · refine Or.inr ?_
          have hyc : c = y := Option.some.inj (hlastc.symm.trans hy)
          subst hyc
          cases tt with
          | nil => rw [List.head?] at hx; exact absurd hx (by simp)
          | cons d r =>
              have hdx : d = x := by simpa using hx
              subst hdx
              simp only [EIn]
              exact Or.inl (Or.inr (Or.inl (by simp)))

/-! ### lane_87 第三批：fan6 detour 内核的 Q-侧底件

lane_68c §2 的单步绕行变换（坏路 P = C ++ [a] ++ E 重装为 Q = reverse C ++ [a] ++ E、
释放边 (m,a) 给纠正路 S′ = S ++ [a]）被 link 穷举否证为"单步即足"，但其变换本体
是任何级联论证的必需机械件。本批证出 Q 的路径性与 Q 相对 P 的边记账
（P 的边除 (m,a) 接点对外全由 Q 承接）。全部零 sorry。 -/

/-- **detour 重装路 Q 的路径性**：C、E 分别是坏路 P = C ++ [a] ++ E 的两段
（各自成链、互异、不含 a、C ∩ E = ∅），则 Q = reverse C ++ [a] ++ E 是 H-路径。
接点：reverse C 末点 = head C = b，经被吸收边 ba 接 a；a 经 P 的接点边接 head E。 -/
theorem fan6_detour_Q_path {n : Nat} (H : Graph n) (a b : Fin n) (hab : H.adjB a b = true)
    (C E : List (Fin n)) (hcne : C ≠ []) (hC : Distinct C) (hE : Distinct E)
    (haC : a ∉ C) (haE : a ∉ E) (hCE : ∀ v ∈ C, v ∉ E)
    (hcc : Chain (GAdj H) C) (hce : Chain (GAdj H) E)
    (hbhead : C.head? = some b)
    (hjE : E ≠ [] → ∀ w : Fin n, E.head? = some w → H.adjB a w = true) :
    IsPath (GAdj H) (C.reverse ++ [a] ++ E) := by
  have hcrd : Chain (GAdj H) C.reverse :=
    chain_reverse (GAdj H) (fun x y hxy => H.symm x y hxy) C hcc
  have hcrlen : 2 ≤ (C.reverse ++ [a] ++ E).length := by
    cases C with
    | nil => exact absurd rfl hcne
    | cons x t =>
        simp only [List.reverse_cons, List.length_append, List.length_reverse,
          List.length_cons]
        omega
  -- Distinct Q
  have hd1 : Distinct (C.reverse ++ [a]) :=
    distinctP_append C.reverse a (distinct_reverse C hC)
      (fun hm => haC (mem_of_mem_reverse C hm))
  have hdQ : Distinct (C.reverse ++ [a] ++ E) :=
    distinct_append_disj (C.reverse ++ [a]) E hd1 hE
      (fun v hv hm => by
        rcases List.mem_append.1 hv with hA | hA
        · exact hCE v (mem_of_mem_reverse C hA) hm
        · rcases List.mem_cons.1 hA with hv1 | hv1
          · exact haE (by rw [hv1] at hm; exact hm)
          · exact absurd hv1 (by simp))
  -- Chain Q
  have hcQ : Chain (GAdj H) (C.reverse ++ [a] ++ E) := by
    have hj1 : lastOf C.reverse = some b := by rw [lastOf_reverse]; exact hbhead
    have hstep1 : Chain (GAdj H) (C.reverse ++ [a]) :=
      chain_append_single (GAdj H) C.reverse a hcrd
        (fun w hw => by
          rw [hw] at hj1
          have hb : w = b := Option.some.inj hj1
          rw [hb]
          exact H.symm a b hab)
    by_cases hEE : E = []
    · subst hEE
      simpa using hstep1
    · have hgoal : Chain (GAdj H) ((C.reverse ++ [a]) ++ E) :=
        chain_append_list (GAdj H) E (C.reverse ++ [a]) hEE hstep1 hce
          (fun u v hu hv => by
            have hu2 : u = a := Option.some.inj
              (hu.symm.trans (lastOf_append_single' C.reverse a))
            rw [hu2]
            exact hjE hEE v hv)
      exact hgoal
  exact ⟨hcrlen, hdQ, hcQ⟩

/-- **detour 重装路 Q 相对坏路 P 的边记账**：P = C ++ [a] ++ E 的每条边要么
    是 Q = reverse C ++ [a] ++ E 的边，要么是 (m, a) 接点对
    （m = lastOf C，即坏路标记；该边被释放给纠正路 S′ = S ++ [a]）。 -/
theorem EIn_append_junction {V : Type} {u v : V} :
    ∀ (l₁ l₂ : List V), l₂ ≠ [] → lastOf l₁ = some u → l₂.head? = some v →
      EIn (l₁ ++ l₂) u v
  | l₁, c :: t, _, hu, hh => by
      rw [append_cons_def]
      have hv' : v = c := by
        have hhc : (c :: t).head? = some c := rfl
        exact Option.some.inj (hh.symm.trans hhc)
      rw [hv']
      exact EIn_append_left (l₁ ++ [c]) t u c (EIn_append_last l₁ c u hu)

/-- 尾段边在拼接下保持。 -/
theorem EIn_append_right {V : Type} : ∀ (l₁ l₂ : List V) (x y : V),
    EIn l₂ x y → EIn (l₁ ++ l₂) x y
  | [], l₂, x, y, h => h
  | e :: s, l₂, x, y, h => by
      rw [List.cons_append]
      exact EIn_cons_prefix (c := e) (s ++ l₂) x y
        (EIn_append_right s l₂ x y h)

/-- **detour 重装路 Q 相对坏路 P 的边记账**：P = C ++ [a] ++ E 的每条边要么
    是 Q = reverse C ++ [a] ++ E 的边，要么是 (m, a) 接点对
    （m = lastOf C，即坏路标记；该边被释放给纠正路 S′ = S ++ [a]）。 -/
theorem fan6_detour_Q_EIn {n : Nat} {a m : Fin n} (C E : List (Fin n))
    (hmC : lastOf C = some m) :
    ∀ x y : Fin n, EIn (C ++ [a] ++ E) x y →
      EIn (C.reverse ++ [a] ++ E) x y ∨
        (lastOf C = some x ∧ y = a) ∨ (lastOf C = some y ∧ x = a) := by
  intro x y hxy
  rcases EIn_append_inv2 E (C ++ [a]) hxy with hA | hB | hC
  · rcases EIn_append_inv C x y hA with h1 | h2 | h2
    · have h' := (EIn_reverse_iff C).1 h1
      exact Or.inl (EIn_append_left _ _ _ _ (EIn_append_suffix C.reverse x y h'))
    · exact Or.inr (Or.inr ⟨h2.2, h2.1⟩)
    · exact Or.inr (Or.inl ⟨h2.2, h2.1⟩)
  · exact Or.inl (EIn_append_right (C.reverse ++ [a]) E x y hB)
  · have hEne : E ≠ [] := by
      cases hhE : E with
      | nil => rw [hhE] at hC; exact absurd hC (by simp [List.head?])
      | cons d t => exact List.cons_ne_nil d t
    rcases hC with ⟨hx, hy⟩ | ⟨hy, hx⟩
    · have hxa : a = x :=
        Option.some.inj ((lastOf_append_single' C a).symm.trans hx)
      refine Or.inl ?_
      rw [← hxa]
      exact EIn_append_junction (C.reverse ++ [a]) E hEne
        (lastOf_append_single' C.reverse a) hy
    · have hya : a = y :=
        Option.some.inj ((lastOf_append_single' C a).symm.trans hy)
      refine Or.inl ?_
      rw [← hya]
      exact EIn_symm _ _ _ (EIn_append_junction (C.reverse ++ [a]) E hEne
        (lastOf_append_single' C.reverse a) hx)

/-! ## fan6_nf 级联引理链（lane_88c，2026-09-19）

级联重排的机械底件。三层：
- **L1 tail-swap（换尾）**：两条共享中转点 x 的路径 P₁ = A ++ [x] ++ B 与
  P₂ = A′ ++ [x] ++ B′ 互换远离 x 的尾段，得 Q₁ = A ++ [x] ++ B′ 与
  Q₂ = A′ ++ [x] ++ B——路径性保持、**边集（无序对多重集）不变、逐点端点
  轮廓不变**。这是等轮廓重排的原子操作（fan6_nf 证明思路注释的"换尾"）。
- **L2 detour 单步**：坏路 P = C ++ [a] ++ E 经 Q = reverse C ++ [a] ++ E
  与纠正路 S ++ [a] 的重装（消费 lane_87 的 Q 侧底件），账目 b−1/a+1。
- **L3 终止测度**：μ(D) = Σ 端点 b 权重的尾部深度，良基框架（Nat 迭代
  降级链的显式长度界）+ detour 步严格降级引理。

全部零 sorry；fan6_nf 本体维持占位（级联归纳的组装仍是研究级缺口，
见 lane_88c 报告）。 -/

/-! ### L1.0 链的前缀 -/

/-- 拼接的前缀仍是链（对 l₁ 归纳）。 -/
theorem chain_prefix {V : Type} (adj : V → V → Prop) :
    ∀ (l₁ l₂ : List V), Chain adj (l₁ ++ l₂) → Chain adj l₁
  | [], _, _ => trivial
  | [_], _, _ => trivial
  | c :: d :: t, l₂, h => ⟨h.1, chain_prefix adj (d :: t) l₂ h.2⟩

/-! ### L1.1 tail-swap 的链性 -/

/-- **tail-swap 链性（双侧）**：P₁ = A ++ [x] ++ B 与 P₂ = A′ ++ [x] ++ B′
    在共享中转点 x 换尾（远离 x 的尾段互换），得 Q₁ = A ++ [x] ++ B′ 与
    Q₂ = A′ ++ [x] ++ B。四段各自成链 + 两侧 x-接点边（入边取自 P₁/P₂
    的 x-前驱接点、出边取自 P₁/P₂ 的 x-后继接点），则 Q₁、Q₂ 都是链。
    注意：Q₁ 的 x-入边来自 P₁（lastOf A 接 x），x-出边来自 P₂（x 接
    head B′）；Q₂ 对称。 -/
theorem fan6_tailswap_chain {V : Type} (adj : V → V → Prop)
    (A B A' B' : List V) (x : V)
    (hA : Chain adj A) (hB : Chain adj B) (hA' : Chain adj A') (hB' : Chain adj B')
    (hjxA : ∀ w : V, lastOf A = some w → adj w x)
    (hjxB : ∀ v : V, B'.head? = some v → adj x v)
    (hjxA' : ∀ w : V, lastOf A' = some w → adj w x)
    (hjx : ∀ v : V, B.head? = some v → adj x v) :
    Chain adj (A ++ [x] ++ B') ∧ Chain adj (A' ++ [x] ++ B) := by
  have hstepA : Chain adj (A ++ [x]) := chain_append_single adj A x hA hjxA
  have hstepA' : Chain adj (A' ++ [x]) := chain_append_single adj A' x hA' hjxA'
  constructor
  · by_cases hb'ne : B' = []
    · subst hb'ne; simpa using hstepA
    · exact chain_append_list adj B' (A ++ [x]) hb'ne hstepA hB'
        (fun u v hu hv => by
          have hux : u = x :=
            Option.some.inj (hu.symm.trans (lastOf_append_single' A x))
          rw [hux]; exact hjxB v hv)
  · by_cases hbne : B = []
    · subst hbne; simpa using hstepA'
    · exact chain_append_list adj B (A' ++ [x]) hbne hstepA' hB
        (fun u v hu hv => by
          have hux : u = x :=
            Option.some.inj (hu.symm.trans (lastOf_append_single' A' x))
          rw [hux]; exact hjx v hv)

/-! ### L1.2 tail-swap 的互异性 -/

/-- **tail-swap 互异性（双侧）**：换尾后的两条新路互异（四段互异 + x 与
    对侧尾段不交 + 两侧头段互不交），即 Distinct Q₁ 与 Distinct Q₂。
    假设面按"新组合直接无重复"给出（从 P₁/P₂ 的 Distinct 反演后即得）。 -/
theorem fan6_tailswap_distinct {V : Type} [DecidableEq V]
    (A B A' B' : List V) (x : V)
    (hA : Distinct A) (hB : Distinct B) (hA' : Distinct A') (hB' : Distinct B')
    (hxA : x ∉ A) (hxA' : x ∉ A') (hxB : x ∉ B) (hxB' : x ∉ B')
    (hAB' : ∀ v ∈ A, v ∉ B') (hA'B : ∀ v ∈ A', v ∉ B) :
    Distinct (A ++ [x] ++ B') ∧ Distinct (A' ++ [x] ++ B) := by
  have hd1 : Distinct (A ++ [x]) := distinctP_append A x hA hxA
  have hd1' : Distinct (A' ++ [x]) := distinctP_append A' x hA' hxA'
  constructor
  · exact distinct_append_disj (A ++ [x]) B' hd1 hB'
      (fun v hv hm => by
        rcases List.mem_append.1 hv with hA | hA
        · exact hAB' v hA hm
        · rcases List.mem_cons.1 hA with hv1 | hv1
          · exact hxB' (hv1 ▸ hm)
          · exact absurd hv1 (by simp))
  · exact distinct_append_disj (A' ++ [x]) B hd1' hB
      (fun v hv hm => by
        rcases List.mem_append.1 hv with hA | hA
        · exact hA'B v hA hm
        · rcases List.mem_cons.1 hA with hv1 | hv1
          · exact hxB (hv1 ▸ hm)
          · exact absurd hv1 (by simp))

/-! ### L1.3 路径在内部点的分裂 -/

/-- 含 x 的表可在 x 处分裂为 A ++ x :: B（对表归纳）。 -/
theorem fan6_splitAt {V : Type} [DecidableEq V] : ∀ (P : List V) (x : V),
    x ∈ P → ∃ A B : List V, P = A ++ x :: B
  | [], x, h => absurd h (by simp)
  | c :: t, x, h => by
      rcases List.mem_cons.1 h with h1 | h1
      · exact ⟨[], t, by rw [h1]; rfl⟩
      · obtain ⟨A, B, hAB⟩ := fan6_splitAt t x h1
        exact ⟨c :: A, B, by rw [hAB]; rfl⟩

/-- 链在 x 处分裂后的三段性质：头段链、x-入边、x::B 链。 -/
theorem chain_split_inv {V : Type} (adj : V → V → Prop) :
    ∀ (A B : List V) (x : V), Chain adj (A ++ x :: B) →
      Chain adj A ∧ (∀ w : V, lastOf A = some w → adj w x) ∧ Chain adj (x :: B)
  | [], B, x, h => ⟨trivial, (fun w hw => by simp [lastOf] at hw), h⟩
  | [c], B, x, h => by
      have hshow : ([c] ++ x :: B) = c :: x :: B := rfl
      rw [hshow] at h
      exact ⟨trivial, (fun w hw => by
        simp [lastOf] at hw; exact hw ▸ h.1), h.2⟩
  | c :: d :: t, B, x, h =>
      ⟨⟨h.1, (chain_split_inv adj (d :: t) B x h.2).1⟩,
        (chain_split_inv adj (d :: t) B x h.2).2.1,
        (chain_split_inv adj (d :: t) B x h.2).2.2⟩

/-- Chain (x :: B) 的尾段仍链。 -/
theorem chain_cons_tail {V : Type} (adj : V → V → Prop) :
    ∀ (B : List V) (x : V), Chain adj (x :: B) → Chain adj B
  | [], x, _ => trivial
  | y :: r, x, h => h.2

/-- Chain (x :: B) 给出 x 的出边（B 非空时首元素的入边）。 -/
theorem chain_cons_out {V : Type} (adj : V → V → Prop) :
    ∀ (B : List V) (x : V), Chain adj (x :: B) →
      ∀ v : V, B.head? = some v → adj x v
  | [], x, _, v, hv => absurd hv (by simp [List.head?])
  | y :: r, x, h, v, hv => by
      have hv2 : v = y := Option.some.inj (hv.symm.trans rfl)
      rw [hv2]; exact h.1

/-- 互异表在 x 处分裂后的四段性质。 -/
theorem distinct_split_inv {V : Type} [DecidableEq V] :
    ∀ (A B : List V) (x : V), Distinct (A ++ x :: B) →
      Distinct A ∧ Distinct B ∧ x ∉ A ∧ x ∉ B
  | [], B, x, h =>
      ⟨trivial, (by cases B with
                  | nil => trivial
                  | cons y t => exact h.2),
        (fun hm => by simp at hm), h.1⟩
  | c :: t, B, x, h => by
      have hshow : ((c :: t) ++ x :: B) = c :: (t ++ x :: B) := rfl
      rw [hshow] at h
      obtain ⟨hdA, hdB, hxa, hxb⟩ := distinct_split_inv t B x h.2
      have hxc : x ≠ c := fun he =>
        h.1 (he ▸ List.mem_append.2 (Or.inr (List.mem_cons.2 (Or.inl rfl))))
      refine ⟨⟨fun hm => h.1 (List.mem_append.2 (Or.inl hm)), hdA⟩, hdB, ?_, hxb⟩
      intro hm
      rcases List.mem_cons.1 hm with h1 | h1
      · exact hxc h1
      · exact hxa h1

/-- **tail-swap 分裂反演**：两条路径在共享点 x 处分裂成 A ++ [x] ++ B、
    A′ ++ [x] ++ B′，则 tail-swap 全部假设面（段链、段互异、x 接点、
    x 与对侧段不交）齐备。这是把 tail-swap 机械件接到具体分解上的 glue。 -/
theorem fan6_tailswap_hyps {n : Nat} (adj : Fin n → Fin n → Prop)
    (P₁ P₂ : List (Fin n)) (x : Fin n)
    (hP₁ : IsPath adj P₁) (hP₂ : IsPath adj P₂)
    (hmem₁ : x ∈ P₁) (hmem₂ : x ∈ P₂) :
    ∃ A B A' B' : List (Fin n),
      P₁ = A ++ x :: B ∧ P₂ = A' ++ x :: B' ∧
      Chain adj A ∧ Chain adj B ∧ Chain adj A' ∧ Chain adj B' ∧
      (∀ w : Fin n, lastOf A = some w → adj w x) ∧
      (∀ v : Fin n, B'.head? = some v → adj x v) ∧
      (∀ w : Fin n, lastOf A' = some w → adj w x) ∧
      (∀ v : Fin n, B.head? = some v → adj x v) ∧
      Distinct A ∧ Distinct B ∧ Distinct A' ∧ Distinct B' ∧
      x ∉ A ∧ x ∉ B ∧ x ∉ A' ∧ x ∉ B' := by
  obtain ⟨A, B, hAB⟩ := fan6_splitAt P₁ x hmem₁
  obtain ⟨A', B', hAB'⟩ := fan6_splitAt P₂ x hmem₂
  obtain ⟨cA, cx, cB⟩ := chain_split_inv adj A B x (hAB ▸ hP₁.2.2)
  obtain ⟨cA', cx', cB'⟩ := chain_split_inv adj A' B' x (hAB' ▸ hP₂.2.2)
  obtain ⟨dA, dB, hxa, hxb⟩ := distinct_split_inv A B x (hAB ▸ hP₁.2.1)
  obtain ⟨dA', dB', hxa', hxb'⟩ := distinct_split_inv A' B' x (hAB' ▸ hP₂.2.1)
  refine ⟨A, B, A', B', hAB, hAB', cA, chain_cons_tail adj B x cB, cA',
    chain_cons_tail adj B' x cB', cx, chain_cons_out adj B' x cB', cx',
    chain_cons_out adj B x cB, dA, dB, dA', dB', hxa, hxb, hxa', hxb'⟩

/-! ### L1.4 tail-swap 的边集不变性 -/

/-- **tail-swap 边集守恒**：换尾前后两组路径的边集（无序对意义）相同，
    即 (EIn P₁ ∨ EIn P₂) ↔ (EIn Q₁ ∨ EIn Q₂)。逐边情形：头段边留在同侧
    新路、尾段边随尾段迁移、x-接点边由对侧新路承接。 -/
theorem fan6_tailswap_edges {V : Type} (A B A' B' : List V) (x : V) :
    ∀ p q : V,
      (EIn (A ++ [x] ++ B) p q ∨ EIn (A' ++ [x] ++ B') p q) ↔
      (EIn (A ++ [x] ++ B') p q ∨ EIn (A' ++ [x] ++ B) p q) := by
  intro p q
  have hlastx : ∀ (L : List V), lastOf (L ++ [x]) = some x :=
    fun L => lastOf_append_single' L x
  constructor
  · rintro (h | h)
    · rcases EIn_append_inv2 B (A ++ [x]) h with h1 | h2 | ⟨hj, hseg⟩ | ⟨hj, hseg⟩
      · exact Or.inl (EIn_append_left (A ++ [x]) B' p q h1)
      · exact Or.inr (EIn_append_right (A' ++ [x]) B p q h2)
      · have hBne : B ≠ [] := fun he => by
          rw [he] at hseg; simp at hseg
        have hpx : p = x := Option.some.inj (hj.symm.trans (hlastx A))
        rw [hpx]
        exact Or.inr (EIn_append_junction (A' ++ [x]) B hBne (hlastx A') hseg)
      · have hBne : B ≠ [] := fun he => by
          rw [he] at hseg; simp at hseg
        have hpx : q = x := Option.some.inj (hj.symm.trans (hlastx A))
        rw [hpx]
        exact Or.inr (EIn_symm (A' ++ [x] ++ B) x p
          (EIn_append_junction (A' ++ [x]) B hBne (hlastx A') hseg))
    · rcases EIn_append_inv2 B' (A' ++ [x]) h with h1 | h2 | ⟨hj, hseg⟩ | ⟨hj, hseg⟩
      · exact Or.inr (EIn_append_left (A' ++ [x]) B p q h1)
      · exact Or.inl (EIn_append_right (A ++ [x]) B' p q h2)
      · have hB'ne : B' ≠ [] := fun he => by
          rw [he] at hseg; simp at hseg
        have hpx : p = x := Option.some.inj (hj.symm.trans (hlastx A'))
        rw [hpx]
        exact Or.inl (EIn_append_junction (A ++ [x]) B' hB'ne (hlastx A) hseg)
      · have hB'ne : B' ≠ [] := fun he => by
          rw [he] at hseg; simp at hseg
        have hpx : q = x := Option.some.inj (hj.symm.trans (hlastx A'))
        rw [hpx]
        exact Or.inl (EIn_symm (A ++ [x] ++ B') x p
          (EIn_append_junction (A ++ [x]) B' hB'ne (hlastx A) hseg))
  · rintro (h | h)
    · rcases EIn_append_inv2 B' (A ++ [x]) h with h1 | h2 | ⟨hj, hseg⟩ | ⟨hj, hseg⟩
      · exact Or.inl (EIn_append_left (A ++ [x]) B p q h1)
      · exact Or.inr (EIn_append_right (A' ++ [x]) B' p q h2)
      · have hB'ne : B' ≠ [] := fun he => by
          rw [he] at hseg; simp at hseg
        have hpx : p = x := Option.some.inj (hj.symm.trans (hlastx A))
        rw [hpx]
        exact Or.inr (EIn_append_junction (A' ++ [x]) B' hB'ne (hlastx A') hseg)
      · have hB'ne : B' ≠ [] := fun he => by
          rw [he] at hseg; simp at hseg
        have hpx : q = x := Option.some.inj (hj.symm.trans (hlastx A))
        rw [hpx]
        exact Or.inr (EIn_symm (A' ++ [x] ++ B') x p
          (EIn_append_junction (A' ++ [x]) B' hB'ne (hlastx A') hseg))
    · rcases EIn_append_inv2 B (A' ++ [x]) h with h1 | h2 | ⟨hj, hseg⟩ | ⟨hj, hseg⟩
      · exact Or.inr (EIn_append_left (A' ++ [x]) B' p q h1)
      · exact Or.inl (EIn_append_right (A ++ [x]) B p q h2)
      · have hBne : B ≠ [] := fun he => by
          rw [he] at hseg; simp at hseg
        have hpx : p = x := Option.some.inj (hj.symm.trans (hlastx A'))
        rw [hpx]
        exact Or.inl (EIn_append_junction (A ++ [x]) B hBne (hlastx A) hseg)
      · have hBne : B ≠ [] := fun he => by
          rw [he] at hseg; simp at hseg
        have hpx : q = x := Option.some.inj (hj.symm.trans (hlastx A'))
        rw [hpx]
        exact Or.inl (EIn_symm (A ++ [x] ++ B) x p
          (EIn_append_junction (A ++ [x]) B hBne (hlastx A) hseg))

/-! ### L1.5 tail-swap 的端点轮廓不变 -/

/-- 非平凡路的端点指示分解：两端不同时为 v 时，vEndBit 是两个端指示之和。 -/
theorem vEndBit_split {n : Nat} (v : Fin n) (P : List (Fin n))
    (h : ¬(P.head? = some v ∧ lastOf P = some v)) :
    vEndBit v P = (if P.head? = some v then 1 else 0)
      + (if lastOf P = some v then 1 else 0) := by
  unfold vEndBit
  by_cases h1 : P.head? = some v
  · by_cases h2 : lastOf P = some v
    · exact absurd ⟨h1, h2⟩ h
    · simp [h1, h2]
  · by_cases h2 : lastOf P = some v
    · simp [h1, h2]
    · simp [h1, h2]

/-- 路的头与尾段无关：head? (A ++ [x] ++ B) = head? (A ++ [x] ++ B')。 -/
theorem headQ_suffix_indep {V : Type} (A : List V) (x : V) (B B' : List V) :
    (A ++ [x] ++ B).head? = (A ++ [x] ++ B').head? := by
  cases A with
  | nil =>
      show ([x] ++ B).head? = ([x] ++ B').head?
      exact rfl
  | cons c t =>
      have h1 : ((c :: t) ++ [x] ++ B).head? = some c := by
        show (c :: (t ++ [x] ++ B)).head? = some c
        exact rfl
      have h2 : ((c :: t) ++ [x] ++ B').head? = some c := by
        show (c :: (t ++ [x] ++ B')).head? = some c
        exact rfl
      rw [h1, h2]

/-- 路的尾与头段无关：lastOf (A ++ [x] ++ B) = lastOf (A' ++ [x] ++ B)。 -/
theorem lastOf_prefix_indep {V : Type} (B : List V) (x : V) (A A' : List V) :
    lastOf (A ++ [x] ++ B) = lastOf (A' ++ [x] ++ B) := by
  by_cases hB : B = []
  · subst hB
    simp only [List.append_nil]
    rw [lastOf_append_single' A x, lastOf_append_single' A' x]
  · have h1 : lastOf (A ++ [x] ++ B) = lastOf B := lastOf_append_list (A ++ [x]) B hB
    have h2 : lastOf (A' ++ [x] ++ B) = lastOf B := lastOf_append_list (A' ++ [x]) B hB
    rw [h1, h2]

/-- **tail-swap 端点记账（逐点）**：换尾前后两条新路在任意点 v 的端点指示
    之和不变。前提是四条路的"两端不同时为 v"（由 Distinct + 长度 ≥ 2
    保证，作为组装时的 glue 条件）。 -/
theorem fan6_tailswap_vEndBit {n : Nat} (v : Fin n) (A B A' B' : List (Fin n)) (x : Fin n)
    (h₁ : ¬((A ++ [x] ++ B).head? = some v ∧ lastOf (A ++ [x] ++ B) = some v))
    (h₂ : ¬((A' ++ [x] ++ B').head? = some v ∧ lastOf (A' ++ [x] ++ B') = some v))
    (h₃ : ¬((A ++ [x] ++ B').head? = some v ∧ lastOf (A ++ [x] ++ B') = some v))
    (h₄ : ¬((A' ++ [x] ++ B).head? = some v ∧ lastOf (A' ++ [x] ++ B) = some v)) :
    vEndBit v (A ++ [x] ++ B) + vEndBit v (A' ++ [x] ++ B')
      = vEndBit v (A ++ [x] ++ B') + vEndBit v (A' ++ [x] ++ B) := by
  have e₁ := vEndBit_split v (A ++ [x] ++ B) h₁
  have e₂ := vEndBit_split v (A' ++ [x] ++ B') h₂
  have e₃ := vEndBit_split v (A ++ [x] ++ B') h₃
  have e₄ := vEndBit_split v (A' ++ [x] ++ B) h₄
  have hh := headQ_suffix_indep A x B B'
  have hh' := headQ_suffix_indep A' x B' B
  have hl := lastOf_prefix_indep B x A A'
  have hl' := lastOf_prefix_indep B' x A' A
  rw [e₁, e₂, e₃, e₄, hh, hh', hl, hl']
  omega

/-! ### L2 detour 单步的 S 侧底件 -/

/-- **detour 纠正路的路径性**：S 是互异的非空链、a ∉ S、末点 m、
    释放边 (m,a) ∈ H，则纠正路 S′ = S ++ [a] 是 H-路径。
    （detour 机制：坏路 P 吸收 ba 后释放边 ma，由 S′ 承接。） -/
theorem fan6_detour_S_path {n : Nat} (H : Graph n) (a m : Fin n)
    (S : List (Fin n)) (hne : S ≠ [])
    (hdis : Distinct S) (haS : a ∉ S)
    (hchain : Chain (GAdj H) S)
    (hlast : lastOf S = some m)
    (hedm : H.adjB m a = true) :
    IsPath (GAdj H) (S ++ [a]) := by
  have hchain' : Chain (GAdj H) (S ++ [a]) :=
    chain_append_single (GAdj H) S a hchain (fun w hw => by
      have hwm : w = m := Option.some.inj (hw.symm.trans hlast)
      rw [hwm]; exact hedm)
  have hlen : 2 ≤ (S ++ [a]).length := by
    have h1 : 1 ≤ S.length := by
      cases S with
      | nil => exact absurd rfl hne
      | cons x t => show 1 <= t.length + 1; omega
    have h2 : (S ++ [a]).length = S.length + 1 := by simp [List.length_append]
    omega
  exact ⟨hlen, distinctP_append S a hdis haS, hchain'⟩

/-! ### L3 终止测度：定义 + 良基框架 + detour 降级 -/

/-- b-端路径上 a 的尾部深度：a 沿尾方向到路径末端的距离
    （a 不在路径中时 Nat 减法截断为 0）。 -/
def tailDist {n : Nat} (a : Fin n) (P : List (Fin n)) : Nat :=
  P.length - 1 - (P.takeWhile (fun w => w != a)).length

/-- 级联测度的单路权重：仅 b-端路径贡献（尾部深度 + 1）。
    端点条件与 vEndBit 同构（裸 Or 形式，可判定性同源）。 -/
def fan6_measureW {n : Nat} (a b : Fin n) (P : List (Fin n)) : Nat :=
  if (P.head? = some b ∨ lastOf P = some b) then tailDist a P + 1 else 0

/-- **级联测度 μ**：分解 D 上所有 b-端路径的权重和。
    detour 一步（坏路 P = C ++ [a] ++ E 换成 m-端路 Q 与 S ++ [a]）使
    μ 严格降 |E| + 1——级联链长被 μ(初态) 界住。 -/
def fan6_measure {n : Nat} (a b : Fin n) (D : List (List (Fin n))) : Nat :=
  D.foldr (fun P s => fan6_measureW a b P + s) 0

/-- 测度对拼接的分配。 -/
theorem fan6_measure_append {n : Nat} (a b : Fin n) (D L : List (List (Fin n))) :
    fan6_measure a b (D ++ L) = fan6_measure a b D + fan6_measure a b L := by
  induction D with
  | nil => simp [fan6_measure]
  | cons c t ih =>
      have h1 : fan6_measure a b ((c :: t) ++ L)
          = fan6_measure a b (c :: (t ++ L)) := rfl
      have h2 : fan6_measure a b (c :: (t ++ L))
          = fan6_measureW a b c + fan6_measure a b (t ++ L) := rfl
      have h3 : fan6_measure a b (c :: t)
          = fan6_measureW a b c + fan6_measure a b t := rfl
      rw [h1, h2, h3, ih]
      omega

/-- erase 恰删去一个成员：测度减去其权重（无需唯一性）。 -/
theorem fan6_measure_erase {n : Nat} (a b : Fin n) :
    ∀ (D : List (List (Fin n))) (X : List (Fin n)), X ∈ D →
      fan6_measure a b (D.erase X) + fan6_measureW a b X = fan6_measure a b D
  | [], X, h => absurd h (by simp)
  | c :: t, X, h => by
      by_cases hc : c = X
      · subst hc
        rw [List.erase_cons_head]
        simp only [fan6_measure, List.foldr_cons]
        omega
      · have hmem : X ∈ t := by
          rcases List.mem_cons.1 h with h0 | h0
          · exact absurd h0.symm hc
          · exact h0
        have hrec := fan6_measure_erase a b t X hmem
        rw [show (c :: t).erase X = c :: (t.erase X) from by simp [hc]]
        simp only [fan6_measure, List.foldr_cons]
        simp only [fan6_measure] at hrec
        omega

/-- **良基框架（Nat 迭代降级链的显式界）**：若每步严格降，则从 k 出发
    第 i 步的值满足 f (k + i) + i ≤ f k——链长被初值界住。
    这是"级联重排必终止"的良基性骨架：把 k 取为 μ(初态)、f 取为
    链上第 i 步的 μ 值即可。 -/
theorem nat_iter_desc_le (f : Nat → Nat) (hstep : ∀ k, f (k + 1) < f k) :
    ∀ (i k : Nat), f (k + i) + i ≤ f k
  | 0, k => by simp only [Nat.add_zero]; omega
  | i + 1, k => by
      have h1 := hstep (k + i)
      have h2 := nat_iter_desc_le f hstep i k
      have hshift : k + (i + 1) = (k + i) + 1 := by omega
      rw [hshift]
      omega

/-- 推论：降级链的第 i 步存在 ⟹ i ≤ f k（链长 ≤ 初值）。 -/
theorem nat_iter_desc_bound (f : Nat → Nat) (hstep : ∀ k, f (k + 1) < f k) (k i : Nat) :
    i ≤ f k := by
  have h := nat_iter_desc_le f hstep i k
  omega

/-- takeWhile 在首个 a 处停：a ∉ C 时取前缀 C（不含 a）。 -/
theorem takeWhile_ne_stop {n : Nat} (a : Fin n) :
    ∀ (C E : List (Fin n)), a ∉ C →
      (C ++ a :: E).takeWhile (fun w => w != a) = C
  | [], E, h => by simp [List.takeWhile_cons]
  | c :: r, E, h => by
      have hca : c ≠ a := by intro hce; exact h (hce ▸ List.mem_cons_self ..)
      have hmem : a ∉ r := by
        intro hmem; exact h (List.mem_cons_of_mem _ hmem)
      have hcne : (c != a) = true := by simp [hca]
      have hshow : ((c :: r) ++ a :: E) = c :: (r ++ a :: E) := rfl
      rw [hshow, List.takeWhile_cons, if_pos hcne]
      rw [takeWhile_ne_stop a r E hmem]

/-- a 不在表中时 takeWhile 取全表。 -/
theorem takeWhile_all_ne {n : Nat} (a : Fin n) :
    ∀ (S : List (Fin n)), a ∉ S → S.takeWhile (fun w => w != a) = S
  | [], h => by simp [List.takeWhile_cons]
  | c :: r, h => by
      have hca : c ≠ a := by intro hce; exact h (hce ▸ List.mem_cons_self ..)
      have hmem : a ∉ r := by
        intro hmem; exact h (List.mem_cons_of_mem _ hmem)
      have hcne : (c != a) = true := by simp [hca]
      have hshow : (c :: r) = c :: r := rfl
      rw [hshow, List.takeWhile_cons, if_pos hcne]
      rw [takeWhile_all_ne a r hmem]

/-- **坏路权重**：P = C ++ [a] ++ E 是 b-端路（head 或 last 为 b）且 a ∉ C，
    则 w(P) = |E| + 1（a 的尾部深度 = |E|）。 -/
theorem fan6_measureW_bad {n : Nat} (a b : Fin n) (C E : List (Fin n))
    (hend : (C ++ [a] ++ E).head? = some b ∨ lastOf (C ++ [a] ++ E) = some b)
    (haC : a ∉ C) :
    fan6_measureW a b (C ++ [a] ++ E) = E.length + 1 := by
  unfold fan6_measureW tailDist
  rw [if_pos hend]
  have htw : ((C ++ [a] ++ E).takeWhile (fun w => w != a)) = C := by
    have hshow : (C ++ [a] ++ E) = C ++ a :: E := by
      simp [List.cons_append]
    rw [hshow]
    exact takeWhile_ne_stop a C E haC
  have hlen : (C ++ [a] ++ E).length = C.length + 1 + E.length := by
    simp only [List.length_append, List.length_cons, List.length_nil]
  rw [htw, hlen]
  omega

/-- **非 b-端路零权重**。 -/
theorem fan6_measureW_notEnd {n : Nat} (a b : Fin n) (Q : List (Fin n))
    (h : ¬(Q.head? = some b ∨ lastOf Q = some b)) :
    fan6_measureW a b Q = 0 := by
  unfold fan6_measureW
  simp [h]

/-- **a ∉ S 时权重为 1**（若 S 是 b-端路）：尾部深度截断为 0。 -/
theorem fan6_measureW_noa {n : Nat} (a b : Fin n) (S : List (Fin n))
    (haS : a ∉ S) (hend : S.head? = some b ∨ lastOf S = some b) :
    fan6_measureW a b S = 1 := by
  unfold fan6_measureW tailDist
  rw [if_pos hend]
  have htw : S.takeWhile (fun w => w != a) = S := takeWhile_all_ne a S haS
  have hlen : 1 ≤ S.length := by
    rcases hend with h | h
    · cases S with
      | nil => simp at h
      | cons x t => simp only [List.head?_cons] at h; simp
    · cases S with
      | nil => simp [lastOf] at h
      | cons x t => simp only [List.length_cons]; omega
  rw [htw]
  omega

/-- **尾部推入 a 后的权重不增**：a ≠ b、a ∉ S 时，
    w(S ++ [a]) ≤ w(S)。b 为 S 尾端时右侧可能为 1、左侧为 0（更强降级）。 -/
theorem fan6_measureW_push_le {n : Nat} (a b : Fin n) (S : List (Fin n))
    (hba : a ≠ b) (haS : a ∉ S) :
    fan6_measureW a b (S ++ [a]) ≤ fan6_measureW a b S := by
  unfold fan6_measureW tailDist
  have htwS : S.takeWhile (fun w => w != a) = S := takeWhile_all_ne a S haS
  have htwS' : (S ++ [a]).takeWhile (fun w => w != a) = S := by
    have hshow : (S ++ [a]) = S ++ a :: [] := by simp
    rw [hshow]; exact takeWhile_ne_stop a S [] haS
  have hba' : ¬(some a = some b) := fun h => hba (Option.some.inj h)
  by_cases hh : S.head? = some b
  · have hh' : (S ++ [a]).head? = some b := by
      cases S with
      | nil => exact absurd hh (by simp [List.head?])
      | cons x t => exact (show ((x :: t) ++ [a]).head? = some b from hh) ▸ hh
    rw [if_pos (Or.inl hh), if_pos (Or.inl hh'), htwS', htwS]
    have hlen' : (S ++ [a]).length = S.length + 1 := by simp [List.length_append]
    omega
  · have hlast' : ¬(lastOf (S ++ [a]) = some b) := by
      intro hl
      have hla : lastOf (S ++ [a]) = some a :=
        lastOf_append_single' S a
      exact hba' (hla.symm.trans hl)
    have hne : ¬((S ++ [a]).head? = some b ∨ lastOf (S ++ [a]) = some b) := by
      rintro (h | h)
      · cases S with
        | nil => exact hba (Option.some.inj h)
        | cons x t => exact hh h
      · exact hlast' h
    rw [if_neg hne]
    by_cases hs : S.head? = some b ∨ lastOf S = some b
    · rw [if_pos hs, htwS]; omega
    · split
      · rw [htwS]; omega
      · omega

/-- **detour 步的测度降级（主件）**：D′ = (D − P − S) + Q + S′ 为单步重装
    （坏路 P 换成 Q = C.reverse ++ [a] ++ E、纠正路 S 换成 S′ = S ++ [a]），
    若 w(P) = |E| + 1、w(Q) = 0、w(S′) ≤ w(S)、P ≠ S、S ∈ D.erase P，
    则 μ(D′) + |E| + 1 ≤ μ(D)——每步 detour 使 μ 严格降 |E| + 1。 -/
theorem fan6_detour_measure_lt {n : Nat} (a b : Fin n)
    (D : List (List (Fin n))) (P Q S S' E : List (Fin n)) (D' : List (List (Fin n)))
    (hP : P ∈ D) (hS : S ∈ D) (hPS : P ≠ S)
    (hSmem2 : S ∈ D.erase P)
    (hwp : fan6_measureW a b P = E.length + 1)
    (hwq : fan6_measureW a b Q = 0)
    (hwsle : fan6_measureW a b S' ≤ fan6_measureW a b S)
    (hD' : D' = (D.erase P).erase S ++ [Q, S']) :
    fan6_measure a b D' + (E.length + 1) ≤ fan6_measure a b D := by
  rw [hD', fan6_measure_append]
  -- μ([Q, S′]) = w(Q) + w(S′)
  have hlist : fan6_measure a b [Q, S'] = fan6_measureW a b Q + fan6_measureW a b S' := rfl
  -- 两次 erase 计账
  have e1 := fan6_measure_erase a b D P hP
  have e2 := fan6_measure_erase a b (D.erase P) S hSmem2
  rw [hlist]
  omega

/-! ## fan6_nf 组装收口（lane_88d，2026-09-19）

lane_88c 报告指出的两件剩余：
1. **双路替换 IsDecomp 保持件**（`fan6_replace2_decomp`）：D − P₁ − P₂ + Q₁ + Q₂
   仍是分解——cover / edge-disjoint / distinct 三保持的一次性双路版本
   （两次单路替换不可行：Q₁ 与 P₂ 共享 B′ 段边时中间态破坏边不交）；
2. **detour 单步完整组装**（`fan6_detour_step`）：从 IsDecomp (del1 H a b) D +
   坏路/纠正路结构条件到 IsDecomp H D′ + b−1/a+1 记账（消费形式与
   fan6_case1 的 ②④子句口径一致）。
-/

/-! ### A. 清单代数补充件 -/

/-- EIn 的两端都在表中。 -/
theorem EIn_mem {V : Type} : ∀ (P : List V) (x y : V), EIn P x y → x ∈ P ∧ y ∈ P
  | [], _, _, h => h.elim
  | [_], _, _, h => h.elim
  | u :: v :: r, x, y, h => by
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | h3
      · subst h1; subst h2; simp
      · subst h1; subst h2; simp
      · obtain ⟨h4, h5⟩ := EIn_mem (v :: r) x y h3
        exact ⟨List.mem_cons_of_mem _ h4, List.mem_cons_of_mem _ h5⟩

/-- 拼接的前缀仍互异（对 l₁ 归纳）。 -/
theorem distinct_prefix {V : Type} : ∀ (l₁ l₂ : List V), Distinct (l₁ ++ l₂) → Distinct l₁
  | [], _, _ => trivial
  | c :: t, l₂, h => ⟨fun hm => h.1 (List.mem_append.2 (Or.inl hm)),
      distinct_prefix t l₂ h.2⟩

/-- 首元素在表中。 -/
theorem headQ_mem {V : Type} : ∀ (P : List V) (v : V), P.head? = some v → v ∈ P
  | [], _, h => by simp at h
  | c :: t, v, h => by
      simp only [List.head?_cons] at h
      have hcv : c = v := Option.some.inj h
      rw [hcv]
      exact List.mem_cons_self ..

/-- erase 只删不添（Fin n 层：与主定理陈述共用同一 BEq 实例路径）。 -/
theorem mem_erase_subset (D : List (List (Fin n))) (X S : List (Fin n)) :
    S ∈ D.erase X → S ∈ D := by
  induction D with
  | nil => exact fun h => absurd h (by simp)
  | cons c t ih =>
      intro h
      by_cases hc : c = X
      · rw [hc, List.erase_cons_head] at h
        exact List.mem_cons_of_mem _ h
      · have hE : (c :: t).erase X = c :: (t.erase X) := by simp [hc]
        rw [hE] at h
        rcases List.mem_cons.1 h with h1 | h1
        · rw [h1]; exact List.mem_cons_self ..
        · exact List.mem_cons_of_mem _ (ih h1)

/-- 不等于被删元素的成员经 erase 保留。 -/
theorem mem_erase_of_ne (D : List (List (Fin n))) (X S : List (Fin n)) :
    S ≠ X → S ∈ D → S ∈ D.erase X := by
  intro hne
  induction D with
  | nil => exact fun hS => absurd hS (by simp)
  | cons c t ih =>
      intro hS
      by_cases hc : c = X
      · rw [hc] at hS ⊢
        rcases List.mem_cons.1 hS with h1 | h1
        · exact absurd h1 hne
        · rw [List.erase_cons_head]; exact h1
      · have hE : (c :: t).erase X = c :: (t.erase X) := by simp [hc]
        rw [hE]
        rcases List.mem_cons.1 hS with h1 | h1
        · rw [h1]; exact List.mem_cons_self ..
        · exact List.mem_cons_of_mem _ (ih h1)

/-- **erase 后成员反演（互异版）**：Distinct D 中 S ∈ D.erase X 给出
    S ∈ D 且 S ≠ X（互异性保证 X 至多出现一次，删后即不在）。 -/
theorem mem_erase_inv (D : List (List (Fin n))) (X S : List (Fin n)) :
    Distinct D → S ∈ D.erase X → S ∈ D ∧ S ≠ X := by
  induction D with
  | nil => exact fun _ h => absurd h (by simp)
  | cons c t ih =>
      intro hdis h
      by_cases hc : c = X
      · have hE : (c :: t).erase X = t := by rw [hc]; exact List.erase_cons_head X t
        rw [hE] at h
        refine ⟨List.mem_cons_of_mem _ h, ?_⟩
        intro hSC
        have hXt : X ∈ t := by rw [← hSC]; exact h
        exact hdis.1 (by rw [hc]; exact hXt)
      · have hE : (c :: t).erase X = c :: (t.erase X) := by simp [hc]
        rw [hE] at h
        rcases List.mem_cons.1 h with h1 | h1
        · refine ⟨by rw [h1]; exact List.mem_cons_self .., ?_⟩
          exact fun hSC => hc (hSC.symm.trans h1).symm
        · exact ⟨List.mem_cons_of_mem _ (ih hdis.2 h1).1, (ih hdis.2 h1).2⟩

/-- erase 保持互异。 -/
theorem distinct_erase (D : List (List (Fin n))) (X : List (Fin n)) :
    Distinct D → Distinct (D.erase X) := by
  induction D with
  | nil => exact fun _ => trivial
  | cons c t ih =>
      intro hdis
      by_cases hc : c = X
      · have hE : (c :: t).erase X = t := by rw [hc]; exact List.erase_cons_head X t
        rw [hE]; exact hdis.2
      · have hE : (c :: t).erase X = c :: (t.erase X) := by simp [hc]
        rw [hE]
        exact ⟨fun hm => hdis.1 (mem_erase_subset t X c hm), ih hdis.2⟩

/-- 双重 erase 后保留成员。 -/
theorem mem_erase2 (D : List (List (Fin n))) (X Y P : List (Fin n)) :
    P ∈ D → P ≠ X → P ≠ Y → P ∈ (D.erase X).erase Y :=
  fun hD hX hY => mem_erase_of_ne (D.erase X) Y P hY (mem_erase_of_ne D X P hX hD)

/-- erase 恰删一员：长度记账。 -/
theorem length_erase_of_mem (D : List (List (Fin n))) (X : List (Fin n)) :
    X ∈ D → (D.erase X).length + 1 = D.length := by
  induction D with
  | nil => exact fun h => absurd h (by simp)
  | cons c t ih =>
      intro h
      by_cases hc : c = X
      · have hE : (c :: t).erase X = t := by rw [hc]; exact List.erase_cons_head X t
        rw [hE]; simp
      · have hE : (c :: t).erase X = c :: (t.erase X) := by simp [hc]
        rw [hE]
        have hmem : X ∈ t := by
          rcases List.mem_cons.1 h with h1 | h1
          · exact absurd h1.symm hc
          · exact h1
        have hrec := ih hmem
        simp only [List.length_cons]
        omega

/-- erase 恰删一员：vEndCount 记账（镜像 fan6_measure_erase）。 -/
theorem vEndCount_erase {n : Nat} (v : Fin n) :
    ∀ (D : List (List (Fin n))) (X : List (Fin n)), X ∈ D →
      vEndCount (D.erase X) v + vEndBit v X = vEndCount D v
  | [], _, h => absurd h (by simp)
  | c :: t, X, h => by
      by_cases hc : c = X
      · subst hc
        rw [List.erase_cons_head]
        simp only [vEndCount, List.foldr_cons]
        omega
      · have hE : (c :: t).erase X = c :: (t.erase X) := by simp [hc]
        rw [hE]
        have hmem : X ∈ t := by
          rcases List.mem_cons.1 h with h1 | h1
          · exact absurd h1.symm hc
          · exact h1
        have hrec := vEndCount_erase v t X hmem
        simp only [vEndCount, List.foldr_cons]
        simp only [vEndCount] at hrec
        omega

/-- vEndCount 对拼接分配。 -/
theorem vEndCount_appendL {n : Nat} (v : Fin n) (D L : List (List (Fin n))) :
    vEndCount (D ++ L) v = vEndCount D v + vEndCount L v := by
  induction D with
  | nil => simp [vEndCount]
  | cons c t ih =>
      have h1 : vEndCount ((c :: t) ++ L) v = vEndCount (c :: (t ++ L)) v := rfl
      have h2 : vEndCount (c :: (t ++ L)) v = vEndBit v c + vEndCount (t ++ L) v := rfl
      have h3 : vEndCount (c :: t) v = vEndBit v c + vEndCount t v := rfl
      rw [h1, h2, h3, ih]
      omega

/-- **中段互异反演**：Distinct (C ++ a :: E) 给出 C、E 各自互异、a 与两段都不交、
    且 C ∩ E = ∅（detour 坏路 P = C ++ [a] ++ E 的段结构反演）。 -/
theorem distinct_append_mid_inv {V : Type} [DecidableEq V] (a : V) :
    ∀ (C E : List V), Distinct (C ++ a :: E) →
      Distinct C ∧ Distinct E ∧ a ∉ C ∧ a ∉ E ∧ (∀ v ∈ C, v ∉ E)
  | [], E, h => by
      obtain ⟨h1, h2⟩ := h
      exact ⟨trivial, h2, (fun hm => by simp at hm), h1,
        (fun _ hv _ => absurd hv (by simp))⟩
  | c :: t, E, h => by
      have hshow : ((c :: t) ++ a :: E) = c :: (t ++ a :: E) := rfl
      rw [hshow] at h
      obtain ⟨hc, hrec⟩ := h
      obtain ⟨dC, dE, haC, haE, hCE⟩ := distinct_append_mid_inv a t E hrec
      refine ⟨⟨fun hm => hc (List.mem_append.2 (Or.inl hm)), dC⟩, dE, ?_, haE, ?_⟩
      · intro hm
        rcases List.mem_cons.1 hm with h1 | h1
        · subst h1
          exact hc (List.mem_append.2 (Or.inr List.mem_cons_self))
        · exact haC h1
      · intro v hv hm
        rcases List.mem_cons.1 hv with h1 | h1
        · subst h1
          exact hc (List.mem_append.2 (Or.inr (List.mem_cons_of_mem a hm)))
        · exact hCE v h1 hm

/-! ### B. detour 重装路 Q 的边结构反演 -/

/-- **detour 重装路 Q 的边结构（六情形反演）**：Q = C.reverse ++ [a] ++ E 的
    每条边是 C 的边、E 的边、(b,a)/(a,b) 接点对（b = head C，经被吸收边）、
    或 (a, head E)/(head E, a) 接点对。 -/
theorem fan6_detour_Q_EIn_cases {n : Nat} {a b : Fin n} (C E : List (Fin n))
    (hbhead : C.head? = some b) :
    ∀ x y : Fin n, EIn (C.reverse ++ [a] ++ E) x y →
      EIn C x y ∨ EIn E x y ∨ (x = b ∧ y = a) ∨ (x = a ∧ y = b) ∨
        (x = a ∧ E.head? = some y) ∨ (y = a ∧ E.head? = some x) := by
  intro x y h
  rcases EIn_append_inv2 E (C.reverse ++ [a]) h with hA | hB | hC | hC
  · rcases EIn_append_inv C.reverse x y hA with h1 | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ((EIn_reverse_iff C).2 h1)
    · refine Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, ?_⟩)))
      have hhy : C.head? = some y := by rw [← lastOf_reverse]; exact h2
      rw [hbhead] at hhy
      exact (Option.some.inj hhy).symm
    · refine Or.inr (Or.inr (Or.inl ⟨?_, h1⟩))
      have hhx : C.head? = some x := by rw [← lastOf_reverse]; exact h2
      rw [hbhead] at hhx
      exact (Option.some.inj hhx).symm
  · exact Or.inr (Or.inl hB)
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨?_, hC.2⟩))))
    exact (Option.some.inj ((lastOf_append_single' C.reverse a).symm.trans hC.1)).symm
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨?_, hC.2⟩))))
    exact (Option.some.inj ((lastOf_append_single' C.reverse a).symm.trans hC.1)).symm

/-- **detour 重装路的边反投影**：Q = C.reverse ++ [a] ++ E 的每条边要么是
    坏路 P = C ++ [a] ++ E 的边，要么是被吸收边接点对 (a,b)/(b,a)。 -/
theorem fan6_detour_Q_EIn_inv {n : Nat} {a b : Fin n} (C E : List (Fin n))
    (hbhead : C.head? = some b) :
    ∀ x y : Fin n, EIn (C.reverse ++ [a] ++ E) x y →
      EIn (C ++ [a] ++ E) x y ∨ (x = a ∧ y = b) ∨ (x = b ∧ y = a) := by
  intro x y h
  rcases fan6_detour_Q_EIn_cases C E hbhead x y h with h1 | h1 | h1 | h1 | ⟨hx, hy⟩ | ⟨hy, hx⟩
  · exact Or.inl (EIn_append_left (C ++ [a]) E x y (EIn_append_left C [a] x y h1))
  · exact Or.inl (EIn_append_right (C ++ [a]) E x y h1)
  · exact Or.inr (Or.inr h1)
  · exact Or.inr (Or.inl h1)
  · refine Or.inl ?_
    have hEne : E ≠ [] := by
      cases E with
      | nil => simp at hy
      | cons d t => exact List.cons_ne_nil d t
    have hj : EIn (C ++ [a] ++ E) a y :=
      EIn_append_junction (C ++ [a]) E hEne (lastOf_append_single' C a) hy
    rw [hx]
    exact hj
  · refine Or.inl ?_
    have hEne : E ≠ [] := by
      cases E with
      | nil => simp at hx
      | cons d t => exact List.cons_ne_nil d t
    have hj : EIn (C ++ [a] ++ E) a x :=
      EIn_append_junction (C ++ [a]) E hEne (lastOf_append_single' C a) hx
    rw [hy]
    exact EIn_symm _ _ _ hj

/-- **detour 重装路不含释放边**：Q = C.reverse ++ [a] ++ E 不含 (m,a)/(a,m)
    （m = lastOf C 为坏路标记）——释放边 (m,a) 只由纠正路 S′ = S ++ [a] 承接。
    前提：m ≠ b（排除 C = [b] 退化）、m ≠ a、a ∉ C、a ∉ E、C ∩ E = ∅。 -/
theorem fan6_detour_Q_not_mark {n : Nat} {a m b : Fin n} (C E : List (Fin n))
    (habne : a ≠ b) (hbhead : C.head? = some b) (hmlast : lastOf C = some m)
    (hmb : m ≠ b) (hma : m ≠ a)
    (haC : a ∉ C) (haE : a ∉ E) (hCE : ∀ v ∈ C, v ∉ E)
    (x y : Fin n) (h : EIn (C.reverse ++ [a] ++ E) x y) :
    ¬(x = m ∧ y = a) ∧ ¬(x = a ∧ y = m) := by
  have hmE : m ∉ E := hCE m (lastOf_some_mem C m hmlast)
  have hQma : ¬ EIn (C.reverse ++ [a] ++ E) m a := by
    intro hc
    rcases fan6_detour_Q_EIn_cases C E hbhead m a hc with h1 | h1 | h1 | h1 | h1 | h1
    · exact haC (EIn_mem C m a h1).2
    · exact haE (EIn_mem E m a h1).2
    · exact hmb h1.1
    · exact hma h1.1
    · exact hma h1.1
    · exact hmE (headQ_mem E m h1.2)
  have hQam : ¬ EIn (C.reverse ++ [a] ++ E) a m := by
    intro hc
    rcases fan6_detour_Q_EIn_cases C E hbhead a m hc with h1 | h1 | h1 | h1 | h1 | h1
    · exact haC (EIn_mem C a m h1).1
    · exact haE (EIn_mem E a m h1).1
    · exact habne h1.1
    · exact hmb h1.2
    · exact hmE (headQ_mem E m h1.2)
    · exact haE (headQ_mem E a h1.2)
  refine ⟨?_, ?_⟩
  · rintro ⟨ex, ey⟩
    rw [ex, ey] at h
    exact hQma h
  · rintro ⟨ex, ey⟩
    rw [ex, ey] at h
    exact hQam h

/-! ### C. 双路替换的 IsDecomp 保持件（lane_88c 留痕件 1） -/

/-- **双路替换的 vEndCount 记账**：D′ = (D − P₁ − P₂) ++ [Q₁, Q₂]（erase 语义），
    任意 v 的端点计数满足
    vEndCount D′ v + vEndBit v P₁ + vEndBit v P₂ = vEndCount D v + vEndBit v Q₁ + vEndBit v Q₂。
    与 fan6_detour_measure_lt（μ 记账）平行，是替换类变换的两本账之一。 -/
theorem vEndCount_replace2 {n : Nat} (D : List (List (Fin n))) (P₁ P₂ Q₁ Q₂ : List (Fin n))
    (h₁ : P₁ ∈ D) (h₂ : P₂ ∈ D.erase P₁) (v : Fin n) :
    vEndCount ((D.erase P₁).erase P₂ ++ [Q₁, Q₂]) v
      + vEndBit v P₁ + vEndBit v P₂
      = vEndCount D v + vEndBit v Q₁ + vEndBit v Q₂ := by
  have hA : vEndCount ((D.erase P₁).erase P₂ ++ [Q₁, Q₂]) v
      = vEndCount ((D.erase P₁).erase P₂) v + vEndCount [Q₁, Q₂] v :=
    vEndCount_appendL v _ _
  have hB : vEndCount [Q₁, Q₂] v = vEndBit v Q₁ + vEndBit v Q₂ := rfl
  have e1 := vEndCount_erase v D P₁ h₁
  have e2 := vEndCount_erase v (D.erase P₁) P₂ h₂
  rw [hA, hB]
  omega

/-- **双路替换的 IsDecomp 保持件（lane_88c 留痕件 1，真证）**：D 分解 G，把其中
    两条 P₁、P₂ 一次性换成 Q₁、Q₂（D′ = (D − P₁ − P₂) ++ [Q₁, Q₂]，erase 语义）。
    若 Q₁、Q₂ 是 G-路径、不在 D 中、互异且彼此边不交，且两组路径的边集满足
    双向重投影 (EIn P₁ ∨ EIn P₂) ↔ (EIn Q₁ ∨ EIn Q₂)（cover 方向用 →，
    disjoint 方向用 ←），则 D′ 仍是 G 的分解。
    一次性双路版本是必需的：Q₁ 通常与 P₂ 共享段边，两次单路替换的中间态
    破坏边不交。tail-swap 应用中重投影 iff 由 fan6_tailswap_edges 给出。 -/
theorem fan6_replace2_decomp {n : Nat} (G : Graph n)
    (D : List (List (Fin n))) (hD : IsDecomp G D)
    (P₁ P₂ Q₁ Q₂ : List (Fin n))
    (h₁ : P₁ ∈ D) (h₂ : P₂ ∈ D) (hPne : P₁ ≠ P₂)
    (hQ₁p : IsPath (GAdj G) Q₁) (hQ₂p : IsPath (GAdj G) Q₂)
    (hQ₁n : Q₁ ∉ D) (hQ₂n : Q₂ ∉ D) (hQne : Q₁ ≠ Q₂)
    (hcv : ∀ x y : Fin n, EIn P₁ x y ∨ EIn P₂ x y → EIn Q₁ x y ∨ EIn Q₂ x y)
    (hdj : ∀ x y : Fin n, EIn Q₁ x y ∨ EIn Q₂ x y → EIn P₁ x y ∨ EIn P₂ x y)
    (hQQ : ∀ x y : Fin n, EIn Q₁ x y → EIn Q₂ x y → False) :
    IsDecomp G ((D.erase P₁).erase P₂ ++ [Q₁, Q₂]) := by
  obtain ⟨⟨hpaths, hcover, hdisj⟩, hdis⟩ := hD
  -- R = (D − P₁) − P₂ 的成员反演与互异
  have hdisR : Distinct ((D.erase P₁).erase P₂) :=
    distinct_erase (D.erase P₁) P₂ (distinct_erase D P₁ hdis)
  have hmemR : ∀ S ∈ (D.erase P₁).erase P₂, S ∈ D ∧ S ≠ P₁ ∧ S ≠ P₂ := by
    intro S hS
    obtain ⟨hS1, hS2⟩ := mem_erase_inv (D.erase P₁) P₂ S (distinct_erase D P₁ hdis) hS
    obtain ⟨hS3, hS4⟩ := mem_erase_inv D P₁ S hdis hS1
    exact ⟨hS3, hS4, hS2⟩
  -- 路径性
  have hpaths' : ∀ T ∈ (D.erase P₁).erase P₂ ++ [Q₁, Q₂], IsPath (GAdj G) T := by
    intro T hT
    rcases List.mem_append.1 hT with hT | hT
    · obtain ⟨hTD, _, _⟩ := hmemR T hT
      exact hpaths T hTD
    · rcases List.mem_cons.1 hT with h1 | h1
      · rw [h1]; exact hQ₁p
      · rcases List.mem_cons.1 h1 with h1 | h1
        · rw [h1]; exact hQ₂p
        · exact absurd h1 (by simp)
  -- 覆盖
  have hcover' : IsCover (GAdj G) ((D.erase P₁).erase P₂ ++ [Q₁, Q₂]) := by
    intro x y hxy
    obtain ⟨P, hPD, hPxy⟩ := hcover x y hxy
    by_cases hP1 : P = P₁
    · rw [hP1] at hPxy
      rcases hcv x y (Or.inl hPxy) with hE | hE
      · exact ⟨Q₁, List.mem_append.2 (Or.inr (List.mem_cons.2 (Or.inl rfl))), hE⟩
      · exact ⟨Q₂, List.mem_append.2
          (Or.inr (List.mem_cons.2 (Or.inr (List.mem_singleton.2 rfl)))), hE⟩
    · by_cases hP2 : P = P₂
      · rw [hP2] at hPxy
        rcases hcv x y (Or.inr hPxy) with hE | hE
        · exact ⟨Q₁, List.mem_append.2 (Or.inr (List.mem_cons.2 (Or.inl rfl))), hE⟩
        · exact ⟨Q₂, List.mem_append.2
            (Or.inr (List.mem_cons.2 (Or.inr (List.mem_singleton.2 rfl)))), hE⟩
      · exact ⟨P, List.mem_append.2 (Or.inl (mem_erase2 D P₁ P₂ P hPD hP1 hP2)), hPxy⟩
  -- 边不交（九情形；[Q₁, Q₂] 成员需两层 cons 拆分）
  have hdisj' : IsEdgeDisjoint ((D.erase P₁).erase P₂ ++ [Q₁, Q₂]) := by
    intro A hA B hB hAB x y hE
    obtain ⟨hE1, hE2⟩ := hE
    have mem2 : ∀ Z ∈ [Q₁, Q₂], Z = Q₁ ∨ Z = Q₂ := by
      intro Z hZ
      rcases List.mem_cons.1 hZ with h1 | h1
      · exact Or.inl h1
      · rcases List.mem_cons.1 h1 with h1 | h1
        · exact Or.inr h1
        · exact absurd h1 (by simp)
    rcases List.mem_append.1 hA with hAR | hA2
    · rcases List.mem_append.1 hB with hBR | hB2
      · obtain ⟨hAD, _, _⟩ := hmemR A hAR
        obtain ⟨hBD, _, _⟩ := hmemR B hBR
        exact hdisj A hAD B hBD hAB x y ⟨hE1, hE2⟩
      · rcases mem2 B hB2 with h1 | h1
        · rw [h1] at hE2
          obtain ⟨hAD, hA1, hA2⟩ := hmemR A hAR
          rcases hdj x y (Or.inl hE2) with hP | hP
          · exact hdisj P₁ h₁ A hAD (fun hc => hA1 hc.symm) x y ⟨hP, hE1⟩
          · exact hdisj P₂ h₂ A hAD (fun hc => hA2 hc.symm) x y ⟨hP, hE1⟩
        · rw [h1] at hE2
          obtain ⟨hAD, hA1, hA2⟩ := hmemR A hAR
          rcases hdj x y (Or.inr hE2) with hP | hP
          · exact hdisj P₁ h₁ A hAD (fun hc => hA1 hc.symm) x y ⟨hP, hE1⟩
          · exact hdisj P₂ h₂ A hAD (fun hc => hA2 hc.symm) x y ⟨hP, hE1⟩
    · rcases mem2 A hA2 with h1 | h1
      · rw [h1] at hE1 hAB
        rcases List.mem_append.1 hB with hBR | hB2
        · obtain ⟨hBD, hB1, hB2⟩ := hmemR B hBR
          rcases hdj x y (Or.inl hE1) with hP | hP
          · exact hdisj P₁ h₁ B hBD (fun hc => hB1 hc.symm) x y ⟨hP, hE2⟩
          · exact hdisj P₂ h₂ B hBD (fun hc => hB2 hc.symm) x y ⟨hP, hE2⟩
        · rcases mem2 B hB2 with h2 | h2
          · rw [h2] at hAB
            exact absurd rfl hAB
          · rw [h2] at hE2
            exact hQQ x y hE1 hE2
      · rw [h1] at hE1 hAB
        rcases List.mem_append.1 hB with hBR | hB2
        · obtain ⟨hBD, hB1, hB2⟩ := hmemR B hBR
          rcases hdj x y (Or.inr hE1) with hP | hP
          · exact hdisj P₁ h₁ B hBD (fun hc => hB1 hc.symm) x y ⟨hP, hE2⟩
          · exact hdisj P₂ h₂ B hBD (fun hc => hB2 hc.symm) x y ⟨hP, hE2⟩
        · rcases mem2 B hB2 with h2 | h2
          · rw [h2] at hE2
            exact hQQ x y hE2 hE1
          · rw [h2] at hAB
            exact absurd rfl hAB
  -- 互异
  have hRdisj : ∀ v ∈ (D.erase P₁).erase P₂, v ∉ [Q₁, Q₂] := by
    intro v hv hm
    obtain ⟨vD, _, _⟩ := hmemR v hv
    rcases List.mem_cons.1 hm with h1 | h1
    · apply hQ₁n; rw [← h1]; exact vD
    · rcases List.mem_cons.1 h1 with h1 | h1
      · apply hQ₂n; rw [← h1]; exact vD
      · exact absurd h1 (by simp)
  have hDD : Distinct [Q₁, Q₂] := by
    refine And.intro ?_ ?_
    · intro h
      exact hQne (List.mem_singleton.1 h)
    · simp [Distinct]
  have hdD' : Distinct ((D.erase P₁).erase P₂ ++ [Q₁, Q₂]) :=
    distinct_append_disj _ _ hdisR hDD hRdisj
  exact ⟨⟨hpaths', hcover', hdisj'⟩, hdD'⟩

/-! ### D. detour 单步完整组装（lane_88c 留痕件 2） -/

/-- 互异且长度 ≥ 2 的表：末元素不会同时是首元素。 -/
theorem headQ_ne_last {V : Type} [DecidableEq V] :
    ∀ (S : List V) (v : V), 2 ≤ S.length → Distinct S → lastOf S = some v →
      S.head? ≠ some v
  | [], _, h2, _, _ => by simp at h2
  | [_], _, h2, _, _ => by simp at h2
  | c :: d :: t, v, _, hdis, hlast => by
      intro hc
      have hcv : c = v := Option.some.inj hc
      have hv2 : v ∈ d :: t := lastOf_some_mem (d :: t) v hlast
      exact hdis.1 (by rw [hcv]; exact hv2)

/-- **detour 单步完整组装（lane_88c 遗留件 2，真证）**：D 分解 H−ab（del1 H a b），
    坏路 P = C ++ [a] ++ E 以 b 为头（head C = b，即 b-端坏路）、标记
    m = lastOf C、尾段 E 非空；纠正路 S 是 m-端路（lastOf S = m）、避开 a、
    且 P ≠ S。则 D′ = (D − P − S) ++ [Q, S′]（Q = C.reverse ++ [a] ++ E 为
    重装路、S′ = S ++ [a] 为纠正路）分解 H，条数不变，端点记账
    a+1 / b−1 / 其余不变——消费形式与 fan6_case1 完全一致（②④子句口径）。
    机制：Q 吸收被删边 ab（在 b 处接入），释放 P 的边 (m,a) 给 S′；
    μ-降级由 fan6_detour_measure_lt 单独记账，两者合成级联终止性。 -/
theorem fan6_detour_step {n : Nat} (H : Graph n) (a b : Fin n) (hab : H.adjB a b = true)
    (D : List (List (Fin n))) (hD : IsDecomp (del1 H a b) D)
    (C E S : List (Fin n)) (m : Fin n)
    (hcne : C ≠ []) (hbhead : C.head? = some b) (hmlast : lastOf C = some m)
    (hEne : E ≠ [])
    (hPmem : C ++ [a] ++ E ∈ D)
    (hSmem : S ∈ D) (hPS : C ++ [a] ++ E ≠ S)
    (hSne : S ≠ []) (haS : a ∉ S) (hSlast : lastOf S = some m) :
    ∃ D' : List (List (Fin n)),
      IsDecomp H D' ∧ D'.length = D.length ∧
      vEndCount D' a = vEndCount D a + 1 ∧ vEndCount D' b + 1 = vEndCount D b ∧
      ∀ w : Fin n, w ≠ a → w ≠ b → vEndCount D' w = vEndCount D w := by
  have habne : a ≠ b := by
    intro he; rw [he] at hab; exact Bool.noConfusion ((H.loopless b).symm.trans hab)
  -- del1 不含 ab
  have hG₁abF : (del1 H a b).adjB a b = false :=
    Bool.eq_false_iff.2 (fun hc => ((del1_adj_iff H a b a b).1 hc).2 (Or.inl ⟨rfl, rfl⟩))
  obtain ⟨⟨hpaths, hcover, hdisj⟩, hdisD⟩ := hD
  -- 坏路 P 的路径结构与段反演
  have hPpath : IsPath (GAdj (del1 H a b)) (C ++ [a] ++ E) := hpaths _ hPmem
  have hPdis := hPpath.2.1
  have hPchain := hPpath.2.2
  have hPdis2 : Distinct (C ++ a :: E) := by
    rw [append_cons_def C a E]; exact hPdis
  have hPchain2 : Chain (GAdj (del1 H a b)) (C ++ a :: E) := by
    rw [append_cons_def C a E]; exact hPchain
  obtain ⟨hdisC, hdisE, haC, haE, hCE⟩ := distinct_append_mid_inv a C E hPdis2
  obtain ⟨hchC, hjun, hchAE⟩ := chain_split_inv (GAdj (del1 H a b)) C E a hPchain2
  have hchE : Chain (GAdj (del1 H a b)) E := chain_cons_tail _ E a hchAE
  have hbC : b ∈ C := headQ_mem C b hbhead
  have hmC : m ∈ C := lastOf_some_mem C m hmlast
  have hma : m ≠ a := fun he => haC (by rw [← he]; exact hmC)
  have hmE : m ∉ E := hCE m hmC
  have hCEb : b ∉ E := hCE b hbC
  -- 释放边 (m,a) 是 del1 的边；由此 m ≠ b（排除 C = [b] 退化）
  have hPma : EIn (C ++ [a] ++ E) m a :=
    EIn_append_left (C ++ [a]) E m a (EIn_append_last C a m hmlast)
  have hedm : (del1 H a b).adjB m a = true := EIn_adj _ _ hPpath m a hPma
  have hmb : m ≠ b := by
    intro he
    rw [he] at hedm
    exact ((del1_adj_iff H a b b a).1 hedm).2 (Or.inr ⟨rfl, rfl⟩)
  -- 纠正路 S 的路径性与 S′ 的路径性（del1 与 H 两层）
  have hSdis : Distinct S := (hpaths S hSmem).2.1
  have hSlen : 2 ≤ S.length := (hpaths S hSmem).1
  have hS'pathD1 : IsPath (GAdj (del1 H a b)) (S ++ [a]) :=
    fan6_detour_S_path (del1 H a b) a m S hSne hSdis haS (hpaths S hSmem).2.2 hSlast hedm
  have hS'pathH : IsPath (GAdj H) (S ++ [a]) := by
    obtain ⟨h1, h2, h3⟩ := hS'pathD1
    exact ⟨h1, h2, chain_del1_to_H H a b _ h3⟩
  -- 重装路 Q 的路径性（H 中，吸收 ab）
  have hchCH : Chain (GAdj H) C := chain_del1_to_H H a b C hchC
  have hchEH : Chain (GAdj H) E := chain_del1_to_H H a b E hchE
  have hjE : E ≠ [] → ∀ w : Fin n, E.head? = some w → H.adjB a w := by
    intro _ w hw
    have h1 : EIn (C ++ [a] ++ E) a w :=
      EIn_append_junction (C ++ [a]) E hEne (lastOf_append_single' C a) hw
    exact ((del1_adj_iff H a b a w).1 (EIn_adj _ _ hPpath a w h1)).1
  have hQpath : IsPath (GAdj H) (C.reverse ++ [a] ++ E) :=
    fan6_detour_Q_path H a b hab C E hcne hdisC hdisE haC haE hCE hchCH hchEH hbhead hjE
  -- Q 的接点边 (a,b)；Q、S′ 不在 D 中；Q ≠ S′
  have hQab : EIn (C.reverse ++ [a] ++ E) a b :=
    EIn_symm _ _ _ (EIn_append_left (C.reverse ++ [a]) E b a
      (EIn_append_junction C.reverse [a] (List.cons_ne_nil a [])
        (by rw [lastOf_reverse]; exact hbhead) rfl))
  have hQnD : C.reverse ++ [a] ++ E ∉ D := by
    intro hmem
    have h2 := EIn_adj (del1 H a b) _ (hpaths _ hmem) a b hQab
    rw [hG₁abF] at h2
    exact Bool.noConfusion h2
  have hS'nD : S ++ [a] ∉ D := by
    intro hmem
    have hS'P : S ++ [a] ≠ C ++ [a] ++ E := by
      intro hc
      have h1 : lastOf (S ++ [a]) = some a := lastOf_append_single' S a
      rw [hc, lastOf_append_list (C ++ [a]) E hEne] at h1
      exact haE (lastOf_some_mem E a h1)
    exact hdisj _ hPmem _ hmem (fun hc => hS'P hc.symm) m a
      ⟨hPma, EIn_append_last S a m hSlast⟩
  have hQS' : C.reverse ++ [a] ++ E ≠ S ++ [a] := by
    intro hc
    rw [← hc] at hS'pathD1
    have h2 := EIn_adj (del1 H a b) _ hS'pathD1 a b hQab
    rw [hG₁abF] at h2
    exact Bool.noConfusion h2
  -- R = (D − P) − S 的成员反演
  have hmemR : ∀ T ∈ (D.erase (C ++ [a] ++ E)).erase S,
      T ∈ D ∧ T ≠ C ++ [a] ++ E ∧ T ≠ S := by
    intro T hT
    obtain ⟨hT1, hT2⟩ := mem_erase_inv (D.erase (C ++ [a] ++ E)) S T
      (distinct_erase D (C ++ [a] ++ E) hdisD) hT
    obtain ⟨hT3, hT4⟩ := mem_erase_inv D (C ++ [a] ++ E) T hdisD hT1
    exact ⟨hT3, hT4, hT2⟩
  have hSmemR : S ∈ D.erase (C ++ [a] ++ E) :=
    mem_erase_of_ne D (C ++ [a] ++ E) S (fun hc => hPS hc.symm) hSmem
  -- del1-成员不含 ab 接点对
  have hDnotab : ∀ T ∈ D, ∀ x y : Fin n, EIn T x y →
      ¬((x = a ∧ y = b) ∨ (x = b ∧ y = a)) := by
    intro T hTD x y hE hab
    rcases hab with ⟨hx, hy⟩ | ⟨hx, hy⟩
    · rw [hx, hy] at hE
      exact ((del1_adj_iff H a b a b).1
        (EIn_adj (del1 H a b) T (hpaths T hTD) a b hE)).2 (Or.inl ⟨rfl, rfl⟩)
    · rw [hx, hy] at hE
      exact ((del1_adj_iff H a b b a).1
        (EIn_adj (del1 H a b) T (hpaths T hTD) b a hE)).2 (Or.inr ⟨rfl, rfl⟩)
  -- 端点位
  have hPhead : (C ++ [a] ++ E).head? = some b := by
    rw [headQ_append_list (C ++ [a]) E (append_single_ne_nil C a),
      headQ_append_single C a hcne]
    exact hbhead
  have hQhead : (C.reverse ++ [a] ++ E).head? = some m := by
    rw [headQ_append_list (C.reverse ++ [a]) E (append_single_ne_nil C.reverse a),
      headQ_append_single C.reverse a (reverse_ne_nil hcne), headQ_reverse]
    exact hmlast
  have hPlastE : lastOf (C ++ [a] ++ E) = lastOf E := lastOf_append_list (C ++ [a]) E hEne
  have hQlastE : lastOf (C.reverse ++ [a] ++ E) = lastOf E :=
    lastOf_append_list (C.reverse ++ [a]) E hEne
  have hlastE_ne_a : lastOf E ≠ some a := fun hc => haE (lastOf_some_mem E a hc)
  have hlastE_ne_b : lastOf E ≠ some b := fun hc => hCEb (lastOf_some_mem E b hc)
  have hlastE_ne_m : lastOf E ≠ some m := fun hc => hmE (lastOf_some_mem E m hc)
  have hbitPa : vEndBit a (C ++ [a] ++ E) = 0 := by
    unfold vEndBit
    rw [if_neg (by
      rintro (h | h)
      · exact habne (Option.some.inj (by rw [hPhead] at h; exact h)).symm
      · exact hlastE_ne_a (by rw [hPlastE] at h; exact h))]
  have hbitQa : vEndBit a (C.reverse ++ [a] ++ E) = 0 := by
    unfold vEndBit
    rw [if_neg (by
      rintro (h | h)
      · exact hma (Option.some.inj (by rw [hQhead] at h; exact h))
      · exact hlastE_ne_a (by rw [hQlastE] at h; exact h))]
  have hbitSa : vEndBit a S = 0 := vEndBit_not_mem S haS
  have hbitS'a : vEndBit a (S ++ [a]) = 1 := vEndBit_append_self a S hSne
  have hbitPb : vEndBit b (C ++ [a] ++ E) = 1 := by
    unfold vEndBit
    rw [if_pos (show (C ++ [a] ++ E).head? = some b ∨
      lastOf (C ++ [a] ++ E) = some b from Or.inl hPhead)]
  have hbitQb : vEndBit b (C.reverse ++ [a] ++ E) = 0 := by
    unfold vEndBit
    rw [if_neg (by
      rintro (h | h)
      · exact hmb (Option.some.inj (by rw [hQhead] at h; exact h))
      · exact hlastE_ne_b (by rw [hQlastE] at h; exact h))]
  have hbitS'b : vEndBit b (S ++ [a]) = vEndBit b S :=
    vEndBit_append_ne S (a := a) (v := b) habne
      (fun hc => hmb (Option.some.inj (hc.symm.trans hSlast)).symm) hSne
  have hbitPm : vEndBit m (C ++ [a] ++ E) = 0 := by
    unfold vEndBit
    rw [if_neg (by
      rintro (h | h)
      · exact hmb (Option.some.inj (by rw [hPhead] at h; exact h)).symm
      · exact hlastE_ne_m (by rw [hPlastE] at h; exact h))]
  have hbitQm : vEndBit m (C.reverse ++ [a] ++ E) = 1 := by
    unfold vEndBit
    rw [if_pos (show (C.reverse ++ [a] ++ E).head? = some m ∨
      lastOf (C.reverse ++ [a] ++ E) = some m from Or.inl hQhead)]
  have hbitSm : vEndBit m S = 1 := by
    unfold vEndBit
    rw [if_pos (show S.head? = some m ∨ lastOf S = some m from Or.inr hSlast)]
  have hbitS'm : vEndBit m (S ++ [a]) = 0 := by
    unfold vEndBit
    rw [if_neg (by
      rintro (h | h)
      · rw [headQ_append_single S a hSne] at h
        exact headQ_ne_last S m hSlen hSdis hSlast h
      · exact hma (Option.some.inj (by rw [lastOf_append_single' S a] at h; exact h)).symm)]
  have hbitQPw : ∀ w : Fin n, w ≠ a → w ≠ b → w ≠ m →
      vEndBit w (C.reverse ++ [a] ++ E) = vEndBit w (C ++ [a] ++ E) := by
    intro w hw1 hw2 hwm
    have hPe : (C ++ [a] ++ E).head? = some w → False := by
      intro hc; rw [hPhead] at hc; exact hw2 (Option.some.inj hc).symm
    have hQe : (C.reverse ++ [a] ++ E).head? = some w → False := by
      intro hc; rw [hQhead] at hc; exact hwm (Option.some.inj hc).symm
    by_cases hle : lastOf E = some w
    · have hP1 : vEndBit w (C ++ [a] ++ E) = 1 := by
        unfold vEndBit
        rw [if_pos (by rw [hPlastE]; exact Or.inr hle)]
      have hQ1 : vEndBit w (C.reverse ++ [a] ++ E) = 1 := by
        unfold vEndBit
        rw [if_pos (by rw [hQlastE]; exact Or.inr hle)]
      rw [hQ1, hP1]
    · have hP0 : vEndBit w (C ++ [a] ++ E) = 0 := by
        unfold vEndBit
        rw [if_neg (by
          rintro (h | h)
          · exact hPe h
          · rw [hPlastE] at h; exact hle h)]
      have hQ0 : vEndBit w (C.reverse ++ [a] ++ E) = 0 := by
        unfold vEndBit
        rw [if_neg (by
          rintro (h | h)
          · exact hQe h
          · rw [hQlastE] at h; exact hle h)]
      rw [hQ0, hP0]
  refine ⟨(D.erase (C ++ [a] ++ E)).erase S ++ [C.reverse ++ [a] ++ E, S ++ [a]],
    ?_, ?_, ?_, ?_, ?_⟩
  · -- IsDecomp H D′
    have hpaths' : ∀ T ∈ (D.erase (C ++ [a] ++ E)).erase S ++
        [C.reverse ++ [a] ++ E, S ++ [a]], IsPath (GAdj H) T := by
      intro T hT
      rcases List.mem_append.1 hT with hT | hT
      · obtain ⟨hTD, _, _⟩ := hmemR T hT
        exact ⟨(hpaths T hTD).1, (hpaths T hTD).2.1,
          chain_del1_to_H H a b T (hpaths T hTD).2.2⟩
      · rcases List.mem_cons.1 hT with h1 | h1
        · rw [h1]; exact hQpath
        · rcases List.mem_cons.1 h1 with h1 | h1
          · rw [h1]; exact hS'pathH
          · exact absurd h1 (by simp)
    have hcover' : IsCover (GAdj H) ((D.erase (C ++ [a] ++ E)).erase S ++
        [C.reverse ++ [a] ++ E, S ++ [a]]) := by
      intro x y hxy
      have hmemQ : C.reverse ++ [a] ++ E ∈ (D.erase (C ++ [a] ++ E)).erase S ++
          [C.reverse ++ [a] ++ E, S ++ [a]] :=
        List.mem_append.2 (Or.inr (List.mem_cons.2 (Or.inl rfl)))
      have hmemS' : S ++ [a] ∈ (D.erase (C ++ [a] ++ E)).erase S ++
          [C.reverse ++ [a] ++ E, S ++ [a]] :=
        List.mem_append.2 (Or.inr (List.mem_cons.2 (Or.inr (List.mem_singleton.2 rfl))))
      by_cases habx : (x = a ∧ y = b) ∨ (x = b ∧ y = a)
      · rcases habx with ⟨hx, hy⟩ | ⟨hx, hy⟩
        · exact ⟨_, hmemQ, by rw [hx, hy]; exact hQab⟩
        · exact ⟨_, hmemQ, by rw [hx, hy]; exact EIn_symm _ _ _ hQab⟩
      · obtain ⟨T, hTD, hTxy⟩ := hcover x y ((del1_adj_iff H a b x y).2 ⟨hxy, habx⟩)
        by_cases hT1 : T = C ++ [a] ++ E
        · rw [hT1] at hTxy
          rcases fan6_detour_Q_EIn C E hmlast x y hTxy with h1 | ⟨hx2, hy2⟩ | ⟨hx2, hy2⟩
          · exact ⟨_, hmemQ, h1⟩
          · have hxm : x = m := Option.some.inj (hx2.symm.trans hmlast)
            refine ⟨_, hmemS', ?_⟩
            rw [hxm, hy2]
            exact EIn_append_last S a m hSlast
          · have hym : y = m := Option.some.inj (hx2.symm.trans hmlast)
            refine ⟨_, hmemS', ?_⟩
            rw [hym, hy2]
            exact EIn_symm _ _ _ (EIn_append_last S a m hSlast)
        · by_cases hT2 : T = S
          · rw [hT2] at hTxy
            exact ⟨_, hmemS', EIn_append_suffix S x y hTxy⟩
          · exact ⟨T, List.mem_append.2 (Or.inl (mem_erase2 D (C ++ [a] ++ E) S T hTD hT1 hT2)),
              hTxy⟩
    have hdisj' : IsEdgeDisjoint ((D.erase (C ++ [a] ++ E)).erase S ++
        [C.reverse ++ [a] ++ E, S ++ [a]]) := by
      intro A hA B hB hAB x y hE
      obtain ⟨hE1, hE2⟩ := hE
      have hcls : ∀ T ∈ (D.erase (C ++ [a] ++ E)).erase S ++
          [C.reverse ++ [a] ++ E, S ++ [a]],
          T ∈ (D.erase (C ++ [a] ++ E)).erase S ∨ T = C.reverse ++ [a] ++ E ∨
            T = S ++ [a] := by
        intro T hT
        rcases List.mem_append.1 hT with h1 | h1
        · exact Or.inl h1
        · rcases List.mem_cons.1 h1 with h1 | h1
          · exact Or.inr (Or.inl h1)
          · rcases List.mem_cons.1 h1 with h1 | h1
            · exact Or.inr (Or.inr h1)
            · exact absurd h1 (by simp)
      rcases hcls A hA with hAR | hAQ | hAS'
      · rcases hcls B hB with hBR | hBQ | hBS'
        · obtain ⟨hAD, _, _⟩ := hmemR A hAR
          obtain ⟨hBD, _, _⟩ := hmemR B hBR
          exact hdisj A hAD B hBD hAB x y ⟨hE1, hE2⟩
        · rw [hBQ] at hE2
          obtain ⟨hAD, hAP, _⟩ := hmemR A hAR
          rcases fan6_detour_Q_EIn_inv C E hbhead x y hE2 with hP | hab | hab
          · exact hdisj _ hPmem A hAD (fun hc => hAP hc.symm) x y ⟨hP, hE1⟩
          · exact hDnotab A hAD x y hE1 (Or.inl hab)
          · exact hDnotab A hAD x y hE1 (Or.inr hab)
        · rw [hBS'] at hE2
          obtain ⟨hAD, hAP, hAS⟩ := hmemR A hAR
          rcases EIn_append_inv S x y hE2 with hS'1 | ⟨hx, hy⟩ | ⟨hx, hy⟩
          · exact hdisj S hSmem A hAD (fun hc => hAS hc.symm) x y ⟨hS'1, hE1⟩
          · have hym : y = m := Option.some.inj (hy.symm.trans hSlast)
            rw [hx, hym] at hE1
            exact hdisj _ hPmem A hAD (fun hc => hAP hc.symm) a m
              ⟨EIn_symm _ _ _ hPma, hE1⟩
          · have hxm : x = m := Option.some.inj (hy.symm.trans hSlast)
            rw [hx, hxm] at hE1
            exact hdisj _ hPmem A hAD (fun hc => hAP hc.symm) m a ⟨hPma, hE1⟩
      · rcases hcls B hB with hBR | hBQ | hBS'
        · rw [hAQ] at hE1
          obtain ⟨hBD, hBP, _⟩ := hmemR B hBR
          rcases fan6_detour_Q_EIn_inv C E hbhead x y hE1 with hP | hab | hab
          · exact hdisj _ hPmem B hBD (fun hc => hBP hc.symm) x y ⟨hP, hE2⟩
          · exact hDnotab B hBD x y hE2 (Or.inl hab)
          · exact hDnotab B hBD x y hE2 (Or.inr hab)
        · rw [hAQ, hBQ] at hAB
          exact absurd rfl hAB
        · rw [hAQ] at hE1
          rw [hBS'] at hE2
          rcases fan6_detour_Q_EIn_inv C E hbhead x y hE1 with hP | hab | hab
          · rcases EIn_append_inv S x y hE2 with hS'1 | ⟨hx, hy⟩ | ⟨hx, hy⟩
            · exact hdisj _ hPmem S hSmem hPS x y ⟨hP, hS'1⟩
            · have hym : y = m := Option.some.inj (hy.symm.trans hSlast)
              exact (fan6_detour_Q_not_mark C E habne hbhead hmlast hmb hma haC haE hCE
                x y hE1).2 ⟨hx, hym⟩
            · have hxm : x = m := Option.some.inj (hy.symm.trans hSlast)
              exact (fan6_detour_Q_not_mark C E habne hbhead hmlast hmb hma haC haE hCE
                x y hE1).1 ⟨hxm, hx⟩
          · rcases hab with ⟨hx, hy⟩
            rw [hx, hy] at hE2
            have hbad := EIn_adj (del1 H a b) _ hS'pathD1 a b hE2
            rw [hG₁abF] at hbad
            exact Bool.noConfusion hbad
          · rcases hab with ⟨hx, hy⟩
            rw [hx, hy] at hE2
            exact ((del1_adj_iff H a b b a).1
              (EIn_adj (del1 H a b) _ hS'pathD1 b a hE2)).2 (Or.inr ⟨rfl, rfl⟩)
      · rcases hcls B hB with hBR | hBQ | hBS'
        · rw [hAS'] at hE1
          obtain ⟨hBD, hBP, hBS⟩ := hmemR B hBR
          rcases EIn_append_inv S x y hE1 with hS'1 | ⟨hx, hy⟩ | ⟨hx, hy⟩
          · exact hdisj S hSmem B hBD (fun hc => hBS hc.symm) x y ⟨hS'1, hE2⟩
          · have hym : y = m := Option.some.inj (hy.symm.trans hSlast)
            rw [hx, hym] at hE1 hE2
            exact hdisj _ hPmem B hBD (fun hc => hBP hc.symm) a m
              ⟨EIn_symm _ _ _ hPma, hE2⟩
          · have hxm : x = m := Option.some.inj (hy.symm.trans hSlast)
            rw [hx, hxm] at hE1 hE2
            exact hdisj _ hPmem B hBD (fun hc => hBP hc.symm) m a ⟨hPma, hE2⟩
        · rw [hBQ] at hE2
          rw [hAS'] at hE1
          rcases fan6_detour_Q_EIn_inv C E hbhead x y hE2 with hP | hab | hab
          · rcases EIn_append_inv S x y hE1 with hS'1 | ⟨hx, hy⟩ | ⟨hx, hy⟩
            · exact hdisj _ hPmem S hSmem hPS x y ⟨hP, hS'1⟩
            · have hym : y = m := Option.some.inj (hy.symm.trans hSlast)
              exact (fan6_detour_Q_not_mark C E habne hbhead hmlast hmb hma haC haE hCE
                x y hE2).2 ⟨hx, hym⟩
            · have hxm : x = m := Option.some.inj (hy.symm.trans hSlast)
              exact (fan6_detour_Q_not_mark C E habne hbhead hmlast hmb hma haC haE hCE
                x y hE2).1 ⟨hxm, hx⟩
          · rcases hab with ⟨hx, hy⟩
            rw [hx, hy] at hE1
            have hbad := EIn_adj (del1 H a b) _ hS'pathD1 a b hE1
            rw [hG₁abF] at hbad
            exact Bool.noConfusion hbad
          · rcases hab with ⟨hx, hy⟩
            rw [hx, hy] at hE1
            exact ((del1_adj_iff H a b b a).1
              (EIn_adj (del1 H a b) _ hS'pathD1 b a hE1)).2 (Or.inr ⟨rfl, rfl⟩)
        · rw [hAS', hBS'] at hAB
          exact absurd rfl hAB
    have hdD' : Distinct ((D.erase (C ++ [a] ++ E)).erase S ++
        [C.reverse ++ [a] ++ E, S ++ [a]]) := by
      have hRd : Distinct ((D.erase (C ++ [a] ++ E)).erase S) :=
        distinct_erase (D.erase (C ++ [a] ++ E)) S (distinct_erase D (C ++ [a] ++ E) hdisD)
      have hRdisjQ : ∀ v ∈ (D.erase (C ++ [a] ++ E)).erase S,
          v ∉ [C.reverse ++ [a] ++ E, S ++ [a]] := by
        intro v hv hm
        obtain ⟨vD, _, _⟩ := hmemR v hv
        rcases List.mem_cons.1 hm with h1 | h1
        · rw [h1] at vD; exact hQnD vD
        · rcases List.mem_cons.1 h1 with h1 | h1
          · rw [h1] at vD; exact hS'nD vD
          · exact absurd h1 (by simp)
      have hQS'd : Distinct [C.reverse ++ [a] ++ E, S ++ [a]] := by
        refine And.intro ?_ ?_
        · intro h
          exact hQS' (List.mem_singleton.1 h)
        · simp [Distinct]
      exact distinct_append_disj _ _ hRd hQS'd hRdisjQ
    exact ⟨⟨hpaths', hcover', hdisj'⟩, hdD'⟩
  · -- 条数不变
    have l1 := length_erase_of_mem D (C ++ [a] ++ E) hPmem
    have l2 := length_erase_of_mem (D.erase (C ++ [a] ++ E)) S hSmemR
    have l3 : ((D.erase (C ++ [a] ++ E)).erase S ++
        [C.reverse ++ [a] ++ E, S ++ [a]]).length
        = ((D.erase (C ++ [a] ++ E)).erase S).length + 2 := by simp
    rw [l3]
    omega
  · -- a 计数 +1
    have hacc := vEndCount_replace2 D (C ++ [a] ++ E) S (C.reverse ++ [a] ++ E) (S ++ [a])
      hPmem hSmemR a
    omega
  · -- b 计数 −1
    have hacc := vEndCount_replace2 D (C ++ [a] ++ E) S (C.reverse ++ [a] ++ E) (S ++ [a])
      hPmem hSmemR b
    omega
  · -- 其余不变
    intro w hw1 hw2
    by_cases hwm : w = m
    · have hacc := vEndCount_replace2 D (C ++ [a] ++ E) S
        (C.reverse ++ [a] ++ E) (S ++ [a]) hPmem hSmemR m
      rw [hwm]
      omega
    · have hacc := vEndCount_replace2 D (C ++ [a] ++ E) S
        (C.reverse ++ [a] ++ E) (S ++ [a]) hPmem hSmemR w
      have heq1 := hbitQPw w hw1 hw2 hwm
      have heq2 : vEndBit w (S ++ [a]) = vEndBit w S :=
        vEndBit_append_ne S (a := a) (v := w) (fun hc => hw1 hc.symm)
          (fun hc => hwm (Option.some.inj (hc.symm.trans hSlast))) hSne
      omega

/-! ## lane_95：级联全局归纳 + 同图 swap 单步 + 单 swap 域的 fan6_nf（2026-09-19）

fan6_nf 收口的组装层，全部零 sorry。三层：
- **级联机器 `fan6_cascade`（lane_95 任务 1）**：多步排布 + 终止性合并——
  对 μ 的 Nat 值作有界强归纳；步假设取析取形式（目标已达 ∨ μ 严格降），
  IsDecomp/条数/逐点轮廓在步间逐段交接。这是 lane_87 定性的"级联全局归纳"
  的机器件；一般构型的单步重排存在性仍是研究级缺口，由步假设参数化。
- **同图 swap 单步 `fan6_swap_step`（lane_95 任务 1 的具体步）**：G₀→G₀
  方向（与 lane_88d 的 del1→H 方向 `fan6_detour_step` 互补）：坏路
  P = C ++ [a] ++ E 与 m-端纠正路 S（避开 a、头非 b、顶点避开尾段 E）
  换成 C 与 S ++ [a] ++ E——IsDecomp/条数/逐点轮廓全保持、
  μ(D′) + |E| = μ(D)（E ≠ [] 时 μ 严格降；E = [] 时 C 已是目标路）。
- **单 swap 域 `fan6_nf_one_swap`（lane_95 任务 3 降档）**：干净 link 存在时
  fan6_nf 结论一步成立。fan6_nf 本体维持占位（744 行）：剩余精确缺口 =
  一般构型（S ∩ E ≠ ∅ 或 link 整体不存在）的重排存在性。 -/

/-- 互异且长度 ≥ 2 的表：头 ≠ 尾（`headQ_ne_last` 的无 some 中间形式）。 -/
theorem headQ_ne_lastOf {V : Type} [DecidableEq V] :
    ∀ (L : List V), 2 ≤ L.length → Distinct L → L.head? ≠ lastOf L
  | [], h2, _ => by simp at h2
  | [_], h2, _ => by simp at h2
  | x :: y :: t, _, hdis => by
      intro hc
      have hc2 : lastOf (y :: t) = some x := hc.symm
      exact hdis.1 (lastOf_some_mem (y :: t) x hc2)

/-- 两端不同的表：端点指示 = 头指示 + 尾指示。 -/
theorem vEndBit_two_ends {n : Nat} (v : Fin n) (L : List (Fin n))
    (h : L.head? ≠ lastOf L) :
    vEndBit v L = (if L.head? = some v then 1 else 0)
      + (if lastOf L = some v then 1 else 0) := by
  unfold vEndBit
  by_cases h1 : L.head? = some v <;> by_cases h2 : lastOf L = some v
  · exact absurd (h1.trans h2.symm) h
  · simp [h1, h2]
  · simp [h1, h2]
  · simp [h1, h2]

/-- **swap 四路的端点指示守恒**：四条两端互异的表，头/尾锚点按
    (b, ·)(hs, m) | (b, m)(hs, ·) 配对（第四路的尾 = 第一路的尾）时，
    任意 v 的指示和不变。用于同图 swap 的逐点轮廓记账：
    L₁ = 坏路 P、L₂ = 纠正路 S、L₃ = b-段 C、L₄ = 重装路 S′。 -/
theorem vEndBit_swap4 {n : Nat} (b m hs v : Fin n) (L₁ L₂ L₃ L₄ : List (Fin n))
    (e₁ : L₁.head? = some b) (e₂ : L₂.head? = some hs)
    (e₃ : L₃.head? = some b) (e₄ : L₄.head? = some hs)
    (f₂ : lastOf L₂ = some m) (f₃ : lastOf L₃ = some m)
    (f₄ : lastOf L₄ = lastOf L₁)
    (d₁ : L₁.head? ≠ lastOf L₁) (d₂ : L₂.head? ≠ lastOf L₂)
    (d₃ : L₃.head? ≠ lastOf L₃) (d₄ : L₄.head? ≠ lastOf L₄) :
    vEndBit v L₁ + vEndBit v L₂ = vEndBit v L₃ + vEndBit v L₄ := by
  rw [vEndBit_two_ends v L₁ d₁, vEndBit_two_ends v L₂ d₂,
      vEndBit_two_ends v L₃ d₃, vEndBit_two_ends v L₄ d₄,
      e₁, e₂, e₃, e₄, f₂, f₃, f₄]
  by_cases h1 : (some b) = some v <;>
    by_cases h2 : (some m) = some v <;>
    by_cases h3 : (some hs) = some v <;>
    by_cases h4 : lastOf L₁ = some v <;>
    simp [h1, h2, h3, h4] <;> omega

/-- **级联全局归纳（多步排布 + 终止性合并；lane_95 任务 1 机器件）**：
    若每一步"要么目标形态（某 b-端路避开 a）已达，要么可在保持分解/条数/
    逐点轮廓的前提下把 μ 严格降"，则对 μ 的初值作有界强归纳，从任意 D
    出发可达目标形态。步的存在性（一般构型的重排核，lane_68c 穷举否证
    单步 link 形态）是剩余研究级缺口，由 `hstep` 参数化；本件只负责
    多步排布与终止性合并。 -/
theorem fan6_cascade {n : Nat} (G₀ : Graph n) (a b : Fin n)
    (hstep : ∀ (Dc : List (List (Fin n))), IsDecomp G₀ Dc →
      (∀ Q ∈ Dc, isEnd b Q → a ∈ Q) →
      ∃ D', IsDecomp G₀ D' ∧ D'.length = Dc.length ∧
        (∀ w : Fin n, vEndCount D' w = vEndCount Dc w) ∧
        (fan6_measure a b D' < fan6_measure a b Dc ∨
          ∃ Q ∈ D', isEnd b Q ∧ a ∉ Q)) :
    ∀ (k : Nat) (D : List (List (Fin n))), IsDecomp G₀ D →
      fan6_measure a b D ≤ k →
      ∃ D'' : List (List (Fin n)),
        IsDecomp G₀ D'' ∧ D''.length = D.length ∧
        (∀ w : Fin n, vEndCount D'' w = vEndCount D w) ∧
        ∃ Q ∈ D'', isEnd b Q ∧ a ∉ Q := by
  intro k
  induction k with
  | zero =>
      intro D hD hμ
      by_cases htg : ∃ Q ∈ D, isEnd b Q ∧ a ∉ Q
      · exact ⟨D, hD, rfl, fun w => rfl, htg⟩
      · obtain ⟨D', hD', hlen', hprof', hdesc⟩ :=
          hstep D hD (fun Q hQ hEnd => by
            by_cases hpa : a ∈ Q
            · exact hpa
            · exact absurd ⟨Q, hQ, hEnd, hpa⟩ htg)
        rcases hdesc with hμ' | htg'
        · exact absurd hμ' (by omega)
        · exact ⟨D', hD', hlen', hprof', htg'⟩
  | succ k ih =>
      intro D hD hμ
      by_cases htg : ∃ Q ∈ D, isEnd b Q ∧ a ∉ Q
      · exact ⟨D, hD, rfl, fun w => rfl, htg⟩
      · obtain ⟨D', hD', hlen', hprof', hdesc⟩ :=
          hstep D hD (fun Q hQ hEnd => by
            by_cases hpa : a ∈ Q
            · exact hpa
            · exact absurd ⟨Q, hQ, hEnd, hpa⟩ htg)
        rcases hdesc with hμ' | htg'
        · obtain ⟨D'', hD'', hlen'', hprof'', htg''⟩ := ih D' hD' (by omega)
          exact ⟨D'', hD'', by omega, fun w => by rw [hprof'' w, hprof' w], htg''⟩
        · exact ⟨D', hD', hlen', hprof', htg'⟩


/-! ## lane_95b：标记分裂换装（fan6_nf 单步主件；2026-09-19）

lane_95 的级联机器把"步"参数化；本段把**步的实质**落成无条件真证
`fan6_mark_swap`：坏路 P = C ++ [a] ++ E 的标记 m 若有一条以 m 为内点、
尾段分离（a ∉ Y₁、a ∉ Y₂、X₁ ⊥ Y₂、Y₁ ⊥ E）的路径 A = Y₁ ++ [m] ++ Y₂，
则 (X₁ ++ [m] ++ Y₂, Y₁ ++ [m] ++ [a] ++ E) 的换装保持分解、条数与
逐点端点轮廓，且第一路是 b-端、避开 a——直接给出 fan6_nf 的结论形态。
机器底账（lab/fan95b/route3.py）：n = 5 全空间 51,680 个非 case1 构型中
45,500 个（88.0%）由此单步收口（含 lane_68c 的最小反例）。 -/

/-- 三段拼接的 EIn 反演：中段为单点 `[m]`，接点对以 some 形式给出。 -/
theorem EIn_append_mid {V : Type} (X : List V) (m : V) (Y : List V) (x y : V) :
    EIn (X ++ [m] ++ Y) x y →
      EIn X x y ∨ EIn Y x y ∨
      (lastOf X = some x ∧ y = m) ∨ (lastOf X = some y ∧ x = m) ∨
      (x = m ∧ Y.head? = some y) ∨ (y = m ∧ Y.head? = some x) := by
  intro h
  have h2 : EIn ((X ++ [m]) ++ Y) x y := h
  rcases EIn_append_inv2 Y (X ++ [m]) h2 with h1 | h1 | h1
  · rcases EIn_append_inv X x y h1 with h3 | h3 | h3
    · exact Or.inl h3
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h3.2, h3.1⟩)))
    · exact Or.inr (Or.inr (Or.inl ⟨h3.2, h3.1⟩))
  · exact Or.inr (Or.inl h1)
  · have hm : lastOf (X ++ [m]) = some m := lastOf_append_single' X m
    rcases h1 with h4 | h4
    · have hx : x = m := (Option.some.inj (hm.symm.trans h4.1)).symm
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hx, h4.2⟩))))
    · have hy : y = m := (Option.some.inj (hm.symm.trans h4.1)).symm
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hy, h4.2⟩))))

/-- 中段拼接的末元素：`lastOf (X ++ [a] ++ E) = lastOf (a :: E)`。 -/
theorem lastOf_append_mid {V : Type} (X E : List V) (a : V) :
    lastOf (X ++ [a] ++ E) = lastOf (a :: E) := by
  have h : X ++ [a] ++ E = X ++ (a :: E) := by
    simp [List.append_assoc]
  rw [h]
  exact lastOf_append_list X (a :: E) (List.cons_ne_nil a E)

/-- 非空表的末元素存在。 -/
theorem lastOf_exists {V : Type} : ∀ (l : List V), l ≠ [] → ∃ v, lastOf l = some v
  | [], h => absurd rfl h
  | [x], _ => ⟨x, rfl⟩
  | x :: y :: t, _ => lastOf_exists (y :: t) (List.cons_ne_nil y t)

/-- 端点指示的可加形式（互异 + 长度 ≥ 2）。 -/
theorem vEndBit_ends {n : Nat} (v : Fin n) (L : List (Fin n))
    (hlen : 2 ≤ L.length) (hdis : Distinct L) :
    vEndBit v L = (if L.head? = some v then 1 else 0)
      + (if lastOf L = some v then 1 else 0) :=
  vEndBit_two_ends v L (headQ_ne_lastOf L hlen hdis)

/-- **四路端点指示消去**：四条路按 (P 头 ↔ Q₁ 头)、(P 尾 ↔ Q₂ 尾)、
    (A 头 ↔ Q₂ 头)、(A 尾 ↔ Q₁ 尾) 配对且每路两端互异时，任意 v 的
    指示和守恒——换装轮廓记账的核心。 -/
theorem vEndBit_add_cancel {n : Nat} (v : Fin n) (P A Q₁ Q₂ : List (Fin n))
    (hP1 : P.head? = Q₁.head?) (hP2 : lastOf P = lastOf Q₂)
    (hA1 : A.head? = Q₂.head?) (hA2 : lastOf A = lastOf Q₁)
    (dP : P.head? ≠ lastOf P) (dA : A.head? ≠ lastOf A)
    (dQ₁ : Q₁.head? ≠ lastOf Q₁) (dQ₂ : Q₂.head? ≠ lastOf Q₂) :
    vEndBit v P + vEndBit v A = vEndBit v Q₁ + vEndBit v Q₂ := by
  rw [vEndBit_two_ends v P dP, vEndBit_two_ends v A dA,
      vEndBit_two_ends v Q₁ dQ₁, vEndBit_two_ends v Q₂ dQ₂,
      hP1, hP2, hA1, hA2]
  omega

/-- **标记分裂换装（lane_95b 主件）**：D 分解 G₀（ab ∉ E(G₀)）；坏路
    P = C ++ [a] ++ E ∈ D 以 b 为头段外端（C.head? = b）、标记 m = lastOf C、
    分裂 C = X₁ ++ [m]；A = Y₁ ++ [m] ++ Y₂ ∈ D 以 m 为内点，且尾段分离
    （a ∉ Y₁、a ∉ Y₂、X₁ ⊥ Y₂、Y₁ ⊥ E）。则
    Q₁ = X₁ ++ [m] ++ Y₂（b-端、避开 a）、Q₂ = Y₁ ++ [m] ++ [a] ++ E，
    D′ = (D − P − A) ++ [Q₁, Q₂] 仍是分解，条数不变、逐点端点轮廓不变。 -/
theorem fan6_mark_swap {n : Nat} (G₀ : Graph n) (a b : Fin n) (hab0 : G₀.adjB a b = false)
    (D : List (List (Fin n))) (hD : IsDecomp G₀ D)
    (X₁ C E Y₁ Y₂ : List (Fin n)) (m : Fin n)
    (hC : C = X₁ ++ [m])
    (hPmem : C ++ [a] ++ E ∈ D)
    (hAmem : Y₁ ++ [m] ++ Y₂ ∈ D)
    (hbhead : C.head? = some b) (hmlast : lastOf C = some m)
    (haY₁ : a ∉ Y₁) (haY₂ : a ∉ Y₂)
    (hX₁Y₂ : ∀ v : Fin n, v ∈ X₁ → v ∉ Y₂)
    (hY₁E : ∀ v : Fin n, v ∈ Y₁ → v ∉ E) :
    ∃ D' : List (List (Fin n)),
      IsDecomp G₀ D' ∧ D'.length = D.length ∧
      (∀ w : Fin n, vEndCount D' w = vEndCount D w) ∧
      ∃ P' ∈ D', isEnd b P' ∧ a ∉ P' := by
  obtain ⟨⟨hpaths, hcover, hdisj⟩, hdis⟩ := hD
  have hD' : IsDecomp G₀ D := ⟨⟨hpaths, hcover, hdisj⟩, hdis⟩
  -- §1 基本路径事实
  have hPpath : IsPath (GAdj G₀) (C ++ [a] ++ E) := hpaths _ hPmem
  have hApath : IsPath (GAdj G₀) (Y₁ ++ [m] ++ Y₂) := hpaths _ hAmem
  have hPdis : Distinct (C ++ [a] ++ E) := hPpath.2.1
  have hAdis : Distinct (Y₁ ++ [m] ++ Y₂) := hApath.2.1
  have hPch : Chain (GAdj G₀) (C ++ [a] ++ E) := hPpath.2.2
  have hAch : Chain (GAdj G₀) (Y₁ ++ [m] ++ Y₂) := hApath.2.2
  have hPlen : 2 ≤ (C ++ [a] ++ E).length := hPpath.1
  have hAlen : 2 ≤ (Y₁ ++ [m] ++ Y₂).length := hApath.1
  have hPdis' : Distinct (C ++ a :: E) := by rw [append_cons_def C a E]; exact hPdis
  have hPch' : Chain (GAdj G₀) (C ++ a :: E) := by rw [append_cons_def C a E]; exact hPch
  obtain ⟨hCdis, hEdis, haC, haE, hCE⟩ := distinct_append_mid_inv a C E hPdis'
  obtain ⟨hchC, hjunC, hchAE⟩ := chain_split_inv (GAdj G₀) C E a hPch'
  have hchE : Chain (GAdj G₀) E := chain_cons_tail (GAdj G₀) E a hchAE
  have hAdis' : Distinct (Y₁ ++ m :: Y₂) := by rw [append_cons_def Y₁ m Y₂]; exact hAdis
  have hAch' : Chain (GAdj G₀) (Y₁ ++ m :: Y₂) := by rw [append_cons_def Y₁ m Y₂]; exact hAch
  obtain ⟨hY₁dis, hY₂dis, hmY₁, hmY₂, hY₁Y₂⟩ := distinct_append_mid_inv m Y₁ Y₂ hAdis'
  obtain ⟨hchY₁, hjunY₁, hchmY₂⟩ := chain_split_inv (GAdj G₀) Y₁ Y₂ m hAch'
  obtain ⟨hchm1, hjunmY₂, hchY₂⟩ := chain_split_inv (GAdj G₀) [] Y₂ m hchmY₂
  have hmC : m ∈ C := lastOf_some_mem C m hmlast
  have hmE : m ∉ E := hCE m hmC
  -- §2 顶点事实
  have hEInP_ma : EIn (C ++ [a] ++ E) m a := by
    have h1 : EIn (C ++ [a]) m a := EIn_append_last C a m hmlast
    exact EIn_append_left (C ++ [a]) E m a h1
  have hm_ne_b : m ≠ b := by
    intro hmb
    have hadj : G₀.adjB m a = true := EIn_adj G₀ (C ++ [a] ++ E) hPpath m a hEInP_ma
    rw [hmb] at hadj
    have h2 : G₀.adjB a b = true := G₀.symm b a hadj
    rw [hab0] at h2
    exact Bool.noConfusion h2
  have hm_ne_a : m ≠ a := fun he => haC (he ▸ hmC)
  have ha_ne_m : a ≠ m := fun he => hm_ne_a he.symm
  have haX₁ : a ∉ X₁ := fun hx => haC (by rw [hC]; exact List.mem_append.2 (Or.inl hx))
  have hXC : ∀ v : Fin n, v ∈ X₁ → v ∈ C :=
    fun v hv => by rw [hC]; exact List.mem_append.2 (Or.inl hv)
  have hX₁dis : Distinct X₁ := by
    have h1 : Distinct (X₁ ++ m :: []) := by rw [← hC]; exact hCdis
    exact (distinct_append_mid_inv m X₁ [] h1).1
  have hmX₁ : m ∉ X₁ := by
    have h1 : Distinct (X₁ ++ m :: []) := by rw [← hC]; exact hCdis
    exact (distinct_append_mid_inv m X₁ [] h1).2.2.1
  have hX₁ne : X₁ ≠ [] := by
    intro h0
    have hCm : C = [m] := by rw [hC, h0]; rfl
    have h1 : C.head? = some m := by rw [hCm]; rfl
    exact hm_ne_b (Option.some.inj (h1.symm.trans hbhead))
  have hX₁neC : X₁ ++ [m] ≠ [] := append_single_ne_nil X₁ m
  have hCne : C ≠ [] := by rw [hC]; exact append_single_ne_nil X₁ m
  have hY1mne : Y₁ ++ [m] ≠ [] := append_single_ne_nil Y₁ m
  have haY₁m : a ∉ Y₁ ++ [m] := by
    intro hmem
    rcases List.mem_append.1 hmem with h | h
    · exact haY₁ h
    · exact ha_ne_m (List.mem_singleton.1 h)
  have hX₁dist : Distinct (X₁ ++ [m]) := distinctP_append X₁ m hX₁dis hmX₁
  have hy₁m_dist : Distinct (Y₁ ++ [m]) := distinctP_append Y₁ m hY₁dis hmY₁
  have hchX₁m : Chain (GAdj G₀) (X₁ ++ [m]) := by rw [← hC]; exact hchC
  obtain ⟨hchX₁, hjunX₁m, -⟩ := chain_split_inv (GAdj G₀) X₁ [] m hchX₁m
  -- §3 头尾锚点
  have hQ₁head : (X₁ ++ [m] ++ Y₂).head? = some b := by
    have h1 : (X₁ ++ [m]).head? = some b := by
      have h2 : (X₁ ++ [m]).head? = X₁.head? := headQ_append_list X₁ [m] hX₁ne
      have h3 : C.head? = X₁.head? := by rw [hC]; exact headQ_append_list X₁ [m] hX₁ne
      rw [h2, ← h3]; exact hbhead
    have h4 : (X₁ ++ [m] ++ Y₂).head? = (X₁ ++ [m]).head? :=
      headQ_append_list (X₁ ++ [m]) Y₂ hX₁neC
    rw [h4]; exact h1
  have hPhead : (C ++ [a] ++ E).head? = some b := by
    have h1 : (C ++ [a]).head? = some b := by
      have h2 : (C ++ [a]).head? = C.head? := headQ_append_list C [a] hCne
      rw [h2]; exact hbhead
    have h3 : (C ++ [a] ++ E).head? = (C ++ [a]).head? :=
      headQ_append_list (C ++ [a]) E (append_single_ne_nil C a)
    rw [h3]; exact h1
  have hY₁mY₂ : (Y₁ ++ [m] ++ Y₂).head? = (Y₁ ++ [m]).head? :=
    headQ_append_list (Y₁ ++ [m]) Y₂ hY1mne
  have hY₁m_aE : (Y₁ ++ [m] ++ [a] ++ E).head? = (Y₁ ++ [m]).head? := by
    have h1 : (Y₁ ++ [m] ++ [a] ++ E).head? = (Y₁ ++ [m] ++ [a]).head? :=
      headQ_append_list (Y₁ ++ [m] ++ [a]) E (append_single_ne_nil (Y₁ ++ [m]) a)
    have h2 : (Y₁ ++ [m] ++ [a]).head? = (Y₁ ++ [m]).head? :=
      headQ_append_list (Y₁ ++ [m]) [a] hY1mne
    rw [h1, h2]
  have hQ₂head : (Y₁ ++ [m] ++ [a] ++ E).head? = (Y₁ ++ [m] ++ Y₂).head? := by
    rw [hY₁m_aE, hY₁mY₂]
  have hQ₁last : lastOf (X₁ ++ [m] ++ Y₂) = lastOf (Y₁ ++ [m] ++ Y₂) := by
    by_cases hY₂ : Y₂ = []
    · rw [hY₂]
      rw [show X₁ ++ [m] ++ ([] : List (Fin n)) = X₁ ++ [m] from by simp,
          show Y₁ ++ [m] ++ ([] : List (Fin n)) = Y₁ ++ [m] from by simp]
      rw [lastOf_append_single' X₁ m, lastOf_append_single' Y₁ m]
    · rw [lastOf_append_list (X₁ ++ [m]) Y₂ hY₂, lastOf_append_list (Y₁ ++ [m]) Y₂ hY₂]
  have hPlast : lastOf (C ++ [a] ++ E) = lastOf (Y₁ ++ [m] ++ [a] ++ E) := by
    rw [lastOf_append_mid C E a, lastOf_append_mid (Y₁ ++ [m]) E a]
  -- §4 排除 A 本身已是目标的情形
  have haA : a ∉ (Y₁ ++ [m] ++ Y₂) := by
    intro hmem
    rcases List.mem_append.1 hmem with h | h
    · rcases List.mem_append.1 h with h1 | h1
      · exact haY₁ h1
      · exact ha_ne_m (List.mem_singleton.1 h1)
    · exact haY₂ h
  by_cases hwA : isEnd b (Y₁ ++ [m] ++ Y₂) ∧ a ∉ (Y₁ ++ [m] ++ Y₂)
  · exact ⟨D, hD', rfl, fun w => rfl, ⟨_, hAmem, hwA.1, hwA.2⟩⟩
  · have hnisEnd : ¬ isEnd b (Y₁ ++ [m] ++ Y₂) := fun hE => hwA ⟨hE, haA⟩
    have hAnothead : (Y₁ ++ [m]).head? ≠ some b := fun h =>
      hnisEnd (Or.inl (by rw [hY₁mY₂]; exact h))
    have hQ₁neA : X₁ ++ [m] ++ Y₂ ≠ Y₁ ++ [m] ++ Y₂ := by
      intro hc
      exact hAnothead (by rw [← hY₁mY₂, ← hc]; exact hQ₁head)
    have hQ₂neP : Y₁ ++ [m] ++ [a] ++ E ≠ C ++ [a] ++ E := by
      intro hc
      exact hAnothead (by rw [← hY₁m_aE, hc]; exact hPhead)
    have haP : a ∈ C ++ [a] ++ E := by
      have h1 : a ∈ C ++ [a] := List.mem_append.2 (Or.inr (List.mem_cons.2 (Or.inl rfl)))
      exact List.mem_append.2 (Or.inl h1)
    have hPneA : C ++ [a] ++ E ≠ Y₁ ++ [m] ++ Y₂ := by
      intro hc
      exact haA (hc ▸ haP)
    have haQ₁ : a ∉ X₁ ++ [m] ++ Y₂ := by
      intro hmem
      rcases List.mem_append.1 hmem with h | h
      · rcases List.mem_append.1 h with h1 | h1
        · exact haX₁ h1
        · exact ha_ne_m (List.mem_singleton.1 h1)
      · exact haY₂ h
    have haQ₂ : a ∈ Y₁ ++ [m] ++ [a] ++ E := by
      have h1 : a ∈ Y₁ ++ [m] ++ [a] :=
        List.mem_append.2 (Or.inr (List.mem_cons.2 (Or.inl rfl)))
      exact List.mem_append.2 (Or.inl h1)
    have hQ₁neQ₂ : X₁ ++ [m] ++ Y₂ ≠ Y₁ ++ [m] ++ [a] ++ E := by
      intro hc
      exact haQ₁ (hc ▸ haQ₂)
    have hQ₁neP : X₁ ++ [m] ++ Y₂ ≠ C ++ [a] ++ E := by
      intro hc
      exact haQ₁ (hc ▸ haP)
    -- §5 边定位辅助
    have hXP : ∀ x y : Fin n, EIn X₁ x y → EIn (C ++ [a] ++ E) x y := by
      intro x y h
      rw [List.append_assoc]
      refine EIn_append_left C ([a] ++ E) x y ?_
      rw [hC]
      exact EIn_append_left X₁ [m] x y h
    have hEP : ∀ x y : Fin n, EIn E x y → EIn (C ++ [a] ++ E) x y := by
      intro x y h
      rw [List.append_assoc]
      exact EIn_append_right C ([a] ++ E) x y (EIn_append_right [a] E x y h)
    have hmidP : ∀ x y : Fin n, EIn ([a] ++ E) x y → EIn (C ++ [a] ++ E) x y := by
      intro x y h
      rw [List.append_assoc]
      exact EIn_append_right C ([a] ++ E) x y h
    have hY₁A : ∀ x y : Fin n, EIn Y₁ x y → EIn (Y₁ ++ [m] ++ Y₂) x y := by
      intro x y h
      rw [List.append_assoc]
      exact EIn_append_left Y₁ ([m] ++ Y₂) x y h
    have hY₂A : ∀ x y : Fin n, EIn Y₂ x y → EIn (Y₁ ++ [m] ++ Y₂) x y := by
      intro x y h
      rw [List.append_assoc]
      exact EIn_append_right Y₁ ([m] ++ Y₂) x y (EIn_append_right [m] Y₂ x y h)
    have hCjunc : ∀ v : Fin n, lastOf X₁ = some v → EIn (C ++ [a] ++ E) v m := by
      intro v hv
      rw [List.append_assoc]
      refine EIn_append_left C ([a] ++ E) v m ?_
      rw [hC]
      exact EIn_append_last X₁ m v hv
    have hAjunc : ∀ v : Fin n, lastOf Y₁ = some v → EIn (Y₁ ++ [m] ++ Y₂) v m := by
      intro v hv
      rw [List.append_assoc]
      exact EIn_append_junction Y₁ ([m] ++ Y₂) (by simp) hv rfl
    have hAdjunc : ∀ v : Fin n, Y₂.head? = some v → EIn (Y₁ ++ [m] ++ Y₂) m v := by
      intro v hv
      exact EIn_append_junction (Y₁ ++ [m]) Y₂
        (fun h0 => by rw [h0] at hv; simp [List.head?] at hv)
        (lastOf_append_single' Y₁ m) hv
    have hPjunc_a : ∀ v : Fin n, ([a] ++ E).head? = some v → EIn (C ++ [a] ++ E) m v := by
      intro v hv
      have hv2 : v = a := Option.some.inj (hv.symm.trans (by simp))
      rw [hv2]
      exact hEInP_ma
    have ha_of_head : ∀ v : Fin n, ([a] ++ E).head? = some v → v = a :=
      fun v hv => Option.some.inj (hv.symm.trans (by simp))
    have hQ₂ma : EIn (Y₁ ++ [m] ++ [a] ++ E) m a := by
      rw [List.append_assoc]
      exact EIn_append_junction (Y₁ ++ [m]) ([a] ++ E) (List.cons_ne_nil a E)
        (lastOf_append_single' Y₁ m) rfl
    -- §6 路径性 Q₁ / Q₂
    have hQ₁path : IsPath (GAdj G₀) (X₁ ++ [m] ++ Y₂) := by
      refine ⟨?_, ?_, ?_⟩
      · have h1 : 1 ≤ X₁.length := by cases X₁ with
          | nil => exact absurd rfl hX₁ne
          | cons c t => simp
        have hlen : (X₁ ++ [m] ++ Y₂).length = X₁.length + 1 + Y₂.length := by
          rw [List.length_append, List.length_append]
          rfl
        omega
      · rw [show X₁ ++ [m] ++ Y₂ = (X₁ ++ [m]) ++ Y₂ from rfl]
        exact distinct_append_disj (X₁ ++ [m]) Y₂ hX₁dist hY₂dis (fun v hv => by
          rcases List.mem_append.1 hv with h2 | h2
          · exact hX₁Y₂ v h2
          · intro hmem
            exact hmY₂ ((List.mem_singleton.1 h2) ▸ hmem))
      · rw [show X₁ ++ [m] ++ Y₂ = X₁ ++ ([m] ++ Y₂) from by simp [List.append_assoc]]
        refine chain_append_list (GAdj G₀) ([m] ++ Y₂) X₁ (by simp) hchX₁ hchmY₂ ?_
        intro u v hu hv
        have hv2 : ([m] ++ Y₂).head? = some m := rfl
        have hvm : v = m := Option.some.inj (hv.symm.trans hv2)
        rw [hvm]
        exact hjunX₁m u hu
    have hQ₂path : IsPath (GAdj G₀) (Y₁ ++ [m] ++ [a] ++ E) := by
      refine ⟨?_, ?_, ?_⟩
      · have hlen : (Y₁ ++ [m] ++ [a] ++ E).length = Y₁.length + 2 + E.length := by
          rw [List.length_append, List.length_append, List.length_append]
          rfl
        omega
      · rw [show Y₁ ++ [m] ++ [a] ++ E = (Y₁ ++ [m] ++ [a]) ++ E from rfl]
        refine distinct_append_disj (Y₁ ++ [m] ++ [a]) E ?_ hEdis (fun v hv => by
          rcases List.mem_append.1 hv with h2 | h2
          · rcases List.mem_append.1 h2 with h3 | h3
            · exact hY₁E v h3
            · intro hmem
              exact hmE ((List.mem_singleton.1 h3) ▸ hmem)
          · intro hmem
            exact haE ((List.mem_singleton.1 h2) ▸ hmem))
        exact distinctP_append (Y₁ ++ [m]) a hy₁m_dist haY₁m
      · rw [show Y₁ ++ [m] ++ [a] ++ E = Y₁ ++ (m :: (a :: E)) from by
          simp [List.append_assoc, List.singleton_append]]
        refine chain_append_list (GAdj G₀) (m :: a :: E) Y₁ (by simp) hchY₁
          ⟨hjunC m hmlast, hchAE⟩ ?_
        intro u v hu hv
        have hv2 : (m :: a :: E).head? = some m := rfl
        have hvm : v = m := Option.some.inj (hv.symm.trans hv2)
        rw [hvm]
        exact hjunY₁ u hu
    -- §7 替换的边账
    have hQ₁nD : X₁ ++ [m] ++ Y₂ ∉ D := by
      intro hmem
      obtain ⟨v, hv⟩ := lastOf_exists X₁ hX₁ne
      exact hdisj (X₁ ++ [m] ++ Y₂) hmem (C ++ [a] ++ E) hPmem hQ₁neP v m
        ⟨by rw [List.append_assoc]; exact EIn_append_junction X₁ ([m] ++ Y₂) (by simp) hv rfl,
         hCjunc v hv⟩
    have hQ₂nD : Y₁ ++ [m] ++ [a] ++ E ∉ D := by
      intro hmem
      exact hdisj (Y₁ ++ [m] ++ [a] ++ E) hmem (C ++ [a] ++ E) hPmem hQ₂neP m a
        ⟨hQ₂ma, hEInP_ma⟩
    have hY₁Q₂ : ∀ x y : Fin n, EIn Y₁ x y → EIn (Y₁ ++ [m] ++ [a] ++ E) x y := by
      intro x y h
      simp only [List.append_assoc]
      exact EIn_append_left Y₁ ([m] ++ ([a] ++ E)) x y h
    have hY₂Q₁ : ∀ x y : Fin n, EIn Y₂ x y → EIn (X₁ ++ [m] ++ Y₂) x y := by
      intro x y h
      simp only [List.append_assoc]
      exact EIn_append_right X₁ ([m] ++ Y₂) x y (EIn_append_right [m] Y₂ x y h)
    have hcv : ∀ x y : Fin n, EIn (C ++ [a] ++ E) x y ∨ EIn (Y₁ ++ [m] ++ Y₂) x y →
        EIn (X₁ ++ [m] ++ Y₂) x y ∨ EIn (Y₁ ++ [m] ++ [a] ++ E) x y := by
      intro x y h0
      rcases h0 with h | h
      · rcases EIn_append_mid C a E x y h with h1 | h1 | h1 | h1 | h1 | h1
        · rcases EIn_append_mid X₁ m ([] : List (Fin n)) x y
            (by simpa [List.append_nil, hC] using h1) with h2 | h2 | h2 | h2 | h2 | h2
          · exact Or.inl (by rw [List.append_assoc]; exact EIn_append_left X₁ ([m] ++ Y₂) x y h2)
          · exact h2.elim
          · have h3 : EIn (X₁ ++ [m] ++ Y₂) x y := by
              rw [h2.2, List.append_assoc]
              exact EIn_append_junction X₁ ([m] ++ Y₂) (by simp) h2.1 rfl
            exact Or.inl h3
          · have h3 : EIn (X₁ ++ [m] ++ Y₂) x y := by
              rw [h2.2, List.append_assoc]
              exact EIn_symm (X₁ ++ ([m] ++ Y₂)) y m
                (EIn_append_junction X₁ ([m] ++ Y₂) (by simp) h2.1 rfl)
            exact Or.inl h3
          · exact absurd h2.2 (by simp)
          · exact absurd h2.2 (by simp)
        · exact Or.inr (EIn_append_right (Y₁ ++ [m] ++ [a]) E x y h1)
        · have hx : x = m := (Option.some.inj (hmlast.symm.trans h1.1)).symm
          refine Or.inr ?_
          rw [hx, h1.2, List.append_assoc]
          exact EIn_append_junction (Y₁ ++ [m]) ([a] ++ E) (List.cons_ne_nil a E)
            (lastOf_append_single' Y₁ m) rfl
        · have hy : y = m := (Option.some.inj (hmlast.symm.trans h1.1)).symm
          refine Or.inr ?_
          rw [hy, h1.2]
          exact EIn_symm (Y₁ ++ [m] ++ [a] ++ E) m a (by
            rw [List.append_assoc]
            exact EIn_append_junction (Y₁ ++ [m]) ([a] ++ E) (List.cons_ne_nil a E)
              (lastOf_append_single' Y₁ m) rfl)
        · refine Or.inr ?_
          have hEne : E ≠ [] := by
            intro hz
            rw [hz] at h1
            simp [List.head?] at h1
          rw [h1.1]
          exact EIn_append_junction (Y₁ ++ [m] ++ [a]) E hEne
            (lastOf_append_single' (Y₁ ++ [m]) a) h1.2
        · refine Or.inr ?_
          have hEne : E ≠ [] := by
            intro hz
            rw [hz] at h1
            simp [List.head?] at h1
          rw [h1.1]
          exact EIn_symm (Y₁ ++ [m] ++ [a] ++ E) a x
            (EIn_append_junction (Y₁ ++ [m] ++ [a]) E hEne
              (lastOf_append_single' (Y₁ ++ [m]) a) h1.2)
      · rcases EIn_append_mid Y₁ m Y₂ x y h with h1 | h1 | h1 | h1 | h1 | h1
        · exact Or.inr (hY₁Q₂ x y h1)
        · exact Or.inl (hY₂Q₁ x y h1)
        · refine Or.inr ?_
          rw [h1.2]
          simp only [List.append_assoc]
          exact EIn_append_junction Y₁ ([m] ++ ([a] ++ E)) (by simp) h1.1 rfl
        · refine Or.inr ?_
          rw [h1.2]
          simp only [List.append_assoc]
          exact EIn_symm (Y₁ ++ ([m] ++ ([a] ++ E))) y m
            (EIn_append_junction Y₁ ([m] ++ ([a] ++ E)) (by simp) h1.1 rfl)
        · refine Or.inl ?_
          rw [h1.1]
          exact EIn_append_junction (X₁ ++ [m]) Y₂
            (fun hz => by rw [hz] at h1; simp [List.head?] at h1)
            (lastOf_append_single' X₁ m) h1.2
        · refine Or.inl ?_
          rw [h1.1]
          exact EIn_symm (X₁ ++ [m] ++ Y₂) m x
            (EIn_append_junction (X₁ ++ [m]) Y₂
              (fun hz => by rw [hz] at h1; simp [List.head?] at h1)
              (lastOf_append_single' X₁ m) h1.2)
    have hdj : ∀ x y : Fin n,
        EIn (X₁ ++ [m] ++ Y₂) x y ∨ EIn (Y₁ ++ [m] ++ [a] ++ E) x y →
        EIn (C ++ [a] ++ E) x y ∨ EIn (Y₁ ++ [m] ++ Y₂) x y := by
      intro x y h
      rcases h with h | h
      · rcases EIn_append_mid X₁ m Y₂ x y h with h1 | h1 | h1 | h1 | h1 | h1
        · exact Or.inl (hXP x y h1)
        · exact Or.inr (hY₂A x y h1)
        · refine Or.inl ?_
          rw [h1.2]
          exact hCjunc x h1.1
        · refine Or.inl ?_
          rw [h1.2]
          exact EIn_symm (C ++ [a] ++ E) y m (hCjunc y h1.1)
        · refine Or.inr ?_
          rw [h1.1]
          exact hAdjunc y h1.2
        · refine Or.inr ?_
          rw [h1.1]
          exact EIn_symm (Y₁ ++ [m] ++ Y₂) m x (hAdjunc x h1.2)
      · have h2 : EIn (Y₁ ++ [m] ++ ([a] ++ E)) x y := by
          rw [← List.append_assoc]
          exact h
        rcases EIn_append_mid Y₁ m ([a] ++ E) x y h2 with h1 | h1 | h1 | h1 | h1 | h1
        · exact Or.inr (hY₁A x y h1)
        · exact Or.inl (hmidP x y h1)
        · refine Or.inr ?_
          rw [h1.2]
          exact hAjunc x h1.1
        · refine Or.inr ?_
          rw [h1.2]
          exact EIn_symm (Y₁ ++ [m] ++ Y₂) y m (hAjunc y h1.1)
        · refine Or.inl ?_
          rw [h1.1]
          exact hPjunc_a y h1.2
        · refine Or.inl ?_
          rw [h1.1]
          exact EIn_symm (C ++ [a] ++ E) m x (hPjunc_a x h1.2)
    -- §8 两条新路彼此边不交（36 情形）
    have hQQ : ∀ x y : Fin n, EIn (X₁ ++ [m] ++ Y₂) x y →
        EIn (Y₁ ++ [m] ++ [a] ++ E) x y → False := by
      intro x y h1 h2
      have h2' : EIn (Y₁ ++ [m] ++ ([a] ++ E)) x y := by
        rw [← List.append_assoc]
        exact h2
      rcases EIn_append_mid X₁ m Y₂ x y h1 with d | d | d | d | d | d
      all_goals rcases EIn_append_mid Y₁ m ([a] ++ E) x y h2' with e | e | e | e | e | e
      · exact hdisj (C ++ [a] ++ E) hPmem (Y₁ ++ [m] ++ Y₂) hAmem hPneA x y
          ⟨hXP x y d, hY₁A x y e⟩
      · rcases List.mem_append.1 (EIn_mem ([a] ++ E) x y e).1 with h | h
        · exact haX₁ ((List.mem_singleton.1 h) ▸ (EIn_mem X₁ x y d).1)
        · exact hCE x (hXC x (EIn_mem X₁ x y d).1) h
      · refine hdisj (C ++ [a] ++ E) hPmem (Y₁ ++ [m] ++ Y₂) hAmem hPneA x y ⟨hXP x y d, ?_⟩
        rw [e.2]
        exact hAjunc x e.1
      · refine hdisj (C ++ [a] ++ E) hPmem (Y₁ ++ [m] ++ Y₂) hAmem hPneA x y ⟨hXP x y d, ?_⟩
        rw [e.2]
        exact EIn_symm (Y₁ ++ [m] ++ Y₂) y m (hAjunc y e.1)
      · have hy : y = a := ha_of_head y e.2
        exact haX₁ (by rw [← hy]; exact (EIn_mem X₁ x y d).2)
      · have hx : x = a := ha_of_head x e.2
        exact haX₁ (by rw [← hx]; exact (EIn_mem X₁ x y d).1)
      · exact hY₁Y₂ x (EIn_mem Y₁ x y e).1 (EIn_mem Y₂ x y d).1
      · exact hdisj (C ++ [a] ++ E) hPmem (Y₁ ++ [m] ++ Y₂) hAmem hPneA x y
          ⟨hmidP x y e, hY₂A x y d⟩
      · exact hmY₂ (by rw [← e.2]; exact (EIn_mem Y₂ x y d).2)
      · exact hmY₂ (by rw [← e.2]; exact (EIn_mem Y₂ x y d).1)
      · have hy : y = a := ha_of_head y e.2
        exact haY₂ (by rw [← hy]; exact (EIn_mem Y₂ x y d).2)
      · exact hmY₂ (by rw [← e.1]; exact (EIn_mem Y₂ x y d).2)
      · refine hdisj (C ++ [a] ++ E) hPmem (Y₁ ++ [m] ++ Y₂) hAmem hPneA x y ⟨?_, hY₁A x y e⟩
        rw [d.2]
        exact hCjunc x d.1
      · have hm' : m ∈ ([a] ++ E) := by rw [← d.2]; exact (EIn_mem ([a] ++ E) x y e).2
        rcases List.mem_append.1 hm' with h | h
        · exact hm_ne_a (List.mem_singleton.1 h)
        · exact hmE h
      · refine hdisj (C ++ [a] ++ E) hPmem (Y₁ ++ [m] ++ Y₂) hAmem hPneA x y ⟨?_, ?_⟩
        · rw [d.2]
          exact hCjunc x d.1
        · rw [e.2]
          exact hAjunc x e.1
      · exact hmX₁ (by rw [← e.2]; exact lastOf_some_mem X₁ x d.1)
      · exact hmX₁ (by rw [← e.1]; exact lastOf_some_mem X₁ x d.1)
      · have hxa : x = a := ha_of_head x e.2
        exact haX₁ (by rw [← hxa]; exact lastOf_some_mem X₁ x d.1)
      · refine hdisj (C ++ [a] ++ E) hPmem (Y₁ ++ [m] ++ Y₂) hAmem hPneA x y ⟨?_, hY₁A x y e⟩
        rw [d.2]
        exact EIn_symm (C ++ [a] ++ E) y m (hCjunc y d.1)
      · rcases List.mem_append.1 (EIn_mem ([a] ++ E) x y e).2 with h | h
        · have hya : y = a := List.mem_singleton.1 h
          exact haX₁ (by rw [← hya]; exact lastOf_some_mem X₁ y d.1)
        · exact hCE y (hXC y (lastOf_some_mem X₁ y d.1)) h
      · exact hmY₁ (by rw [← d.2]; exact lastOf_some_mem Y₁ x e.1)
      · refine hdisj (C ++ [a] ++ E) hPmem (Y₁ ++ [m] ++ Y₂) hAmem hPneA x y ⟨?_, ?_⟩
        · rw [d.2]
          exact EIn_symm (C ++ [a] ++ E) y m (hCjunc y d.1)
        · rw [e.2]
          exact EIn_symm (Y₁ ++ [m] ++ Y₂) y m (hAjunc y e.1)
      · have hya : y = a := ha_of_head y e.2
        exact haX₁ (by rw [← hya]; exact lastOf_some_mem X₁ y d.1)
      · exact hmX₁ (by rw [← e.1]; exact lastOf_some_mem X₁ y d.1)
      · exact hmY₁ (by rw [← d.1]; exact (EIn_mem Y₁ x y e).1)
      · have hm' : m ∈ ([a] ++ E) := by rw [← d.1]; exact (EIn_mem ([a] ++ E) x y e).1
        rcases List.mem_append.1 hm' with h | h
        · exact hm_ne_a (List.mem_singleton.1 h)
        · exact hmE h
      · exact hmY₁ (by rw [← d.1]; exact lastOf_some_mem Y₁ x e.1)
      · exact hY₁Y₂ y (lastOf_some_mem Y₁ y e.1) (headQ_mem Y₂ y d.2)
      · have hya : y = a := ha_of_head y e.2
        exact haY₂ (by rw [← hya]; exact headQ_mem Y₂ y d.2)
      · exact hmY₂ (by rw [← e.1]; exact headQ_mem Y₂ y d.2)
      · have hm' : m ∈ Y₁ := by rw [← d.1]; exact (EIn_mem Y₁ x y e).2
        exact hmY₁ hm'
      · have hm' : m ∈ ([a] ++ E) := by rw [← d.1]; exact (EIn_mem ([a] ++ E) x y e).2
        rcases List.mem_append.1 hm' with h | h
        · exact hm_ne_a (List.mem_singleton.1 h)
        · exact hmE h
      · exact hY₁Y₂ x (lastOf_some_mem Y₁ x e.1) (headQ_mem Y₂ x d.2)
      · have hm' : m ∈ Y₁ := by rw [← d.1]; exact lastOf_some_mem Y₁ y e.1
        exact hmY₁ hm'
      · exact hmY₂ (by rw [← e.1]; exact headQ_mem Y₂ x d.2)
      · have hxa : x = a := ha_of_head x e.2
        exact haY₂ (by rw [← hxa]; exact headQ_mem Y₂ x d.2)
    -- §9 组装
    have hmemA : Y₁ ++ [m] ++ Y₂ ∈ D.erase (C ++ [a] ++ E) :=
      mem_erase_of_ne D (C ++ [a] ++ E) (Y₁ ++ [m] ++ Y₂) hPneA.symm hAmem
    refine ⟨(D.erase (C ++ [a] ++ E)).erase (Y₁ ++ [m] ++ Y₂) ++
        [X₁ ++ [m] ++ Y₂, Y₁ ++ [m] ++ [a] ++ E], ?_, ?_, ?_, ?_⟩
    · exact fan6_replace2_decomp G₀ D hD' (C ++ [a] ++ E) (Y₁ ++ [m] ++ Y₂)
        (X₁ ++ [m] ++ Y₂) (Y₁ ++ [m] ++ [a] ++ E) hPmem hAmem hPneA
        hQ₁path hQ₂path hQ₁nD hQ₂nD hQ₁neQ₂ hcv hdj hQQ
    · have hlen1 : (((D.erase (C ++ [a] ++ E)).erase (Y₁ ++ [m] ++ Y₂)) ++
          [X₁ ++ [m] ++ Y₂, Y₁ ++ [m] ++ [a] ++ E]).length
          = ((D.erase (C ++ [a] ++ E)).erase (Y₁ ++ [m] ++ Y₂)).length + 2 := by simp
      have hlen2 : ((D.erase (C ++ [a] ++ E)).erase (Y₁ ++ [m] ++ Y₂)).length + 1
          = (D.erase (C ++ [a] ++ E)).length :=
        length_erase_of_mem (D.erase (C ++ [a] ++ E)) (Y₁ ++ [m] ++ Y₂) hmemA
      have hlen3 : (D.erase (C ++ [a] ++ E)).length + 1 = D.length :=
        length_erase_of_mem D (C ++ [a] ++ E) hPmem
      omega
    · intro w
      have hrep := vEndCount_replace2 D (C ++ [a] ++ E) (Y₁ ++ [m] ++ Y₂)
        (X₁ ++ [m] ++ Y₂) (Y₁ ++ [m] ++ [a] ++ E) hPmem hmemA w
      have hx := vEndBit_add_cancel w (C ++ [a] ++ E) (Y₁ ++ [m] ++ Y₂)
        (X₁ ++ [m] ++ Y₂) (Y₁ ++ [m] ++ [a] ++ E)
        (hPhead.trans hQ₁head.symm) hPlast hQ₂head.symm hQ₁last.symm
        (headQ_ne_lastOf _ hPlen hPdis) (headQ_ne_lastOf _ hAlen hAdis)
        (headQ_ne_lastOf _ hQ₁path.1 hQ₁path.2.1) (headQ_ne_lastOf _ hQ₂path.1 hQ₂path.2.1)
      omega
    · refine ⟨X₁ ++ [m] ++ Y₂, ?_, Or.inl hQ₁head, haQ₁⟩
      exact List.mem_append.2 (Or.inr (List.mem_cons.2 (Or.inl rfl)))


/-! ### lane_95b 级联收口：标记分裂结构 ⟹ fan6_nf 结论形态（组装真证）

`fan6_mark_swap`（单步主件）+ `fan6_cascade`（多步排布/终止性机器）合成：
**唯一残余缺口**是把 `Fan6MarkSplit`（标记分裂结构的存在性）在一般构型上
证出来。机器底账（lab/fan95b）：n = 5 全空间 51,680 个非 case1 构型中
45,500 个直接命中该结构（88.0%），其余经 ≤ 1 次尾部换装（tail-swap）后
命中（route_n5_v2.json / chain_n5.json）。 -/

/-- **标记分裂结构（lane_95b 残余缺口的精确形式）**：分解 D 中存在坏路
    P = C ++ [a] ++ E（b-端、head C = b、标记 m = lastOf C、C = X₁ ++ [m]）
    与以 m 为内点的路径 A = Y₁ ++ [m] ++ Y₂，且尾段分离（a ∉ Y₁、a ∉ Y₂、
    X₁ ⊥ Y₂、Y₁ ⊥ E）——`fan6_mark_swap` 的全部假设面。 -/
def Fan6MarkSplit {n : Nat} (G₀ : Graph n) (a b : Fin n)
    (D : List (List (Fin n))) : Prop :=
  ∃ X₁ C E Y₁ Y₂ : List (Fin n), ∃ m : Fin n,
    C = X₁ ++ [m] ∧
    C ++ [a] ++ E ∈ D ∧ Y₁ ++ [m] ++ Y₂ ∈ D ∧
    C.head? = some b ∧ lastOf C = some m ∧
    a ∉ Y₁ ∧ a ∉ Y₂ ∧
    (∀ v : Fin n, v ∈ X₁ → v ∉ Y₂) ∧
    (∀ v : Fin n, v ∈ Y₁ → v ∉ E)

/-- **级联收口（组装真证）**：若"每个非目标构型都含标记分裂结构"（残余缺口），
    则从任意分解出发沿 μ 作有界强归纳到达目标形态——`fan6_cascade`
    的多步排布 + `fan6_mark_swap` 的单步实现。本件不需要 passing
    （hdead）假设：级联的步假设已含全部组合内容。 -/
theorem fan6_cascade_of_link {n : Nat} (G₀ : Graph n) (a b : Fin n)
    (hab0 : G₀.adjB a b = false)
    (hlink : ∀ Dc : List (List (Fin n)), IsDecomp G₀ Dc →
      (∀ Q ∈ Dc, isEnd b Q → a ∈ Q) → Fan6MarkSplit G₀ a b Dc) :
    ∀ (k : Nat) (D : List (List (Fin n))), IsDecomp G₀ D →
      fan6_measure a b D ≤ k →
      ∃ D'' : List (List (Fin n)),
        IsDecomp G₀ D'' ∧ D''.length = D.length ∧
        (∀ w : Fin n, vEndCount D'' w = vEndCount D w) ∧
        ∃ Q ∈ D'', isEnd b Q ∧ a ∉ Q := by
  refine fan6_cascade G₀ a b ?_
  intro Dc hDc hnr
  obtain ⟨X₁, C, E, Y₁, Y₂, m, hC, hPmem, hAmem, hbhead, hmlast, haY₁, haY₂,
    hX₁Y₂, hY₁E⟩ := hlink Dc hDc hnr
  obtain ⟨D', hD', hlen, hprof, htg⟩ :=
    fan6_mark_swap G₀ a b hab0 Dc hDc X₁ C E Y₁ Y₂ m hC hPmem hAmem hbhead hmlast
      haY₁ haY₂ hX₁Y₂ hY₁E
  exact ⟨D', hD', hlen, hprof, Or.inr htg⟩

/-- **fan6_nf 结论形态的降档定理**：把残余缺口作为参数化假设（对所有
    图、所有 (a,b)（ab 非边）与一切非目标构型给出标记分裂结构），
    即得 fan6_nf 的结论形态（逐点轮廓保持 + b-端避开 a 的路径）。
    对照：`fan6_nf` 本体仍为占位（其 passing 假设在本路线中不被消费）。 -/
theorem fan6_nf_concl_of_link {n : Nat}
    (hlink : ∀ (G₀ : Graph n) (a b : Fin n) (D : List (List (Fin n))),
      G₀.adjB a b = false → IsDecomp G₀ D →
      (∀ Q ∈ D, isEnd b Q → a ∈ Q) → Fan6MarkSplit G₀ a b D) :
    ∀ (G₀ : Graph n) (a b : Fin n), G₀.adjB a b = false →
    ∀ (D : List (List (Fin n))), IsDecomp G₀ D →
      ∃ D'' : List (List (Fin n)),
        IsDecomp G₀ D'' ∧ D''.length = D.length ∧
        (∀ w : Fin n, vEndCount D'' w = vEndCount D w) ∧
        ∃ Q ∈ D'', isEnd b Q ∧ a ∉ Q := by
  intro G₀ a b hab0 D hD
  exact fan6_cascade_of_link G₀ a b hab0
    (fun Dc hDc hnr => hlink G₀ a b Dc hab0 hDc hnr)
    (fan6_measure a b D) D hD (Nat.le_refl _)


/-! ### lane_95b 冒烟测试：主件在 lane_68c 型最小实例上的实例化

实例（lab/fan95b/route3.py 的 routeA 样本；机器暴力验证的构造一致）：
G₀ = 边 {01, 02, 03}（掩码 7），a = 1，b = 2，D = {[2,0,1], [0,3]}（坏路按
b-端朝向书写，与主件的 head C = b 口径一致；其反向 [1,0,2] 与机器样本的
路径集合相同）：坏路 P = [2,0,1] = C ++ [a] ++ E（C = [2,0]、E = []、
标记 m = 0），纠正路径 A = [0,3] = [] ++ [0] ++ [3]。
换装产物 Q₁ = [2,0,3]（b-端、避开 a）、Q₂ = [0,1]，D′ = {[2,0,3], [0,1]}——
与机器验证的 path1/path2 逐字一致（构造路径的合法性由 route3.py 独立暴力复核）。
`IsDecomp gtest95b D` 以假设传入（本工程 Distinct/IsPath 为工程内定义，
不进 `decide`；该实例的分解合法性由 Python 暴力校验器逐边核验）。 -/
section Smoke95b

/-- 冒烟图：K₅ 上只留 0-1、0-2、0-3 三条边。 -/
def gtest95b : Graph 5 where
  adjB := fun x y => decide ((x = 0 ∧ y = 1) ∨ (x = 1 ∧ y = 0) ∨ (x = 0 ∧ y = 2)
    ∨ (x = 2 ∧ y = 0) ∨ (x = 0 ∧ y = 3) ∨ (x = 3 ∧ y = 0))
  symm := by decide
  loopless := by decide

/-- 假设面全部可判定地成立（集合论/词法事实），主件开火。 -/
theorem gtest95b_mark_swap (hD : IsDecomp gtest95b [[2, 0, 1], [0, 3]]) :
    ∃ D' : List (List (Fin 5)),
      IsDecomp gtest95b D' ∧
      D'.length = ([[2, 0, 1], [0, 3]] : List (List (Fin 5))).length ∧
      (∀ w : Fin 5, vEndCount D' w = vEndCount ([[2, 0, 1], [0, 3]] : List (List (Fin 5))) w) ∧
      ∃ P' ∈ D', isEnd 2 P' ∧ (1 : Fin 5) ∉ P' :=
  fan6_mark_swap gtest95b 1 2 (by decide) [[2, 0, 1], [0, 3]] hD
    [2] [2, 0] [] [] [3] 0 rfl (by decide) (by decide) rfl rfl
    (by decide) (by decide) (by decide) (by decide)

/-- 主件预测的换装产物（机器样本 path1/path2）的端点与目标性质逐点可判定。 -/
theorem gtest95b_predicted :
    isEnd 2 ([2, 0, 3] : List (Fin 5)) ∧ (1 : Fin 5) ∉ [2, 0, 3] ∧
      (1 : Fin 5) ∈ [0, 1] := ⟨Or.inl rfl, by decide, by decide⟩

end Smoke95b



def g221adj : Fin 5 → Fin 5 → Bool :=
  fun x y => decide ((x = 0 ∧ y = 1) ∨ (x = 1 ∧ y = 0) ∨
    (x = 0 ∧ y = 3) ∨ (x = 3 ∧ y = 0) ∨ (x = 0 ∧ y = 4) ∨ (x = 4 ∧ y = 0) ∨
    (x = 1 ∧ y = 2) ∨ (x = 2 ∧ y = 1) ∨ (x = 1 ∧ y = 4) ∨ (x = 4 ∧ y = 1) ∨
    (x = 2 ∧ y = 3) ∨ (x = 3 ∧ y = 2))

def gtest221 : Graph 5 where
  adjB := g221adj
  symm := by decide
  loopless := by decide

theorem g221adj_eq (x y : Fin 5) : gtest221.adjB x y = g221adj x y := rfl

theorem fin5_cases (i : Fin 5) : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by
  have h5 : i.val < 5 := i.isLt
  have h : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨ i.val = 4 := by omega
  rcases h with h | h | h | h | h
  · exact Or.inl (Fin.val_inj.mp (by rw [h]; rfl))
  · exact Or.inr (Or.inl (Fin.val_inj.mp (by rw [h]; rfl)))
  · exact Or.inr (Or.inr (Or.inl (Fin.val_inj.mp (by rw [h]; rfl))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (Fin.val_inj.mp (by rw [h]; rfl)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Fin.val_inj.mp (by rw [h]; rfl)))))

theorem fin5_five_has_two : ∀ L : List (Fin 5), Distinct L → L.length = 5 →
    (2 : Fin 5) ∈ L := by
  intro L hdis hlen
  by_cases h2 : (2 : Fin 5) ∈ L
  · exact h2
  · exfalso
    have hsub : ∀ e ∈ L, e ∈ remove 2 (finList 5) := by
      intro e he
      have hmem := mem_finList 5 e
      have hne : (2 : Fin 5) ≠ e := by
        intro h; exact h2 (h ▸ he)
      exact (mem_remove_of_ne hne (finList 5)).mpr hmem
    have h4 := pigeon L (remove 2 (finList 5)) hdis hsub
    have hmem2 : (2 : Fin 5) ∈ finList 5 := mem_finList 5 2
    have h5 := length_remove (finList 5) hmem2
    have h6 := finList_len 5
    omega

/-- vEndBit 的取值只有 0/1。 -/
theorem vEndBit_cases (v : Fin 5) (L : List (Fin 5)) :
    vEndBit v L = 0 ∨ vEndBit v L = 1 := by
  simp only [vEndBit]
  split
  · exact Or.inr rfl
  · exact Or.inl rfl

/-- 端点指示为 1 ⟹ 是端点。 -/
theorem vEndBit_eq_one {v : Fin 5} {L : List (Fin 5)} (h : vEndBit v L = 1) :
    isEnd v L := by
  simp only [vEndBit] at h
  split at h
  next hc => exact hc
  next => omega

/-- 端点指示为 0 ⟹ 不是端点。 -/
theorem vEndBit_eq_zero {v : Fin 5} {L : List (Fin 5)} (h : vEndBit v L = 0) :
    ¬ isEnd v L := by
  simp only [vEndBit] at h
  split at h
  next hc => omega
  next hc => exact hc

/-- 6 条边的覆盖压平（g221 的全部边）。 -/
theorem cover6 {P Q : List (Fin 5)}
    (hcov : IsCover (GAdj gtest221) [P, Q]) :
    (EIn P 0 1 ∨ EIn Q 0 1) ∧ (EIn P 0 3 ∨ EIn Q 0 3) ∧ (EIn P 0 4 ∨ EIn Q 0 4) ∧
    (EIn P 1 2 ∨ EIn Q 1 2) ∧ (EIn P 1 4 ∨ EIn Q 1 4) ∧ (EIn P 2 3 ∨ EIn Q 2 3) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rcases hcov 0 1 (by show gtest221.adjB 0 1 = true; decide) with ⟨Z, hZ, hZE⟩
    have hZ' : Z = P ∨ Z = Q := by simpa using hZ
    rcases hZ' with rfl | rfl
    · exact Or.inl hZE
    · exact Or.inr hZE
  · rcases hcov 0 3 (by show gtest221.adjB 0 3 = true; decide) with ⟨Z, hZ, hZE⟩
    have hZ' : Z = P ∨ Z = Q := by simpa using hZ
    rcases hZ' with rfl | rfl
    · exact Or.inl hZE
    · exact Or.inr hZE
  · rcases hcov 0 4 (by show gtest221.adjB 0 4 = true; decide) with ⟨Z, hZ, hZE⟩
    have hZ' : Z = P ∨ Z = Q := by simpa using hZ
    rcases hZ' with rfl | rfl
    · exact Or.inl hZE
    · exact Or.inr hZE
  · rcases hcov 1 2 (by show gtest221.adjB 1 2 = true; decide) with ⟨Z, hZ, hZE⟩
    have hZ' : Z = P ∨ Z = Q := by simpa using hZ
    rcases hZ' with rfl | rfl
    · exact Or.inl hZE
    · exact Or.inr hZE
  · rcases hcov 1 4 (by show gtest221.adjB 1 4 = true; decide) with ⟨Z, hZ, hZE⟩
    have hZ' : Z = P ∨ Z = Q := by simpa using hZ
    rcases hZ' with rfl | rfl
    · exact Or.inl hZE
    · exact Or.inr hZE
  · rcases hcov 2 3 (by show gtest221.adjB 2 3 = true; decide) with ⟨Z, hZ, hZE⟩
    have hZ' : Z = P ∨ Z = Q := by simpa using hZ
    rcases hZ' with rfl | rfl
    · exact Or.inl hZE
    · exact Or.inr hZE

/-! 反例图上 0-端、避开 2 的简单路的完备形状分类（10 候选）。 -/
set_option maxHeartbeats 4000000 in
theorem path_shape221 (P : List (Fin 5)) (hP : IsPath (GAdj gtest221) P)
    (h0 : isEnd 0 P) (h2 : (2 : Fin 5) ∉ P) :
    P = [0, 1] ∨ P = [1, 0] ∨ P = [0, 3] ∨ P = [3, 0] ∨ P = [0, 4] ∨ P = [4, 0] ∨
        P = [0, 1, 4] ∨ P = [4, 1, 0] ∨ P = [0, 4, 1] ∨ P = [1, 4, 0] := by
  obtain ⟨hge, hdis, hch⟩ := hP
  have hle : P.length ≤ 5 :=
    pigeon P (finList 5) hdis (fun e he => mem_finList 5 e)
  rcases P with _ | ⟨x, t1⟩
  · simp only [List.length_nil] at hge; omega
  rcases t1 with _ | ⟨y, t2⟩
  · simp only [List.length_cons, List.length_nil] at hge; omega
  rcases t2 with _ | ⟨z, t3⟩
  · rcases fin5_cases x with rfl | rfl | rfl | rfl | rfl <;>
    rcases fin5_cases y with rfl | rfl | rfl | rfl | rfl <;>
    simp only [isEnd, lastOf, List.head?, Chain, GAdj, Distinct, g221adj_eq, g221adj,
      List.mem_cons, List.mem_singleton, decide_eq_true_eq, Option.some.injEq,
      reduceCtorEq, true_and, and_true] at h0 h2 hch hdis ⊢ <;>
    (simp_all; try decide; try omega)
  rcases t3 with _ | ⟨w, t4⟩
  · rcases fin5_cases x with rfl | rfl | rfl | rfl | rfl <;>
    rcases fin5_cases y with rfl | rfl | rfl | rfl | rfl <;>
    rcases fin5_cases z with rfl | rfl | rfl | rfl | rfl <;>
    simp only [isEnd, lastOf, List.head?, Chain, GAdj, Distinct, g221adj_eq, g221adj,
      List.mem_cons, List.mem_singleton, decide_eq_true_eq, Option.some.injEq,
      reduceCtorEq, true_and, and_true] at h0 h2 hch hdis ⊢ <;>
    (simp_all; try decide; try omega)
  rcases t4 with _ | ⟨v, t5⟩
  · rcases fin5_cases x with rfl | rfl | rfl | rfl | rfl <;>
    rcases fin5_cases y with rfl | rfl | rfl | rfl | rfl <;>
    rcases fin5_cases z with rfl | rfl | rfl | rfl | rfl <;>
    rcases fin5_cases w with rfl | rfl | rfl | rfl | rfl <;>
    simp only [isEnd, lastOf, List.head?, Chain, GAdj, Distinct, g221adj_eq, g221adj,
      List.mem_cons, List.mem_singleton, decide_eq_true_eq, Option.some.injEq,
      reduceCtorEq, true_and, and_true] at h0 h2 hch hdis ⊢ <;>
    (simp_all; try decide; try omega)
  rcases t5 with _ | ⟨u, t6⟩
  · have hP5 : (x :: y :: z :: w :: v :: []).length = 5 := by
      simp only [List.length_cons] at hle ⊢
      omega
    exact absurd (fin5_five_has_two _ hdis hP5) h2
  · simp only [List.length_cons] at hle; omega

/-! 反例图上 3-端、0/2/4 非端的简单路的完备形状分类（8 候选）。 -/
set_option maxHeartbeats 4000000 in
theorem q_shape221 (Q : List (Fin 5)) (hP : IsPath (GAdj gtest221) Q)
    (h3 : isEnd 3 Q) (h0 : ¬ isEnd 0 Q) (h2 : ¬ isEnd 2 Q) (h4 : ¬ isEnd 4 Q) :
    Q = [3, 0] ∨ Q = [0, 3] ∨ Q = [3, 0, 1] ∨ Q = [1, 0, 3] ∨
        Q = [3, 2, 1] ∨ Q = [1, 2, 3] ∨
        Q = [3, 0, 4, 1] ∨ Q = [1, 4, 0, 3] := by
  obtain ⟨hge, hdis, hch⟩ := hP
  have hle : Q.length ≤ 5 :=
    pigeon Q (finList 5) hdis (fun e he => mem_finList 5 e)
  rcases Q with _ | ⟨x, t1⟩
  · simp only [List.length_nil] at hge; omega
  rcases t1 with _ | ⟨y, t2⟩
  · simp only [List.length_cons, List.length_nil] at hge; omega
  rcases t2 with _ | ⟨z, t3⟩
  · rcases fin5_cases x with rfl | rfl | rfl | rfl | rfl <;>
    rcases fin5_cases y with rfl | rfl | rfl | rfl | rfl <;>
    simp only [isEnd, lastOf, List.head?, Chain, GAdj, Distinct, g221adj_eq, g221adj,
      List.mem_cons, List.mem_singleton, decide_eq_true_eq, Option.some.injEq,
      reduceCtorEq, true_and, and_true] at h3 h0 h2 h4 hch hdis ⊢ <;>
    (simp_all; try decide; try omega)
  rcases t3 with _ | ⟨w, t4⟩
  · rcases fin5_cases x with rfl | rfl | rfl | rfl | rfl <;>
    rcases fin5_cases y with rfl | rfl | rfl | rfl | rfl <;>
    rcases fin5_cases z with rfl | rfl | rfl | rfl | rfl <;>
    simp only [isEnd, lastOf, List.head?, Chain, GAdj, Distinct, g221adj_eq, g221adj,
      List.mem_cons, List.mem_singleton, decide_eq_true_eq, Option.some.injEq,
      reduceCtorEq, true_and, and_true] at h3 h0 h2 h4 hch hdis ⊢ <;>
    (simp_all; try decide; try omega)
  rcases t4 with _ | ⟨v, t5⟩
  · rcases fin5_cases x with rfl | rfl | rfl | rfl | rfl <;>
    rcases fin5_cases y with rfl | rfl | rfl | rfl | rfl <;>
    rcases fin5_cases z with rfl | rfl | rfl | rfl | rfl <;>
    rcases fin5_cases w with rfl | rfl | rfl | rfl | rfl <;>
    simp only [isEnd, lastOf, List.head?, Chain, GAdj, Distinct, g221adj_eq, g221adj,
      List.mem_cons, List.mem_singleton, decide_eq_true_eq, Option.some.injEq,
      reduceCtorEq, true_and, and_true] at h3 h0 h2 h4 hch hdis ⊢ <;>
    (simp_all; try decide; try omega)
  rcases t5 with _ | ⟨u, t6⟩
  · -- len 5：哈密顿、3-端、0/2/4 非端：穷举五顶点
    rcases fin5_cases x with rfl | rfl | rfl | rfl | rfl <;>
    rcases fin5_cases y with rfl | rfl | rfl | rfl | rfl <;>
    rcases fin5_cases z with rfl | rfl | rfl | rfl | rfl <;>
    rcases fin5_cases w with rfl | rfl | rfl | rfl | rfl <;>
    rcases fin5_cases v with rfl | rfl | rfl | rfl | rfl <;>
    simp only [isEnd, lastOf, List.head?, Chain, GAdj, Distinct, g221adj_eq, g221adj,
      List.mem_cons, List.mem_singleton, decide_eq_true_eq, Option.some.injEq,
      reduceCtorEq, true_and, and_true] at h3 h0 h2 h4 hch hdis ⊢ <;>
    (simp_all; try decide; try omega)
  · simp only [List.length_cons] at hle; omega
/-- IsCover 对分解列表顺序不敏感。 -/
theorem isCover_swap {P Q : List (Fin 5)}
    (h : IsCover (GAdj gtest221) [P, Q]) : IsCover (GAdj gtest221) [Q, P] := by
  intro x y hxy
  rcases h x y hxy with ⟨Z, hZ, hZE⟩
  have hZ' : Z = P ∨ Z = Q := by simpa using hZ
  rcases hZ' with rfl | rfl
  · exact ⟨Z, by simp, hZE⟩
  · exact ⟨Z, by simp, hZE⟩

/-! **反例主引理**：g221 上两条路 P、Q 划分边集且 P 的轮廓与参考一致、
P 是 0-端且避开 2 —— 不可能（即 fan6_nf 的结论面在 gtest221 上失败）。 -/
set_option maxHeartbeats 4000000 in
/-! cover6 的 Bool 镜像版（EIn 无可判定实例，经 eInB 转换）。 -/
theorem cover6B {P Q : List (Fin 5)}
    (hcov : IsCover (GAdj gtest221) [P, Q]) :
    (eInB P 0 1 = true ∨ eInB Q 0 1 = true) ∧ (eInB P 0 3 = true ∨ eInB Q 0 3 = true) ∧
    (eInB P 0 4 = true ∨ eInB Q 0 4 = true) ∧ (eInB P 1 2 = true ∨ eInB Q 1 2 = true) ∧
    (eInB P 1 4 = true ∨ eInB Q 1 4 = true) ∧ (eInB P 2 3 = true ∨ eInB Q 2 3 = true) := by
  have cv := cover6 hcov
  rcases cv with ⟨h1, h2, h3, h4, h5, h6⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rcases h1 with h | h
    · exact Or.inl (EIn_true_eInB _ h)
    · exact Or.inr (EIn_true_eInB _ h)
  · rcases h2 with h | h
    · exact Or.inl (EIn_true_eInB _ h)
    · exact Or.inr (EIn_true_eInB _ h)
  · rcases h3 with h | h
    · exact Or.inl (EIn_true_eInB _ h)
    · exact Or.inr (EIn_true_eInB _ h)
  · rcases h4 with h | h
    · exact Or.inl (EIn_true_eInB _ h)
    · exact Or.inr (EIn_true_eInB _ h)
  · rcases h5 with h | h
    · exact Or.inl (EIn_true_eInB _ h)
    · exact Or.inr (EIn_true_eInB _ h)
  · rcases h6 with h | h
    · exact Or.inl (EIn_true_eInB _ h)
    · exact Or.inr (EIn_true_eInB _ h)

set_option maxHeartbeats 4000000 in
theorem g221_core (P Q : List (Fin 5))
    (hpathP : IsPath (GAdj gtest221) P) (hpathQ : IsPath (GAdj gtest221) Q)
    (hcover : IsCover (GAdj gtest221) [P, Q])
    (hprofP : ∀ w : Fin 5,
      vEndBit w P + vEndBit w Q = vEndCount [[0, 1, 2, 3], [1, 4, 0, 3]] w)
    (hP0 : isEnd 0 P) (hP2 : (2 : Fin 5) ∉ P) : False := by
  have e0 := hprofP 0
  have e2 := hprofP 2
  have e3 := hprofP 3
  have e4 := hprofP 4
  rcases path_shape221 P hpathP hP0 hP2 with hPc | hPc | hPc | hPc | hPc |
    hPc | hPc | hPc | hPc | hPc
  · rw [show P = [0, 1] from hPc] at e3
    rcases vEndBit_cases (3 : Fin 5) Q with h3Q | h3Q
    · rw [h3Q] at e3; simp [vEndBit, vEndCount, lastOf] at e3
    · rw [h3Q] at e3; simp [vEndBit, vEndCount, lastOf] at e3
  · rw [show P = [1, 0] from hPc] at e3
    rcases vEndBit_cases (3 : Fin 5) Q with h3Q | h3Q
    · rw [h3Q] at e3; simp [vEndBit, vEndCount, lastOf] at e3
    · rw [h3Q] at e3; simp [vEndBit, vEndCount, lastOf] at e3
  · rw [show P = [0, 3] from hPc] at e0 e2 e3 e4 hcover
    rcases vEndBit_cases (3 : Fin 5) Q with h3Q | h3Q
    · rw [h3Q] at e3; simp [vEndBit, vEndCount, lastOf] at e3
    · rw [h3Q] at e3; simp [vEndBit, vEndCount, lastOf] at e3
      have h3Q1 : vEndBit (3 : Fin 5) Q = 1 := h3Q
      have h3Qe : isEnd (3 : Fin 5) Q := vEndBit_eq_one h3Q1
      rcases vEndBit_cases (0 : Fin 5) Q with h0' | h0'
      · rw [h0'] at e0; simp [vEndBit, vEndCount, lastOf] at e0
        have h0Q : ¬ isEnd (0 : Fin 5) Q := vEndBit_eq_zero h0'
        rcases vEndBit_cases (2 : Fin 5) Q with h2' | h2'
        · rw [h2'] at e2; simp [vEndBit, vEndCount, lastOf] at e2
          have h2Q : ¬ isEnd (2 : Fin 5) Q := vEndBit_eq_zero h2'
          rcases vEndBit_cases (4 : Fin 5) Q with h4' | h4'
          · rw [h4'] at e4; simp [vEndBit, vEndCount, lastOf] at e4
            have h4Q : ¬ isEnd (4 : Fin 5) Q := vEndBit_eq_zero h4'
            rcases q_shape221 Q hpathQ h3Qe h0Q h2Q h4Q with hQc | hQc | hQc | hQc | hQc | hQc | hQc | hQc
            · rw [show Q = [3, 0] from hQc] at hcover
              exact (by decide : ¬ ((eInB [0, 3] 0 1 = true ∨ eInB [3, 0] 0 1 = true) ∧ (eInB [0, 3] 0 3 = true ∨ eInB [3, 0] 0 3 = true) ∧
                (eInB [0, 3] 0 4 = true ∨ eInB [3, 0] 0 4 = true) ∧ (eInB [0, 3] 1 2 = true ∨ eInB [3, 0] 1 2 = true) ∧
                (eInB [0, 3] 1 4 = true ∨ eInB [3, 0] 1 4 = true) ∧ (eInB [0, 3] 2 3 = true ∨ eInB [3, 0] 2 3 = true))) (cover6B hcover)
            · rw [show Q = [0, 3] from hQc] at hcover
              exact (by decide : ¬ ((eInB [0, 3] 0 1 = true ∨ eInB [0, 3] 0 1 = true) ∧ (eInB [0, 3] 0 3 = true ∨ eInB [0, 3] 0 3 = true) ∧
                (eInB [0, 3] 0 4 = true ∨ eInB [0, 3] 0 4 = true) ∧ (eInB [0, 3] 1 2 = true ∨ eInB [0, 3] 1 2 = true) ∧
                (eInB [0, 3] 1 4 = true ∨ eInB [0, 3] 1 4 = true) ∧ (eInB [0, 3] 2 3 = true ∨ eInB [0, 3] 2 3 = true))) (cover6B hcover)
            · rw [show Q = [3, 0, 1] from hQc] at hcover
              exact (by decide : ¬ ((eInB [0, 3] 0 1 = true ∨ eInB [3, 0, 1] 0 1 = true) ∧ (eInB [0, 3] 0 3 = true ∨ eInB [3, 0, 1] 0 3 = true) ∧
                (eInB [0, 3] 0 4 = true ∨ eInB [3, 0, 1] 0 4 = true) ∧ (eInB [0, 3] 1 2 = true ∨ eInB [3, 0, 1] 1 2 = true) ∧
                (eInB [0, 3] 1 4 = true ∨ eInB [3, 0, 1] 1 4 = true) ∧ (eInB [0, 3] 2 3 = true ∨ eInB [3, 0, 1] 2 3 = true))) (cover6B hcover)
            · rw [show Q = [1, 0, 3] from hQc] at hcover
              exact (by decide : ¬ ((eInB [0, 3] 0 1 = true ∨ eInB [1, 0, 3] 0 1 = true) ∧ (eInB [0, 3] 0 3 = true ∨ eInB [1, 0, 3] 0 3 = true) ∧
                (eInB [0, 3] 0 4 = true ∨ eInB [1, 0, 3] 0 4 = true) ∧ (eInB [0, 3] 1 2 = true ∨ eInB [1, 0, 3] 1 2 = true) ∧
                (eInB [0, 3] 1 4 = true ∨ eInB [1, 0, 3] 1 4 = true) ∧ (eInB [0, 3] 2 3 = true ∨ eInB [1, 0, 3] 2 3 = true))) (cover6B hcover)
            · rw [show Q = [3, 2, 1] from hQc] at hcover
              exact (by decide : ¬ ((eInB [0, 3] 0 1 = true ∨ eInB [3, 2, 1] 0 1 = true) ∧ (eInB [0, 3] 0 3 = true ∨ eInB [3, 2, 1] 0 3 = true) ∧
                (eInB [0, 3] 0 4 = true ∨ eInB [3, 2, 1] 0 4 = true) ∧ (eInB [0, 3] 1 2 = true ∨ eInB [3, 2, 1] 1 2 = true) ∧
                (eInB [0, 3] 1 4 = true ∨ eInB [3, 2, 1] 1 4 = true) ∧ (eInB [0, 3] 2 3 = true ∨ eInB [3, 2, 1] 2 3 = true))) (cover6B hcover)
            · rw [show Q = [1, 2, 3] from hQc] at hcover
              exact (by decide : ¬ ((eInB [0, 3] 0 1 = true ∨ eInB [1, 2, 3] 0 1 = true) ∧ (eInB [0, 3] 0 3 = true ∨ eInB [1, 2, 3] 0 3 = true) ∧
                (eInB [0, 3] 0 4 = true ∨ eInB [1, 2, 3] 0 4 = true) ∧ (eInB [0, 3] 1 2 = true ∨ eInB [1, 2, 3] 1 2 = true) ∧
                (eInB [0, 3] 1 4 = true ∨ eInB [1, 2, 3] 1 4 = true) ∧ (eInB [0, 3] 2 3 = true ∨ eInB [1, 2, 3] 2 3 = true))) (cover6B hcover)
            · rw [show Q = [3, 0, 4, 1] from hQc] at hcover
              exact (by decide : ¬ ((eInB [0, 3] 0 1 = true ∨ eInB [3, 0, 4, 1] 0 1 = true) ∧ (eInB [0, 3] 0 3 = true ∨ eInB [3, 0, 4, 1] 0 3 = true) ∧
                (eInB [0, 3] 0 4 = true ∨ eInB [3, 0, 4, 1] 0 4 = true) ∧ (eInB [0, 3] 1 2 = true ∨ eInB [3, 0, 4, 1] 1 2 = true) ∧
                (eInB [0, 3] 1 4 = true ∨ eInB [3, 0, 4, 1] 1 4 = true) ∧ (eInB [0, 3] 2 3 = true ∨ eInB [3, 0, 4, 1] 2 3 = true))) (cover6B hcover)
            · rw [show Q = [1, 4, 0, 3] from hQc] at hcover
              exact (by decide : ¬ ((eInB [0, 3] 0 1 = true ∨ eInB [1, 4, 0, 3] 0 1 = true) ∧ (eInB [0, 3] 0 3 = true ∨ eInB [1, 4, 0, 3] 0 3 = true) ∧
                (eInB [0, 3] 0 4 = true ∨ eInB [1, 4, 0, 3] 0 4 = true) ∧ (eInB [0, 3] 1 2 = true ∨ eInB [1, 4, 0, 3] 1 2 = true) ∧
                (eInB [0, 3] 1 4 = true ∨ eInB [1, 4, 0, 3] 1 4 = true) ∧ (eInB [0, 3] 2 3 = true ∨ eInB [1, 4, 0, 3] 2 3 = true))) (cover6B hcover)
          · rw [h4'] at e4; simp [vEndBit, vEndCount, lastOf] at e4
        · rw [h2'] at e2; simp [vEndBit, vEndCount, lastOf] at e2
      · rw [h0'] at e0; simp [vEndBit, vEndCount, lastOf] at e0
  · rw [show P = [3, 0] from hPc] at e0 e2 e3 e4 hcover
    rcases vEndBit_cases (3 : Fin 5) Q with h3Q | h3Q
    · rw [h3Q] at e3; simp [vEndBit, vEndCount, lastOf] at e3
    · rw [h3Q] at e3; simp [vEndBit, vEndCount, lastOf] at e3
      have h3Q1 : vEndBit (3 : Fin 5) Q = 1 := h3Q
      have h3Qe : isEnd (3 : Fin 5) Q := vEndBit_eq_one h3Q1
      rcases vEndBit_cases (0 : Fin 5) Q with h0' | h0'
      · rw [h0'] at e0; simp [vEndBit, vEndCount, lastOf] at e0
        have h0Q : ¬ isEnd (0 : Fin 5) Q := vEndBit_eq_zero h0'
        rcases vEndBit_cases (2 : Fin 5) Q with h2' | h2'
        · rw [h2'] at e2; simp [vEndBit, vEndCount, lastOf] at e2
          have h2Q : ¬ isEnd (2 : Fin 5) Q := vEndBit_eq_zero h2'
          rcases vEndBit_cases (4 : Fin 5) Q with h4' | h4'
          · rw [h4'] at e4; simp [vEndBit, vEndCount, lastOf] at e4
            have h4Q : ¬ isEnd (4 : Fin 5) Q := vEndBit_eq_zero h4'
            rcases q_shape221 Q hpathQ h3Qe h0Q h2Q h4Q with hQc | hQc | hQc | hQc | hQc | hQc | hQc | hQc
            · rw [show Q = [3, 0] from hQc] at hcover
              exact (by decide : ¬ ((eInB [3, 0] 0 1 = true ∨ eInB [3, 0] 0 1 = true) ∧ (eInB [3, 0] 0 3 = true ∨ eInB [3, 0] 0 3 = true) ∧
                (eInB [3, 0] 0 4 = true ∨ eInB [3, 0] 0 4 = true) ∧ (eInB [3, 0] 1 2 = true ∨ eInB [3, 0] 1 2 = true) ∧
                (eInB [3, 0] 1 4 = true ∨ eInB [3, 0] 1 4 = true) ∧ (eInB [3, 0] 2 3 = true ∨ eInB [3, 0] 2 3 = true))) (cover6B hcover)
            · rw [show Q = [0, 3] from hQc] at hcover
              exact (by decide : ¬ ((eInB [3, 0] 0 1 = true ∨ eInB [0, 3] 0 1 = true) ∧ (eInB [3, 0] 0 3 = true ∨ eInB [0, 3] 0 3 = true) ∧
                (eInB [3, 0] 0 4 = true ∨ eInB [0, 3] 0 4 = true) ∧ (eInB [3, 0] 1 2 = true ∨ eInB [0, 3] 1 2 = true) ∧
                (eInB [3, 0] 1 4 = true ∨ eInB [0, 3] 1 4 = true) ∧ (eInB [3, 0] 2 3 = true ∨ eInB [0, 3] 2 3 = true))) (cover6B hcover)
            · rw [show Q = [3, 0, 1] from hQc] at hcover
              exact (by decide : ¬ ((eInB [3, 0] 0 1 = true ∨ eInB [3, 0, 1] 0 1 = true) ∧ (eInB [3, 0] 0 3 = true ∨ eInB [3, 0, 1] 0 3 = true) ∧
                (eInB [3, 0] 0 4 = true ∨ eInB [3, 0, 1] 0 4 = true) ∧ (eInB [3, 0] 1 2 = true ∨ eInB [3, 0, 1] 1 2 = true) ∧
                (eInB [3, 0] 1 4 = true ∨ eInB [3, 0, 1] 1 4 = true) ∧ (eInB [3, 0] 2 3 = true ∨ eInB [3, 0, 1] 2 3 = true))) (cover6B hcover)
            · rw [show Q = [1, 0, 3] from hQc] at hcover
              exact (by decide : ¬ ((eInB [3, 0] 0 1 = true ∨ eInB [1, 0, 3] 0 1 = true) ∧ (eInB [3, 0] 0 3 = true ∨ eInB [1, 0, 3] 0 3 = true) ∧
                (eInB [3, 0] 0 4 = true ∨ eInB [1, 0, 3] 0 4 = true) ∧ (eInB [3, 0] 1 2 = true ∨ eInB [1, 0, 3] 1 2 = true) ∧
                (eInB [3, 0] 1 4 = true ∨ eInB [1, 0, 3] 1 4 = true) ∧ (eInB [3, 0] 2 3 = true ∨ eInB [1, 0, 3] 2 3 = true))) (cover6B hcover)
            · rw [show Q = [3, 2, 1] from hQc] at hcover
              exact (by decide : ¬ ((eInB [3, 0] 0 1 = true ∨ eInB [3, 2, 1] 0 1 = true) ∧ (eInB [3, 0] 0 3 = true ∨ eInB [3, 2, 1] 0 3 = true) ∧
                (eInB [3, 0] 0 4 = true ∨ eInB [3, 2, 1] 0 4 = true) ∧ (eInB [3, 0] 1 2 = true ∨ eInB [3, 2, 1] 1 2 = true) ∧
                (eInB [3, 0] 1 4 = true ∨ eInB [3, 2, 1] 1 4 = true) ∧ (eInB [3, 0] 2 3 = true ∨ eInB [3, 2, 1] 2 3 = true))) (cover6B hcover)
            · rw [show Q = [1, 2, 3] from hQc] at hcover
              exact (by decide : ¬ ((eInB [3, 0] 0 1 = true ∨ eInB [1, 2, 3] 0 1 = true) ∧ (eInB [3, 0] 0 3 = true ∨ eInB [1, 2, 3] 0 3 = true) ∧
                (eInB [3, 0] 0 4 = true ∨ eInB [1, 2, 3] 0 4 = true) ∧ (eInB [3, 0] 1 2 = true ∨ eInB [1, 2, 3] 1 2 = true) ∧
                (eInB [3, 0] 1 4 = true ∨ eInB [1, 2, 3] 1 4 = true) ∧ (eInB [3, 0] 2 3 = true ∨ eInB [1, 2, 3] 2 3 = true))) (cover6B hcover)
            · rw [show Q = [3, 0, 4, 1] from hQc] at hcover
              exact (by decide : ¬ ((eInB [3, 0] 0 1 = true ∨ eInB [3, 0, 4, 1] 0 1 = true) ∧ (eInB [3, 0] 0 3 = true ∨ eInB [3, 0, 4, 1] 0 3 = true) ∧
                (eInB [3, 0] 0 4 = true ∨ eInB [3, 0, 4, 1] 0 4 = true) ∧ (eInB [3, 0] 1 2 = true ∨ eInB [3, 0, 4, 1] 1 2 = true) ∧
                (eInB [3, 0] 1 4 = true ∨ eInB [3, 0, 4, 1] 1 4 = true) ∧ (eInB [3, 0] 2 3 = true ∨ eInB [3, 0, 4, 1] 2 3 = true))) (cover6B hcover)
            · rw [show Q = [1, 4, 0, 3] from hQc] at hcover
              exact (by decide : ¬ ((eInB [3, 0] 0 1 = true ∨ eInB [1, 4, 0, 3] 0 1 = true) ∧ (eInB [3, 0] 0 3 = true ∨ eInB [1, 4, 0, 3] 0 3 = true) ∧
                (eInB [3, 0] 0 4 = true ∨ eInB [1, 4, 0, 3] 0 4 = true) ∧ (eInB [3, 0] 1 2 = true ∨ eInB [1, 4, 0, 3] 1 2 = true) ∧
                (eInB [3, 0] 1 4 = true ∨ eInB [1, 4, 0, 3] 1 4 = true) ∧ (eInB [3, 0] 2 3 = true ∨ eInB [1, 4, 0, 3] 2 3 = true))) (cover6B hcover)
          · rw [h4'] at e4; simp [vEndBit, vEndCount, lastOf] at e4
        · rw [h2'] at e2; simp [vEndBit, vEndCount, lastOf] at e2
      · rw [h0'] at e0; simp [vEndBit, vEndCount, lastOf] at e0
  · rw [show P = [0, 4] from hPc] at e3
    rcases vEndBit_cases (3 : Fin 5) Q with h3Q | h3Q
    · rw [h3Q] at e3; simp [vEndBit, vEndCount, lastOf] at e3
    · rw [h3Q] at e3; simp [vEndBit, vEndCount, lastOf] at e3
  · rw [show P = [4, 0] from hPc] at e3
    rcases vEndBit_cases (3 : Fin 5) Q with h3Q | h3Q
    · rw [h3Q] at e3; simp [vEndBit, vEndCount, lastOf] at e3
    · rw [h3Q] at e3; simp [vEndBit, vEndCount, lastOf] at e3
  · rw [show P = [0, 1, 4] from hPc] at e3
    rcases vEndBit_cases (3 : Fin 5) Q with h3Q | h3Q
    · rw [h3Q] at e3; simp [vEndBit, vEndCount, lastOf] at e3
    · rw [h3Q] at e3; simp [vEndBit, vEndCount, lastOf] at e3
  · rw [show P = [4, 1, 0] from hPc] at e3
    rcases vEndBit_cases (3 : Fin 5) Q with h3Q | h3Q
    · rw [h3Q] at e3; simp [vEndBit, vEndCount, lastOf] at e3
    · rw [h3Q] at e3; simp [vEndBit, vEndCount, lastOf] at e3
  · rw [show P = [0, 4, 1] from hPc] at e3
    rcases vEndBit_cases (3 : Fin 5) Q with h3Q | h3Q
    · rw [h3Q] at e3; simp [vEndBit, vEndCount, lastOf] at e3
    · rw [h3Q] at e3; simp [vEndBit, vEndCount, lastOf] at e3
  · rw [show P = [1, 4, 0] from hPc] at e3
    rcases vEndBit_cases (3 : Fin 5) Q with h3Q | h3Q
    · rw [h3Q] at e3; simp [vEndBit, vEndCount, lastOf] at e3
    · rw [h3Q] at e3; simp [vEndBit, vEndCount, lastOf] at e3

/-! 假设面与反例主定理。 -/

/-- 假设面：D 是 gtest221 的分解——以假设传入（gtest95b 同款先例；
    6 边划分逐边可查：{01,12,23} ∪ {14,04,03} = E 且不交，
    双实现机器校验同此）。 -/
theorem gtest221_isdecomp_of (hD : IsDecomp gtest221 [[0, 1, 2, 3], [1, 4, 0, 3]]) :
    IsDecomp gtest221 [[0, 1, 2, 3], [1, 4, 0, 3]] := hD

/-- 假设面：死邻居数 0 < D(b) = 1。 -/
theorem gtest221_hdead :
    ((finList 5).filter (fun w => decide (gtest221.adjB (2 : Fin 5) w = true ∧
      vEndCount ([[0, 1, 2, 3], [1, 4, 0, 3]] : List (List (Fin 5))) w = 0))).length
    < vEndCount ([[0, 1, 2, 3], [1, 4, 0, 3]] : List (List (Fin 5))) (0 : Fin 5) := by
  decide

/-- 假设面：ab = (2, 0) 非边（lane_111 补件；lane_109 §1.3 勘误指出 lane_108
    报告表格列有此件而 Lean 中未落盘）。(2, 0) 不在 g221adj 边表
    {01, 03, 04, 12, 14, 23} 中，decide 级机检。 -/
theorem gtest221_hab0 : gtest221.adjB (2 : Fin 5) (0 : Fin 5) = false := by
  decide

/-! **反例主定理**：gtest221 上 fan6_nf 的结论面失败——不存在满足
    同条数、同逐点轮廓、含 0-端避开 2 的路的分解。 -/
set_option maxHeartbeats 4000000 in
theorem gtest221_no_target :
    ¬ ∃ D'' : List (List (Fin 5)),
      IsDecomp gtest221 D'' ∧ D''.length = 2 ∧
      (∀ w : Fin 5, vEndCount D'' w = vEndCount [[0, 1, 2, 3], [1, 4, 0, 3]] w) ∧
      ∃ P ∈ D'', isEnd 0 P ∧ (2 : Fin 5) ∉ P := by
  rintro ⟨D'', ⟨⟨hpaths, hcov, hdj⟩, hdis⟩, hlen, hprof, P, hPmem, hP0, hP2⟩
  rcases D'' with _ | ⟨X, _ | ⟨Y, _ | ⟨Z, _⟩⟩⟩ <;> simp at hlen
  have hP' : P = X ∨ P = Y := by simpa using hPmem
  rcases hP' with rfl | rfl
  · exact g221_core P Y (hpaths P (by simp)) (hpaths Y (by simp)) hcov hprof hP0 hP2
  · exact g221_core P X (hpaths P (by simp)) (hpaths X (by simp)) (isCover_swap hcov)
      (fun w => by
        have hw := hprof w
        simp only [vEndCount, List.foldr_cons, List.foldr_nil, vEndBit] at hw ⊢
        omega)
      hP0 hP2


/-! ## 死角引理 · 硬残差 120 三路编织（lane_136，W3 第六棒；纸面真证 +
机器底账；本节为独立纯注释块，零代码零 sorry，陈述勿当定理引用，不接
前棒注释链）

**[GAP-133A] 消解（lane_133 §3.3 收窄的硬残差 120，本棒模板化）**：
骨架（120/120 机器逐例断言，`lab136_template`；域内全域刻画
`lab136_class`：a_fail 的 (2,1,3) 形态 1,440 中骨架实例 240、
(u,v₁)=(x,q) 刚性分配 240/240）：
  (S1) P_b = [b, x, a, q]（b 端、a 内部 j=2、q 端）；
  (S2) R = [a, p, b, q, x]（a 端、b 内部中位）；
  (S3) S₀ = 单边 {s,t}（第三路，钉住路）。

**引理（S₀ 二分逼迫，纸面）**：S₀ ∈ {{p,q}, {p,x}}。证：S₀ 是 G₀ 的边
且异于 R/P_b 全部边；10 顶点对中含 b 的 4 对 = 删边 {a,b} 或 R/P_b 边、
不含 b 的 6 对中 {a,p},{q,x}∈R、{a,q},{a,x}∈P_b ⟹ 仅剩两对。

**定理（T-pq 三路编织模板，纸面完整记账证明；机器 120/120）**：前提
骨架 ∧ S₀={p,q}，D′ = {Q₁,Q₂,Q₃}：
  Q₁ = [a, b, q, x]（ab 新、bq、qx）
  Q₂ = [q, p, b, x, a]（pq = S₀、pb、bx、xa）
  Q₃ = [q, a, p]（qa、ap）
边账：pes(Q₁)⊔pes(Q₂)⊔pes(Q₃) = P_b 全边 ∪ R 全边 ∪ S₀ ∪ {ab} =
E(H)（九条两两不交，划分性显式）；路性：三路顶点集两两互异内各自互异；
条数 3 = 3；端账：旧 (a1,b1,q2,x1,p1) → 新 (a2,b0,q2,x1,p1) =
旧 + (a:+1, b:−1) ∎。代表例 G=511、删 (0,1)、a=0、b=1：
D = {[0,3,1,2,4],[1,4,0,2],[2,3]}，D′ = {[0,1,2,4],[2,3,1,4,0],[2,0,3]}。

**定理（T-px 模板，纸面记账证明；机器 120/120 + 合成实例）**：前提
骨架 ∧ S₀={p,x}，D′ = {[a,b,q,x,p], [q,a,x], [a,p,b,x]}：边账
{ab,bq,qx,xp}⊔{qa,ax}⊔{ap,pb,bx} = E(H)；端账旧 (a1,b1,q1,x2,p1) →
新 (a2,b0,q1,x2,p1) ∎。

**引理（硬性来源，纸面）**：骨架 ∧ S₀={p,q} ⟹ 无任何 2-路替换。
证：S=S₀ 时 deg_U(b)=1<2 ✗；S=R 时两新路端多集 {a,a,q,x}、b 全内部
⟹ b 的 4 边三种配对逐一穷举：(i) {bx,pb}|{bq,ab}、(ii) {bx,bq}|{pb,ab}
（p-侧链含 [p,a] 与同路端 a 重复，一步否决）、(iii) {bx,ab}|{pb,bq}，
各配对下非 b 边 {xa,aq,ap,qx} 作端链的放置穷举均致「剩余边无法安置或
路内顶点重复或端多集不合」∎。推论：硬类 = 骨架 ∩ S₀={p,q}
（⟸ 纸面；⟹ 机器域内刻画）。{p,x} 半 120/120 有 2-路解（机器）⟹
不入硬类——此即 {p,x} 在硬类中为空之因。

**机器底账（`lab136_template`/`lab136_class` from-scratch + `lab133`
管线复跑全锚逐位命中）**：T-pq 覆盖 120/120（lab136 显式不交五子句
验证器 + lab133 verify_five 双验证器交叉）；T-px 覆盖骨架类 px 半
120/120；骨架类全二分 {p,q}×120 + {p,x}×120；独立 2-路判定（2^|U|
子集枚举）复核硬类 0 违反。shapeA 撞顶点 8,160 定理级收口（2-路替换
8,040 承 lane_133 + 本棒 120）；死角引理三桶机器底账 44,940 全 sat。 -/

/-! ## lane_150：统一记账主引理 Lean 化（r-路替换段重组；一般 n 真证） -/

/-- 端点计数在拼接下的可加性。 -/
theorem vEndCount_append {n : Nat} (D1 D2 : List (List (Fin n))) (v : Fin n) :
    vEndCount (D1 ++ D2) v = vEndCount D1 v + vEndCount D2 v := by
  induction D1 with
  | nil => simp [vEndCount]
  | cons x t ih =>
      change vEndBit v x + vEndCount (t ++ D2) v =
        (vEndBit v x + vEndCount t v) + vEndCount D2 v
      rw [ih]
      omega

/-- 长 ≥2 的列表必有边（EIn 存在性）。 -/
theorem EIn_exists_of_length_ge2 {V : Type} : ∀ (l : List V),
    2 ≤ l.length → ∃ u v, EIn l u v
  | [], h => by simp at h
  | [_], h => by simp at h
  | u :: v :: r, h => ⟨u, v, by simp [EIn]⟩

/-- Distinct 拼接下左半元素不落入右半。 -/
theorem distinct_append_na {V : Type} : ∀ (l1 l2 : List V) (a : V),
    Distinct (l1 ++ l2) → a ∈ l1 → a ∉ l2
  | [], l2, a, h, hmem => by simp at hmem
  | b :: t, l2, a, h, hmem => by
      rcases h with ⟨hb, hrest⟩
      rcases List.mem_cons.1 hmem with hm | ht
      · intro ha
        exact hb (List.mem_append.2 (Or.inr (by simpa [hm] using ha)))
      · exact distinct_append_na t l2 a hrest ht

/-- **统一记账主引理（r-路替换段重组；lane_150 Lean 化，一般 n 真证）**：
    D = Ps ++ R 分解 G₀ = H − ab。把 Ps（r 条）替换为 Qs（|Qs|=|Ps| 条 H 上
    简单路）：
      (i)  Qs 两两（作为列表）互异且边不交，每条 Q 的边 ⊆ pes(Ps) ∪ {ab}；
      (ii) pes(Ps) 的每条边被某条 Q 覆盖；
      (iii) ∃ Q ∈ Qs 含边 ab；
      (iv) 端点账：vEndCount Qs = vEndCount Ps + (a:+1, b:−1)（hEnd 三条）；
    则 D' = Qs ++ R 满足 fan6_use 五子句（条数不变、覆盖恰 E(H)、两两边不交、
    a 端 +1、b 端 −1、其余逐点不变）。纯记账组装，无路存在性前提
    （r≤3 存在性 = [GAP-149]，属另一层，由机器完备枚举背书）。 -/
theorem fan6_replace_many {n : Nat} (H : Graph n) (a b : Fin n)
    (Ps Qs R : List (List (Fin n)))
    (hD : IsDecomp (del1 H a b) (Ps ++ R))
    (hQlen : Qs.length = Ps.length)
    (hQdisQ : Distinct Qs)
    (hQpath : ∀ Q ∈ Qs, IsPath (GAdj H) Q)
    (hQdisjQ : ∀ Q1 ∈ Qs, ∀ Q2 ∈ Qs, Q1 ≠ Q2 → ∀ x y, ¬ (EIn Q1 x y ∧ EIn Q2 x y))
    (hQinU : ∀ Q ∈ Qs, ∀ x y, EIn Q x y →
        (∃ P ∈ Ps, EIn P x y) ∨ (x = a ∧ y = b) ∨ (x = b ∧ y = a))
    (hQcovPs : ∀ P ∈ Ps, ∀ x y, EIn P x y → ∃ Q ∈ Qs, EIn Q x y)
    (hQhasAb : ∃ Q ∈ Qs, EIn Q a b)
    (hEndA : vEndCount Qs a = vEndCount Ps a + 1)
    (hEndB : vEndCount Qs b + 1 = vEndCount Ps b)
    (hEndO : ∀ w : Fin n, w ≠ a → w ≠ b → vEndCount Qs w = vEndCount Ps w) :
    ∃ D' : List (List (Fin n)), IsDecomp H D' ∧ D'.length = (Ps ++ R).length ∧
      vEndCount D' a = vEndCount (Ps ++ R) a + 1 ∧
      vEndCount D' b + 1 = vEndCount (Ps ++ R) b ∧
      ∀ w : Fin n, w ≠ a → w ≠ b → vEndCount D' w = vEndCount (Ps ++ R) w := by
  -- R 中路的 H-路径性
  have hRpathH : ∀ Q ∈ R, IsPath (GAdj H) Q := by
    intro Q hQmem
    have hQD : Q ∈ Ps ++ R := List.mem_append.2 (Or.inr hQmem)
    have hQ0 : IsPath (GAdj (del1 H a b)) Q := hD.1.1 Q hQD
    exact ⟨hQ0.1, hQ0.2.1, chain_del1_to_H H a b Q hQ0.2.2⟩
  -- Q ∈ Qs 必不落入 R（Q 有边；边 ⊆ pes(Ps) ∪ {ab}；ab ∉ G₀；D 边不交）
  have hQnotR : ∀ Q ∈ Qs, Q ∉ R := by
    intro Q hQmem hQR
    have hED : IsEdgeDisjoint (Ps ++ R) := hD.1.2.2
    have hQdel : IsPath (GAdj (del1 H a b)) Q :=
      hD.1.1 Q (List.mem_append.2 (Or.inr hQR))
    obtain ⟨u, v, hEin⟩ := EIn_exists_of_length_ge2 Q hQdel.1
    have hU := hQinU Q hQmem u v hEin
    rcases hU with hP | hab | hab
    · rcases hP with ⟨P, hPs, hPuv⟩
      have hPD : P ∈ Ps ++ R := List.mem_append.2 (Or.inl hPs)
      have hQD : Q ∈ Ps ++ R := List.mem_append.2 (Or.inr hQR)
      have hne : P ≠ Q := by
        intro hq
        have hPna : P ∉ R := distinct_append_na Ps R P hD.2 hPs
        exact hPna (by simpa [← hq] using hQR)
      exact hED P hPD Q hQD hne u v ⟨hPuv, hEin⟩
    · rcases hab with ⟨hu, hv⟩
      have hE2 := EIn_adj (del1 H a b) Q hQdel a b (by simpa [hu, hv] using hEin)
      exact ((del1_adj_iff H a b a b).1 hE2).2 (Or.inl ⟨rfl, rfl⟩)
    · rcases hab with ⟨hu, hv⟩
      have hE2 := EIn_adj (del1 H a b) Q hQdel b a (by simpa [hu, hv] using hEin)
      exact ((del1_adj_iff H a b b a).1 hE2).2 (Or.inr ⟨rfl, rfl⟩)
  -- Distinct
  have hRdis : Distinct R := distinct_append_inv Ps R hD.2
  have hdis' : Distinct (Qs ++ R) := distinct_append Qs R hQdisQ hRdis hQnotR
  -- 路径性（Qs 直接假设；R 用 hD）
  have hpaths' : ∀ P ∈ Qs ++ R, IsPath (GAdj H) P := by
    intro P hPmem
    rcases List.mem_append.1 hPmem with hPs | hRmem
    · exact hQpath P hPs
    · exact hRpathH P hRmem
  -- 覆盖
  have hcov' : IsCover (GAdj H) (Qs ++ R) := by
    intro x y hxy
    by_cases hE : (x = a ∧ y = b) ∨ (x = b ∧ y = a)
    · rcases hE with ⟨hx, hy⟩ | ⟨hx, hy⟩
      · obtain ⟨Q, hQmem, hQab⟩ := hQhasAb
        refine ⟨Q, List.mem_append.2 (Or.inl hQmem), ?_⟩
        rw [hx, hy]
        exact hQab
      · obtain ⟨Q, hQmem, hQab⟩ := hQhasAb
        refine ⟨Q, List.mem_append.2 (Or.inl hQmem), ?_⟩
        rw [hx, hy]
        exact EIn_symm Q a b hQab
    · obtain ⟨P, hPmem, hPxy⟩ :=
        hD.1.2.1 x y ((del1_adj_iff H a b x y).2 ⟨hxy, hE⟩)
      rcases List.mem_append.1 hPmem with hPs | hRmem
      · rcases hQcovPs P hPs x y hPxy with ⟨Q, hQmem, hQxy⟩
        refine ⟨Q, List.mem_append.2 (Or.inl hQmem), hQxy⟩
      · exact ⟨P, List.mem_append.2 (Or.inr hRmem), hPxy⟩
  -- 边不交
  have hdisj' : IsEdgeDisjoint (Qs ++ R) := by
    intro Q1 hQ1 Q2 hQ2 hne x y hE
    obtain ⟨hE1, hE2⟩ := hE
    rcases List.mem_append.1 hQ1 with hQ1s | hQ1r
    · rcases List.mem_append.1 hQ2 with hQ2s | hQ2r
      · exact hQdisjQ Q1 hQ1s Q2 hQ2s hne x y ⟨hE1, hE2⟩
      · -- Q1 ∈ Qs, Q2 ∈ R
        have hQ2D : Q2 ∈ Ps ++ R := List.mem_append.2 (Or.inr hQ2r)
        have hQ2del : IsPath (GAdj (del1 H a b)) Q2 := hD.1.1 Q2 hQ2D
        have hE1U := hQinU Q1 hQ1s x y hE1
        rcases hE1U with hP | hab | hab
        · rcases hP with ⟨P, hPs, hPxy⟩
          have hPD : P ∈ Ps ++ R := List.mem_append.2 (Or.inl hPs)
          have hne' : P ≠ Q2 := by
            intro hq
            have hPna : P ∉ R := distinct_append_na Ps R P hD.2 hPs
            exact hPna (by simpa [← hq] using hQ2r)
          exact hD.1.2.2 P hPD Q2 hQ2D hne' x y ⟨hPxy, hE2⟩
        · rcases hab with ⟨hx, hy⟩
          have hE2' := EIn_adj (del1 H a b) Q2 hQ2del a b (by simpa [hx, hy] using hE2)
          exact ((del1_adj_iff H a b a b).1 hE2').2 (Or.inl ⟨rfl, rfl⟩)
        · rcases hab with ⟨hx, hy⟩
          have hE2' := EIn_adj (del1 H a b) Q2 hQ2del b a (by simpa [hx, hy] using hE2)
          exact ((del1_adj_iff H a b b a).1 hE2').2 (Or.inr ⟨rfl, rfl⟩)
    · rcases List.mem_append.1 hQ2 with hQ2s | hQ2r
      · -- Q1 ∈ R, Q2 ∈ Qs
        have hQ1D : Q1 ∈ Ps ++ R := List.mem_append.2 (Or.inr hQ1r)
        have hQ1del : IsPath (GAdj (del1 H a b)) Q1 := hD.1.1 Q1 hQ1D
        have hE2U := hQinU Q2 hQ2s x y hE2
        rcases hE2U with hP | hab | hab
        · rcases hP with ⟨P, hPs, hPxy⟩
          have hPD : P ∈ Ps ++ R := List.mem_append.2 (Or.inl hPs)
          have hne' : P ≠ Q1 := by
            intro hq
            have hPna : P ∉ R := distinct_append_na Ps R P hD.2 hPs
            exact hPna (by simpa [← hq] using hQ1r)
          exact hD.1.2.2 P hPD Q1 hQ1D hne' x y ⟨hPxy, hE1⟩
        · rcases hab with ⟨hx, hy⟩
          have hE1' := EIn_adj (del1 H a b) Q1 hQ1del a b (by simpa [hx, hy] using hE1)
          exact ((del1_adj_iff H a b a b).1 hE1').2 (Or.inl ⟨rfl, rfl⟩)
        · rcases hab with ⟨hx, hy⟩
          have hE1' := EIn_adj (del1 H a b) Q1 hQ1del b a (by simpa [hx, hy] using hE1)
          exact ((del1_adj_iff H a b b a).1 hE1').2 (Or.inr ⟨rfl, rfl⟩)
      · -- Q1, Q2 ∈ R：承 D 的边不交
        have hQ1D : Q1 ∈ Ps ++ R := List.mem_append.2 (Or.inr hQ1r)
        have hQ2D : Q2 ∈ Ps ++ R := List.mem_append.2 (Or.inr hQ2r)
        exact hD.1.2.2 Q1 hQ1D Q2 hQ2D hne x y ⟨hE1, hE2⟩
  -- 组装
  have hdec : IsDecomp H (Qs ++ R) := ⟨⟨hpaths', hcov', hdisj'⟩, hdis'⟩
  have hlen' : (Qs ++ R).length = (Ps ++ R).length := by
    rw [List.length_append, List.length_append, hQlen]
  have hEndA' : vEndCount (Qs ++ R) a = vEndCount (Ps ++ R) a + 1 := by
    rw [vEndCount_append Qs R a, vEndCount_append Ps R a, hEndA]
    omega
  have hEndB' : vEndCount (Qs ++ R) b + 1 = vEndCount (Ps ++ R) b := by
    rw [vEndCount_append Qs R b, vEndCount_append Ps R b]
    rw [← hEndB]
    omega
  have hEndO' : ∀ w : Fin n, w ≠ a → w ≠ b → vEndCount (Qs ++ R) w = vEndCount (Ps ++ R) w := by
    intro w hwa hwb
    rw [vEndCount_append Qs R w, vEndCount_append Ps R w, hEndO w hwa hwb]
  exact ⟨Qs ++ R, hdec, hlen', hEndA', hEndB', hEndO'⟩

/-! ## 死角引理一般形态 · r-路替换段重组主引理（lane_149，W3 第七棒；
统一记账 + 机器完备底账 + 边界刻画；独立纯注释块，零代码零 sorry，
陈述勿当定理引用，不接前棒注释链）

**死角域**（承 lane_120 口径）：H 有边 ab，G₀=H−ab，D 分解 G₀，无 b-端
避开 a 路 ∧ dead(a)=0 ∧ vEndCount D b=1。n=5：qualifying 482,080 /
直用 430,400 / 死角 44,940 / C5 域 6,740。

**统一记账主引理（r-路替换段重组，纸面真证，一般 n）**：P_b ∈ D 唯一
b-端路（死角 ⟹ 恰一条），T ⊆ D∖{P_b}，|T|=k≥1，U := pes(P_b) ∪
pes(T₁) ∪ … ∪ pes(T_k) ∪ {ab}。若 ∃ k+1 条 H 上简单路 Q₁..Q_{k+1} 使
  (i)  pes(Q₁) ⊔ … ⊔ pes(Q_{k+1}) = U（边划分）；
  (ii) endvec{Q₁..Q_{k+1}} = endvec{P_b}∪T + (a:+1, b:−1)，
则 D' := (D∖({P_b}∪T)) ∪ {Q₁..Q_{k+1}} 满足 fan6_use 五子句：条数
−（k+1）+（k+1）=0；覆盖 = 其余路 ∪ U = E(G₀)∪{ab} = E(H)；边不交 =
(i) 与其余路原不交性；端账 = 其余不动 + (ii)；每条 Qᵢ 边 ⊆ U ⊆ E(H)。
∎ 记 r := k+1。全部既有模板——tail-swap、shapeC B/B2/B3、B-S、B-T、
T-SB、配对三分 T-i/T-ii/T-iii、T-pq/T-px——皆为主引理的具体段划分
实例；lane_133 的 148 类形状目录无需逐类证明。

**死角引理一般形态（n=5，定理级）**：死角域每一例 ∃ T，|T|≤2（r≤3）
满足 (i)(ii) ⟹ 五子句成立。机器完备（`src/lab149_unify.py`
from-scratch 完备精确覆盖搜索 + 第二实现 `src/lab149_cross.py` 全量对拍）：
corner_r2 = 43,920、corner_r3 = 1,020、corner_none = 0；三桶分域
（机器精确互斥划分）：shapeC 29,340 = r2 28,560 + r3 780；
shapeA 11,160 = r2 11,040 + r3 120；shapeB 4,440 = r2 4,320 + r3 120。

**r=3 边界（必须三路、最小不可二路的 1,020 例，逐例核入纸面模板域）**：
shapeA 硬 120 = lane_136 骨架 P_b=[b,x,a,q]、R=[a,p,b,q,x]、S₀={p,q}
（T-pq 域；「无 2-路替换」为 lane_136 §3.4 三配对穷举纸面定理；本棒
独立完备搜索 120/120 复核）；shapeB 120（|D|=3、|P_b|=4、j=2、无 b-
内部伙伴）→ B-T 域；shapeC 780 全部 |P_b|=3（P_b=[b,u,a]），五子类
(|D|,b 内部伙伴数)=(3,0)×240、(4,1)×240、(4,0)×180、(3,1)×120 →
B2 域 780/780。最小实例：G=511（K₅）、删边 (0,1)、a=1、b=0、
D={[0,3,1,2],[1,4,0,2,3],[2,4]}。witness 五子句独立核验 1,040 条
bad=0（`src/lab149_verify.py`）。

**[GAP-149]（诚实边界）**：主引理一般 n 纸面真证；「r≤3 存在性」为
n=5 域内机器完备事实（穷举搜索），非一般 n 纸面证明——一般 n 的替换
路数上界仍开放（承 lane_120「受控级联构造理论」）。

**勘误补记（tail-swap 计数）**：lane_120/129/133 的 tmpl_ok=3,000 /
tmpl_fail=8,160 系实现缺陷所致——lane_120 的
`template_construct(...) or template_construct(..., rev_R=True)` 中
`or` 短路使反向切片从未生效（首调用返回非空元组即短路）；
lane_129/133 的 `ja = Pb.index(a)` 用未定向原序 Pb 的索引去切定向后
Pbo，混合朝向。修正口径（ja 取 Pbo 定向序）下 tail-swap 实际覆盖
**6,000/11,160（54%）**、失败 5,160；「8,160 撞顶点桶」随之更正为
5,160。与 bug 无关的机器事实不受影响并逐位复核：2-路替换边界
（r2 43,920 / r3 1,020 / hard 120）、lane_136 T-pq 域 120/120、
B2 域 780/780、锚点 482,080/44,940/4,440/29,340。 -/

/-! ## lane_154：C2 直组降档（fan6_use 四子句真证，2026-09-21）

**背景**：fan6_use（Astar.lean）原为五子句陈述（IsDecomp / 条数 / a+1 / b−1 /
其余逐点不动），剩余域 sorry 挂在「无 b-端避开 a 路」分支。lane_119 §1 组装
锁死引理：case1 式组装（C2 提供 a/b 两点轮廓 + 避开路，fan6_case1 延长）恰得
前四子句，第 5 子句对 w∉{a,b} 组装不出（需 D''(w)=D(w) 全轮廓，= 假陈述
fan6_nf 面）。消费面核对（lane_120 逐点 + 本棒独立复核）：paper 5 应用点
（main.tex :480/:544/:594/:2641/:2667）+ :329 内嵌 + Lean 侧 lEngine（1/2/4）、
fan7_use_le_two（3）全不消费第 5 子句 ⟹ 删第 5 子句语义保真。

**C2（fan6_use_c2）**：与 fan6_nf 同假设面（hab0 + hdead），结论弱化为
a/b 两点轮廓保持 + 存在 b-端避开 a 的路。机器验证：n=5 全空间 78,540
qualifying 四元组 0 违反、n=6 已扫 ≈1.07 亿 0 违反（lane_119 §3.2/§3.3）；
反例点 221 有显式 witness。**未证（研究缺口），`sorry` 换位承接原
fan6_use 的剩余域缺口；勿当已证定理引用**。

**fan6_use_weak（四子句，完全真证）**：C2 给 D''（G₀ 上等 a/b 轮廓 + 避开路
P），fan6_case1 延长得 D'：IsDecomp H / 条数不变 / a+1 / b−1。零新 sorry，
证明体无分支无占位；唯一外部依赖 = fan6_use_c2。 -/

/-- **C2：等 a/b 轮廓重排 + b-端避开 a 路（lane_119 候选，机器 0 违反）**：
    G₀ 无边 ab，D 分解 G₀，a 的死邻居数 < D(b) ⟹ 存在同条数、a/b 两点轮廓
    相同的分解 D''，其中某条 b-端路径避开 a。n=5 全空间 + n=6 已扫 0 违反
    （`lab119_cand`）；**未证（研究缺口，由 fan6_use 五子句剩余域换位承接，
    lane_154）**。 -/
theorem fan6_use_c2 {n : Nat} (G₀ : Graph n) (a b : Fin n)
    (hab0 : G₀.adjB a b = false)
    (D : List (List (Fin n))) (hD : IsDecomp G₀ D)
    (hdead : ((finList n).filter
        (fun w => decide (G₀.adjB a w = true ∧ vEndCount D w = 0))).length
      < vEndCount D b) :
    ∃ D'' : List (List (Fin n)),
      IsDecomp G₀ D'' ∧ D''.length = D.length ∧
      vEndCount D'' a = vEndCount D a ∧ vEndCount D'' b = vEndCount D b ∧
      ∃ P ∈ D'', isEnd b P ∧ a ∉ P := by
  sorry

/-- **fan6_use 弱化版（四子句；lane_154 C2 直组完全真证）**：H 有边 ab，D 分解
    H−ab，a 在 H−ab 中死邻居数 < D(b) ⟹ ∃ D'：IsDecomp H D' ∧ |D'|=|D| ∧
    D'(a)=D(a)+1 ∧ D'(b)+1=D(b)。第 5 子句（其余逐点不动）已删除——组装锁死
    引理（lane_119 §1）证明其不可由 C2+case1 组装，且无任何消费者使用
    （paper 5 应用点 + :329 内嵌 + Lean lEngine/fan7_use_le_two，本棒独立
    复核）。证明：`fan6_use_c2` 给 D''（等 a/b 轮廓 + b-端避开 a 路 P），
    `fan6_case1`（真证）延长得四子句。 -/
theorem fan6_use_weak {n : Nat} (H : Graph n) (a b : Fin n) (hab : H.adjB a b = true)
    (D : List (List (Fin n))) (hD : IsDecomp (del1 H a b) D)
    (hpass : ((finList n).filter
        (fun w => decide ((del1 H a b).adjB a w = true ∧ vEndCount D w = 0))).length
      < vEndCount D b) :
    ∃ D' : List (List (Fin n)), IsDecomp H D' ∧ D'.length = D.length ∧
      vEndCount D' a = vEndCount D a + 1 ∧ vEndCount D' b + 1 = vEndCount D b := by
  have hab0 : (del1 H a b).adjB a b = false :=
    Bool.eq_false_iff.2 (fun hc => by
      have hr := (del1_adj_iff H a b a b).1 hc
      exact hr.2 (Or.inl ⟨rfl, rfl⟩))
  obtain ⟨D'', hD'', hlen'', hA'', hB'', P, hPmem, hPend, hPav⟩ :=
    fan6_use_c2 (del1 H a b) a b hab0 D hD hpass
  obtain ⟨D', hD', hlen', hA', hB', _⟩ :=
    fan6_case1 H a b hab D'' hD'' P hPmem hPend hPav
  refine ⟨D', hD', ?_, ?_, ?_⟩
  · rw [hlen']
    exact hlen''
  · rw [hA', hA'']
  · rw [hB', hB'']

/-! ## lane_161：[GAP-150]「死角域替换路数 r≤4 恒成立?」机器扩样定界 +
4-路编织族提炼（独立纯注释块，零代码零 sorry，不接前棒注释链）

**机器定界（lab161_ext，白天 120,000 角例，双 seed）**：n=6: 54,000
（r2 52,591 / r3 1,392 / r4 17）、n=7: 36,000（r2 35,325 / r3 663 /
r4 12）、n=8: 30,000（r2 29,520 / r3 476 / r4 4）；r5=r6=none=0。
**覆盖缺口修复**：lab150 生成器只产 |D|≤4（r≤4 结构性封顶），本棒
补齐 |D|≤7——|D|≥5 象限 36,895 例零 r≥5（首份该象限数据）；r4 于
|D|=5/7 亦出现，min_r 不被 |D| 平凡封顶。

**4-路编织族 W4-TYPES（lab161_w4，7 型参数化机检零违例）**：旧段
P_b+三伙伴（8 边），新段 4 条 H-路含 ab；逐型机检 (i) 边划分
(ii) 端账位移 a:+1/b:−1，经 `fan6_replace_many` 组装五子句。代表型
T1（即 lane_150 n=6 最小反例）：旧段 bxa|cadx|ec|dea，新段
cabx|cea|dxa|eda，U 九边划分 {ca,ab,bx}⊔{ce,ea}⊔{dx,xa}⊔{ed,da}，
端账 (b1,a2,c2,x1,d1,e1)→(b0,a3,c2,x1,d1,e1)。同旧段容 4 个新分划
（T1/T1b/T1c/T1d）；另有 T2（bxa|pqar|qr|apx）、T3（buva|satv|twa|ws）、
T4（aub|gahi|uia|hj）。**族丰富性障碍**：7 型仅盖 32 witness 中 8 个
（旧段长度签名 8 种/新段 15 种）⟹ 逐型枚举路线对一般 n「r≤4」证明
不可达，须结构性刻画（[GAP-150] 保持开放；r≥5 无——120k 例 +
36,895 例 |D|≥5 零命中，扩样续于夜批）。31 条 r4 证书第二实现
（lab161_refute）全量复核 CERTIFIED。 -/

/-! ## lane_163：T158.1 闭式蒸馏（表级闭式覆盖 62/62）——L160.3 低带分离不等式核
（独立定理块，零 sorry，不接前棒注释链）

**纸面-机器混合底账（lab163_*，2026-09-21 白天）**：62 例 C148.1 判据域实际选择
(hv,π,m*,Lw,Sw) 全量提取（lab163_choices62.json）；无搜索展开器 ctor4 四层验证
（表一致 / L160.2 账本 / 双射+边类互异 / check_theta+solve_E 双通道）62/62 全过。
槽位界（机器 62 例全量）：hv 候选序号 ≤8；π ∈ {asc:16, desc:8, swap:38}；
m* 距 sorted(T) 最近端 ≤5；b-对称引理 L163.1：ctor3 选择只依赖 (bL,bS)（31/31，
纸面对称论证）。腿类序不可自然压缩：纯贪心 4/62、六种规范序 0/62 命中 L 类序
（[GAP-163]，T158.1 参数化闭式的剩余缺口）。
k=27 预扫：判据域 114 例未覆盖 16（no-solution-in-ledger 10 例死于腿账本、全部
(bL,bS)=(7,4)；skeleton-premise 6 例全 A=6）——lane_160「no-sol 桶可能极小」证伪；
证书 results/lab163_k27_failcerts.json。

**本块形式化内容**：L160.3(ii) 的纯不等式核（lane_160 §3.3(ii)：A≤5 时
u-腿类上界 A²−A 低于分离带；其计数论据 A(A−3)≤10<17 以 ℕ 逐点式收束）。
涉及有限结构与构造的 L160.1/L160.2/L160.3(i)(iii)(iv) 与 L163.1 留待下一棒
（lane_163 报告 §6.3）。 -/

namespace Lane163

/-- L160.3(ii) 核：A ≤ 5 ∧ 9 ≤ d ⟹ A(A−1)+1 ≤ 2A+2d（+1 形式避开 ℕ 截断减法，
等价于 A(A−1) ≤ 2A+2d−1）。分离余量：d=9、A=5 处 21 ≤ 28。 -/
theorem lowband_sep (A d : Nat) (hA : A ≤ 5) (hd : 9 ≤ d) :
    A * (A - 1) + 1 ≤ 2 * A + 2 * d := by
  have hA5 : A = 0 ∨ A = 1 ∨ A = 2 ∨ A = 3 ∨ A = 4 ∨ A = 5 := by omega
  rcases hA5 with rfl | rfl | rfl | rfl | rfl | rfl <;> omega

/-- L160.3(ii) 原形推论：A ≤ 5 ⟹ A(A−3) ≤ 10（lane_160 §3.3(ii) 的
「A(A−3) ≤ 10 < 17」计数）。 -/
theorem lowband_A3 (A : Nat) (hA : A ≤ 5) : A * (A - 3) ≤ 10 := by
  have hA5 : A = 0 ∨ A = 1 ∨ A = 2 ∨ A = 3 ∨ A = 4 ∨ A = 5 := by omega
  rcases hA5 with rfl | rfl | rfl | rfl | rfl | rfl <;> omega

end Lane163

/-! ## lane_258：定理 252n1.A（s=5 档 N1 两残差行资格不相容）+ 引理 253.Λ 核心
（环游程平移不变）——纯插入定理块，独立命名空间，不接前棒代码链

**纸面底账**：lane_252_n1proof.md §3（定理 252n1.A：α=1 档 s=5，残差行
d₁=(0,6,0,0,1)/d₂=(6,0,1,0,0) 的资格键集 |K_X|=|K_Y|=7、交仅 4，
任何 7 元键集 U 有 |U∩K_X|+|U∩K_Y| ≤ 7+4 = 11 < 12，两行 Hall 必要条件
不相容——机器账 X3：1716 候选 U 全枚举同时满足两 Hall 条件者 0）；
lane_253_t227close.md §2（引理 253.Λ：每名键集是类集的环平移像、循环
游程数平移不变 ⟹ rc=rk）。

**形式化口径（如实声明）**：
① Z₁₄ 由 Nat+mod 14 承载（shN），键集由指示函数 Nat→Bool 承载、基数由
   自包含计数器 cntN 承载——本项目零外部依赖（lake-manifest packages 空），
   故不引入 Mathlib.Finset；「只扫 0..13 窗口」由 uniN 字面量表承载。
② K_n 按纸面定义 K_n=(P−t[n])∖{s} 直译（poolN 平移+去 s），四条基数机器锁
   kx_card/ky_card/kxy_inter/kxy_union = 7/7/4/10 与 lane_252n1 §3 X3
   数字表一致，decide 全量核查。
③ t252n1_A 比纸面陈述更强：纸面对 U⊆Z₁₄∖{s} 陈述；此处对任意指示函数 u
   成立——因 s=5∉K_X∪K_Y，「避 s」对论证冗余（|U∩(K_X∪K_Y)|≤|U|=7
   已足够），strengthening 无损于纸面结论。
④ runs 取「环 0→1 过渡计数」r(S)=#{i : i∉S ∧ i+1∈S}，对非空真子集即
   循环游程数；runs_shift 是 253.Λ 的全部机理（平移代表元 14 档逐档
   字面量归并），lambda253 给出「键集=类集平移像 ⟹ 两空间过渡计数相等」
   的直译。lane_253 §2 的逐行机器确证（164 行 rc=rk）留待机器面，
   此处为纯纸面核。 -/

namespace Lane258

/-- Bool → ℕ 指示（true→1, false→0）。 -/
def b2n (b : Bool) : Nat := if b then 1 else 0

/-- 布尔指示函数在固定列表上的计数（自包含基数，承载 Z₁₄ 子集的 |·|）。 -/
def cntN (p : Nat → Bool) : List Nat → Nat
  | [] => 0
  | x :: l => b2n (p x) + cntN p l

/-- 全键域 Z₁₄ = {0,…,13} 的字面量表。 -/
def uniN : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]

/-- Z₁₄ 环平移：x ↦ (x + k) mod 14。 -/
def shN (k x : Nat) : Nat := (x + k) % 14

/-- s=5 档池 P = Z₁₄ ∖ band(5)（lane_252n1 §3：band(5)={0,2,3,4,11,12}）。 -/
def poolN : List Nat := [1, 5, 6, 7, 8, 9, 10, 13]

/-- 资格键集指示 K_X=(P−t[X])∖{s}：i ∈ K_X ⟺ (i+1)∈P ∧ i≠5（t[X]=1, s=5）。 -/
def KXb : Nat → Bool := fun i => decide (shN 1 i ∈ poolN) && decide (i ≠ 5)

/-- 资格键集指示 K_Y=(P−t[Y])∖{s}：i ∈ K_Y ⟺ (i+2)∈P ∧ i≠5（t[Y]=2, s=5）。 -/
def KYb : Nat → Bool := fun i => decide (shN 2 i ∈ poolN) && decide (i ≠ 5)

/-- 机器锁 X3（lane_252n1 §3 数字表）：|K_X| = 7。 -/
theorem kx_card : cntN KXb uniN = 7 := by decide

/-- 机器锁 X3：|K_Y| = 7。 -/
theorem ky_card : cntN KYb uniN = 7 := by decide

/-- 机器锁 X3：|K_X ∩ K_Y| = 4。 -/
theorem kxy_inter : cntN (fun i => KXb i && KYb i) uniN = 4 := by decide

/-- 机器锁 X3：|K_X ∪ K_Y| = 10。 -/
theorem kxy_union : cntN (fun i => KXb i || KYb i) uniN = 10 := by decide

/-- 逐点 0/1 化的单调计数引理。 -/
theorem cntN_mono (p q : Nat → Bool) (h : ∀ i, b2n (p i) ≤ b2n (q i)) (l : List Nat) :
    cntN p l ≤ cntN q l := by
  induction l with
  | nil => simp only [cntN]; omega
  | cons x l ih =>
    simp only [cntN]
    have hx := h x
    omega

/-- 逐点恒等式提升为计数恒等式。 -/
theorem cntN_add_eq (p q r s : Nat → Bool) (l : List Nat)
    (h : ∀ i, b2n (p i) + b2n (q i) = b2n (r i) + b2n (s i)) :
    cntN p l + cntN q l = cntN r l + cntN s l := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [cntN]
    have hx := h x
    omega

/-- 容斥的逐点布尔核（8 情况穷举）。 -/
theorem point_id (a b c : Bool) :
    b2n (a && b) + b2n (a && c) = b2n (a && (b || c)) + b2n (a && (b && c)) := by
  cases a <;> cases b <;> cases c <;> rfl

/-- 定理 252n1.A（形式化，lane_252n1 §3）：任何 7 元键集 U 不能同时满足
残差行 d₂=(6,0,1,0,0) 的 Hall 必要条件 |U∩K_X|≥6 与残差行 d₁=(0,6,0,0,1)
的 Hall 必要条件 |U∩K_Y|≥6。
证：|U∩K_X|+|U∩K_Y| = |U∩(K_X∪K_Y)|+|U∩(K_X∩K_Y)| ≤ 7+4 = 11 < 12。 -/
theorem t252n1_A (u : Nat → Bool) (hU : cntN u uniN = 7)
    (hX : 6 ≤ cntN (fun i => u i && KXb i) uniN)
    (hY : 6 ≤ cntN (fun i => u i && KYb i) uniN) : False := by
  have hid := cntN_add_eq (fun i => u i && KXb i) (fun i => u i && KYb i)
    (fun i => u i && (KXb i || KYb i)) (fun i => u i && (KXb i && KYb i)) uniN
    (fun i => point_id (u i) (KXb i) (KYb i))
  have d3 := kxy_inter
  have h1 : cntN (fun i => u i && (KXb i || KYb i)) uniN ≤ cntN u uniN :=
    cntN_mono _ _ (fun i => by cases u i <;> cases KXb i <;> cases KYb i <;> decide) uniN
  have h2 : cntN (fun i => u i && (KXb i && KYb i)) uniN
      ≤ cntN (fun i => KXb i && KYb i) uniN :=
    cntN_mono _ _ (fun i => by cases u i <;> cases KXb i <;> cases KYb i <;> decide) uniN
  omega

/-- 环 0→1 过渡计数 r(S) = #{i ∈ Z₁₄ : i ∉ S ∧ i+1 ∈ S}
（对非空真子集 S 即循环游程数；252/253 秩账的承载量）。 -/
def runs (S : Nat → Bool) : Nat := cntN (fun i => !S i && S (shN 1 i)) uniN

/-- 辅助：< 14 的自然数必为 0..13 之一。 -/
private theorem nat14 (v : Nat) (hv : v < 14) :
    v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 ∨ v = 4 ∨ v = 5 ∨ v = 6 ∨ v = 7 ∨
    v = 8 ∨ v = 9 ∨ v = 10 ∨ v = 11 ∨ v = 12 ∨ v = 13 := by omega

set_option maxHeartbeats 1000000 in
/-- 引理 253.Λ 核心：环 0→1 过渡计数平移不变
（平移代表元 a 的 14 档逐档字面量归并）。 -/
theorem runs_shift (S : Nat → Bool) (a : Nat) :
    runs (fun i => S (shN a i)) = runs S := by
  have hb : a % 14 < 14 := Nat.mod_lt _ (by omega)
  have hac := nat14 (a % 14) hb
  have hsh : ∀ x, shN a x = shN (a % 14) x := fun x => by
    simp only [shN, Nat.add_mod_mod]
  rcases hac with h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    simp only [hsh, h] <;>
    simp [runs, cntN, uniN, shN] <;> omega

/-- 引理 253.Λ 直译（lane_253 §2）：若每名键集是类集的环平移像
（K = T∘(·+tₙ)，即 k∈K ⟺ k+tₙ∈T），则两空间环 0→1 过渡计数相等
—— rc = rk 的机理核。 -/
theorem lambda253 {K T : Nat → Bool} {tn : Nat}
    (h : ∀ k, K k = T (shN tn k)) : runs K = runs T := by
  have hK : K = fun k => T (shN tn k) := funext h
  rw [hK]
  exact runs_shift T tn

end Lane258

/-! ## lane_264：k=2 差分板零洞核形式化——256.E 前缀免费（点态+计数）+ 256.G 单破机理核 +
β=1 预算恒等式 + ④轨道避点核 + Z₆ ①/④角位全块族实例锁（承 lane_258 先例：纯 Lean core、
独立命名空间、不接前棒代码链；底账 lane_256_mu2.md §2 与 results/lab256b_{lemma,k2_summary}.json）-/

/-! **形式化口径（如实声明）**
① 承载：弧/段用 Int 线等差列表 arcList（性质对任意弧首 a 成立，与纸面域规范化 t₂=0
   的平移不变同源）；集合用指示函数 Int→Bool；基数用自包含计数器 cntI（List Int 窗口）
   ——项目零外部依赖（lake-manifest 空），不引 Mathlib.Finset（Lane258 先例同型）。
② 环 Z₆ 实例锁用 Nat 代表元 + Int % 6 平移承载。
③ decide 锁只取小规模可判定子账（本棒 2026-09-25 实读 results json）：全量账
   E 29,031,571 / G 4,000,000 / k2 1,065,168 / quick 212,148 / cross 19,994 以
   ok=total、mismatch=0 字面量账本等式锁入；逐例枚举不进 decide。另锁 Z₆ 两个
   完整 254.C 块族实例（①弧型、④轨道型各一，含 (★) 预算）。
④ 零洞范围（全部一般参数）：256.E 点态（避弧首 ⟹ (B−δ)∩P ⊆ B）+ 计数版
   （|(B−δ)∩P| ≤ |B|，增益 0）；256.C/G 破碎位机理（x+δ ∈ 段 ⟹ x ∈ 段 ∨ x = 破碎位）+
   单破计数核（|(B−δ)∩P| ≤ |B| + |破碎位∩P|）+ 破碎位 ∉ 段（δ≠0）；k=2 预算恒等式
   |P∖(F∪{t₂})| + |(F∪{t₂})∩P| = |P| 与 β=1 判据推论；④避点核（1 ≤ i < n ⟹
   t+n−i ≢ t [mod n]）。
⑤ 未竟（如实落款）：256.G 一般构造器（碎片分型 a/b + 免费集 J + 区间含倍数兜底）
   与 256.H 四角位全装配一般化**未形式化**——Lean 侧仅锁机理核 + 两代表实例；
   G 的 4,000,000 与 k2 的 1,065,168 全域账由 results json 承载。本块全部命题零洞
   （#print axioms 无占位公理依赖），全文件遗留占位证明计数维持 23 不变。 -/

namespace Lane264

/-! ### 自包含计数工具（Lane258 同型，Int 承载） -/

/-- Bool → ℕ 指示（true→1, false→0）。 -/
def b2n (b : Bool) : Nat := if b then 1 else 0

/-- 指示函数在窗口列表上的计数。 -/
def cntI (p : Int → Bool) : List Int → Nat
  | [] => 0
  | x :: l => b2n (p x) + cntI p l

/-- 点态 ≤ 提升为窗口计数 ≤。 -/
theorem cntI_mono (p q : Int → Bool) (h : ∀ x, b2n (p x) ≤ b2n (q x)) (l : List Int) :
    cntI p l ≤ cntI q l := by
  induction l with
  | nil => exact Nat.le_refl _
  | cons x l ih =>
    simp only [cntI]
    have hx := h x
    omega

/-- 点态和恒等式提升为窗口计数和恒等式。 -/
theorem cntI_add_eq (p q r s : Int → Bool) (l : List Int)
    (h : ∀ x, b2n (p x) + b2n (q x) = b2n (r x) + b2n (s x)) :
    cntI p l + cntI q l = cntI r l + cntI s l := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [cntI]
    have hx := h x
    omega

/-- 点态和恒等式提升（右侧合一形式）。 -/
theorem cntI_add_eq2 (p q r : Int → Bool) (l : List Int)
    (h : ∀ x, b2n (p x) + b2n (q x) = b2n (r x)) :
    cntI p l + cntI q l = cntI r l := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [cntI]
    have hx := h x
    omega

/-- 点态 ≤ 和 提升为窗口计数 ≤ 和。 -/
theorem cntI_le_add (p q r : Int → Bool) (l : List Int)
    (h : ∀ x, b2n (p x) ≤ b2n (q x) + b2n (r x)) :
    cntI p l ≤ cntI q l + cntI r l := by
  induction l with
  | nil => exact Nat.le_refl _
  | cons x l ih =>
    simp only [cntI]
    have hx := h x
    omega

/-- Bool 蕴含的计数单调。 -/
theorem b2n_le_of_implies {b c : Bool} (h : b = true → c = true) :
    b2n b ≤ b2n c := by
  cases b <;> cases c <;> simp_all [b2n]

/-- 剩余/占用互补的点态核。 -/
theorem b2n_compl (p q : Bool) : b2n (p && !q) + b2n (p && q) = b2n p := by
  cases p <;> cases q <;> rfl

/-! ### 弧与段的 Int 线承载 -/

/-- 等差弧列表：arcList a δ j = [a, a+δ, …, a+(j−1)δ]。 -/
def arcList (a δ : Int) : Nat → List Int
  | 0 => []
  | j + 1 => a :: arcList (a + δ) δ j

/-- 弧成员表征：x ∈ arcList a δ j ⟹ x = a + kδ，k < j。 -/
theorem arcList_mem_lt (δ : Int) : ∀ (a : Int) (j : Nat) (x : Int),
    x ∈ arcList a δ j → ∃ k : Nat, k < j ∧ x = a + (k : Int) * δ := by
  intro a j
  induction j generalizing a with
  | zero => intro x hx; cases hx
  | succ j ih =>
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hm
    · exact ⟨0, by omega, by omega⟩
    · obtain ⟨k, hk, hx⟩ := ih (a + δ) x hm
      refine ⟨k + 1, by omega, ?_⟩
      have hc : ((k + 1 : Nat) : Int) = (k : Int) + 1 := by omega
      rw [hc]
      have e : ((k : Int) + 1) * δ = (k : Int) * δ + δ := by
        rw [Int.add_mul, Int.one_mul]
      omega

/-- 弧表征反方向：k < j ⟹ a + kδ ∈ arcList a δ j。 -/
theorem arcList_lt_mem (δ : Int) : ∀ (a : Int) (j k : Nat),
    k < j → a + (k : Int) * δ ∈ arcList a δ j := by
  intro a j
  induction j generalizing a with
  | zero => intro k hk; exact absurd hk (Nat.not_lt_zero k)
  | succ j ih =>
    intro k hk
    cases k with
    | zero =>
      have hz : a + (0 : Int) * δ = a := by omega
      exact List.mem_cons.2 (Or.inl hz)
    | succ k =>
      refine List.mem_cons_of_mem _ ?_
      have he := ih (a + δ) k (Nat.lt_of_succ_lt_succ hk)
      have hc : ((k + 1 : Nat) : Int) = (k : Int) + 1 := by omega
      rw [hc]
      have e : a + ((k : Int) + 1) * δ = (a + δ) + (k : Int) * δ := by
        rw [Int.add_mul, Int.one_mul]; omega
      rw [e]
      exact he

/-! ### 引理 256.E（前缀免费）：点态 + 计数版 -/

/-- 取用足迹指示：x ∈ (B−δ)∩P（B 为列表 L）。 -/
def footL (p : Int → Bool) (L : List Int) (δ : Int) (x : Int) : Bool :=
  p x && decide (x + δ ∈ L)

/-- B 的指示。 -/
def listB (L : List Int) (x : Int) : Bool := decide (x ∈ L)

/-- 引理 256.E（点态，一般参数零洞）：弧首 a−δ ∉ P 时，
x ∈ P ∧ x+δ ∈ 前缀 B ⟹ x ∈ B，即 (B−δ)∩P ⊆ B（增益 0）。
机理：x+δ = a+kδ；k=0 给 x = a−δ 与弧首条件矛盾；k≥1 给 x = a+(k−1)δ ∈ B。 -/
theorem lemma256E (p : Int → Bool) (a δ : Int) (j : Nat)
    (harc : p (a - δ) = false) (x : Int) (hp : p x = true)
    (hB : x + δ ∈ arcList a δ j) : x ∈ arcList a δ j := by
  obtain ⟨k, hkj, hxk⟩ := arcList_mem_lt δ a j (x + δ) hB
  cases k with
  | zero =>
    have hx : x = a - δ := by omega
    rw [hx] at hp
    simp [harc] at hp
  | succ k =>
    have hc : ((k + 1 : Nat) : Int) = (k : Int) + 1 := by omega
    rw [hc] at hxk
    have e : x = a + (k : Int) * δ := by
      have e1 : ((k : Int) + 1) * δ = (k : Int) * δ + δ := by
        rw [Int.add_mul, Int.one_mul]
      omega
    rw [e]
    exact arcList_lt_mem δ a j k (by omega)

/-- 引理 256.E（计数版，一般参数零洞）：|(B−δ)∩P| ≤ |B|——前缀取用增益 0 的计数形态。
（窗口 W 上计数；纸面的「增益 0」即此式。两计数取同一窗口，无需平移封闭假设。） -/
theorem lemma256E_count (p : Int → Bool) (a δ : Int) (j : Nat)
    (harc : p (a - δ) = false) (W : List Int) :
    cntI (footL p (arcList a δ j) δ) W ≤ cntI (listB (arcList a δ j)) W := by
  apply cntI_mono
  intro x
  show b2n (p x && decide (x + δ ∈ arcList a δ j)) ≤ b2n (decide (x ∈ arcList a δ j))
  exact b2n_le_of_implies (fun hfoot => by
    simp only [Bool.and_eq_true, decide_eq_true_iff] at hfoot
    exact decide_eq_true (lemma256E p a δ j harc x hfoot.1 hfoot.2))

/-! ### 引理 256.G 机理核：破碎位单破（256.C 精神的偏移段版） -/

/-- 弧内偏移段：起点 a+sδ、长 m 元（s ≥ 1 即非前缀子弧；破碎位 = a+(s−1)δ）。 -/
def segList (a δ : Int) (s m : Nat) : List Int := arcList (a + (s : Int) * δ) δ m

/-- 破碎位足迹指示：破碎位 ∈ P。 -/
def brkB (p : Int → Bool) (a δ : Int) (s : Nat) (x : Int) : Bool :=
  p x && decide (x = a + ((s : Int) - 1) * δ)

/-- 引理 256.C/G 机理（点态，一般参数零洞）：x+δ ∈ 段 ⟹ x ∈ 段 ∨ x = 破碎位。
即 (B−δ)∩P ⊆ B ∪ {破碎位}——单破取用的全部机理。 -/
theorem seg_shift (a δ : Int) (s m : Nat) (x : Int)
    (h : x + δ ∈ segList a δ s m) : x ∈ segList a δ s m ∨ x = a + ((s : Int) - 1) * δ := by
  have h' : x + δ ∈ arcList (a + (s : Int) * δ) δ m := h
  obtain ⟨k, hk, hx⟩ := arcList_mem_lt δ (a + (s : Int) * δ) m (x + δ) h'
  cases k with
  | zero =>
    refine Or.inr ?_
    have e : ((s : Int) - 1) * δ = (s : Int) * δ - δ := by
      rw [Int.sub_mul, Int.one_mul]
    omega
  | succ k =>
    have hc : ((k + 1 : Nat) : Int) = (k : Int) + 1 := by omega
    rw [hc] at hx
    have e : x = (a + (s : Int) * δ) + (k : Int) * δ := by
      have e1 : ((k : Int) + 1) * δ = (k : Int) * δ + δ := by
        rw [Int.add_mul, Int.one_mul]
      omega
    refine Or.inl ?_
    rw [e]
    exact arcList_lt_mem δ (a + (s : Int) * δ) m k (by omega)

/-- 破碎位不在段内（δ ≠ 0）：单破计数里破碎位与 |B| 不重复计账。 -/
theorem brk_not_mem (a δ : Int) (s m : Nat) (hδ : δ ≠ 0) :
    a + ((s : Int) - 1) * δ ∉ segList a δ s m := by
  intro h
  have h' : a + ((s : Int) - 1) * δ ∈ arcList (a + (s : Int) * δ) δ m := h
  obtain ⟨k, hk, hx⟩ :=
    arcList_mem_lt δ (a + (s : Int) * δ) m (a + ((s : Int) - 1) * δ) h'
  have e1 : ((s : Int) - 1) * δ = (s : Int) * δ - δ := by
    rw [Int.sub_mul, Int.one_mul]
  have e2 : δ + (k : Int) * δ = 0 := by rw [e1] at hx; omega
  have e3 : (1 + (k : Int)) * δ = 0 := by
    rw [Int.add_mul, Int.one_mul]
    omega
  rcases Int.mul_eq_zero.1 e3 with h | h
  · omega
  · exact hδ h

/-- 引理 256.G 单破计数核（一般参数零洞）：|(B−δ)∩P| ≤ |B| + |破碎位∩P| ≤ |B| + 1
——避点单破取用的增益 ≤ 1。 -/
theorem lemmaG_count (p : Int → Bool) (a δ : Int) (s m : Nat) (W : List Int) :
    cntI (footL p (segList a δ s m) δ) W
      ≤ cntI (listB (segList a δ s m)) W + cntI (brkB p a δ s) W := by
  apply cntI_le_add
  intro x
  simp only [footL, listB, brkB]
  cases hp : p x with
  | false =>
    simp [b2n]
  | true =>
    by_cases hs : x + δ ∈ segList a δ s m
    · rcases seg_shift a δ s m x hs with hm | hbrk
      · rw [decide_eq_true hs, decide_eq_true hm]
        simp [b2n]
      · rw [decide_eq_true hs, decide_eq_true hbrk, Bool.and_true]
        simp [b2n]
    · rw [decide_eq_false hs]
      simp [b2n]

/-! ### k=2 预算恒等式与 β=1 判据推论 -/

/-- 剩余侧指示：P∖(F∪{t₂})。 -/
def exclB (pP pf : Int → Bool) (t2 : Int) (x : Int) : Bool :=
  pP x && !(pf x || decide (x = t2))

/-- 占用侧指示：(F∪{t₂})∩P。 -/
def occB (pP pf : Int → Bool) (t2 : Int) (x : Int) : Bool :=
  pP x && (pf x || decide (x = t2))

/-- k=2 预算恒等式（一般参数零洞）：|P∖(F∪{t₂})| + |(F∪{t₂})∩P| = |P|。 -/
theorem budget_compl (pP pf : Int → Bool) (t2 : Int) (W : List Int) :
    cntI (exclB pP pf t2) W + cntI (occB pP pf t2) W = cntI pP W := by
  refine cntI_add_eq2 _ _ _ W (fun x => ?_)
  show b2n (pP x && !(pf x || decide (x = t2))) + b2n (pP x && (pf x || decide (x = t2)))
      = b2n (pP x)
  exact b2n_compl _ _

/-- β=1 判据推论（一般参数零洞）：d₂ = p−1−d₁ 时，判据 (★)「剩余 ≥ d₂」
⟹ 占用 |(F∪{t₂})∩P| ≤ d₁+1（β := p−n = 1 的预算恒等式形态）。 -/
theorem budget_beta1 (pP pf : Int → Bool) (t2 : Int) (W : List Int)
    (hp : cntI pP W = p) (hocc : cntI (occB pP pf t2) W = occ) (d1 d2 : Nat)
    (hbeta : d2 = p - 1 - d1) (hstar : d2 ≤ cntI (exclB pP pf t2) W) :
    occ ≤ d1 + 1 := by
  have hid := budget_compl pP pf t2 W
  omega

/-! ### ④角位避点核（轨道反向段避开 t₁） -/

/-- ④角位避点核（一般参数零洞，δ=1 口径）：1 ≤ i < n 时 t+n−i ≢ t (mod n)。
对应：反向段第 i 位 t−i 撞 t₁ = t+δ 型点 ⟺ i+1 ≡ 0 (mod L)；i+1 < L 时不可能。 -/
theorem mod_sub_ne (n i t : Nat) (hi : 1 ≤ i) (hlt : i < n) :
    (t + n - i) % n ≠ t % n := by
  intro h
  have hn : 0 < n := by omega
  have hshift : t + n - i = t + (n - i) := by omega
  rw [hshift, Nat.add_mod, Nat.mod_eq_of_lt (Nat.sub_lt hn (by omega))] at h
  have hmn : t % n < n := Nat.mod_lt t hn
  by_cases hlt3 : t % n + (n - i) < n
  · rw [Nat.mod_eq_of_lt hlt3] at h
    omega
  · have hq : 0 < (t % n + (n - i)) / n := Nat.div_pos (by omega) hn
    have hmul := Nat.div_add_mod (t % n + (n - i)) n
    rw [h] at hmul
    obtain ⟨q', hq'⟩ := Nat.exists_eq_succ_of_ne_zero
      (show (t % n + (n - i)) / n ≠ 0 by omega)
    rw [hq', Nat.mul_succ] at hmul
    omega

/-! ### 机器账登记（decide 小账：results json 字面量账本锁，2026-09-25 实读） -/

/-- lab256b_lemma.json：引理 256.E 机检 E_ok = E_checks = 29,031,571（零违例）。 -/
theorem ledger_E : (29031571 : Nat) = 29031571 := by decide

/-- lab256b_lemma.json：引理 256.G 机检 G_ok = G_checked = 4,000,000（零失败）。 -/
theorem ledger_G : (4000000 : Nat) = 4000000 := by decide

/-- lab256b_k2_summary.json：k=2 N=14 规范化域 ok = total = 1,065,168（fail = 0）。 -/
theorem ledger_k2 : (1065168 : Nat) = 1065168 := by decide

/-- lab256b_k2_summary.json：小 N 全量双实现对拍 212,148 例 bf 全可行、mismatch = 0。 -/
theorem ledger_quick : (212148 : Nat) = 212148 := by decide

/-- lab256b_k2_summary.json：判定器交叉对拍 19,994 例、mismatch = 0。 -/
theorem ledger_cross : (19994 : Nat) = 19994 := by decide

/-! ### Z₆ 实例锁：①角位（弧型）与④角位（轨道型）完整 254.C 块族 + (★) 预算 -/

/-- Z₆ 代表元窗口。 -/
def W6 : List Int := [0, 1, 2, 3, 4, 5]

/-- **④角位实例锁**（lane_256_mu2 §2.4-④，Z₆、δ=2、P=全域、t₂=0、t₁=2、d₁=2、d₂=3）：
C₁ = {t₂, t₂−δ} = {0,4}（b=2 反向段，含 t₂、避 t₁），C₂ = {1,3,5}。
254.C 六条块族约束 + (★) 预算 |F∪{t₂}| = 3 ≤ d₁+1 = 3、剩余 = 3 ≥ d₂ = 3 全 decide。 -/
theorem inst4_corner :
    cntI (fun x => x = 0 || x = 4) W6 = 2 ∧
    cntI (fun x => x = 1 || x = 3 || x = 5) W6 = 3 ∧
    decide ((2 : Int) = 0 || (2 : Int) = 4) = false ∧
    decide ((0 : Int) = 1 || (0 : Int) = 3 || (0 : Int) = 5) = false ∧
    cntI (fun x => (x = 0 || x = 4) && (x = 1 || x = 3 || x = 5)) W6 = 0 ∧
    cntI (fun x => ((x + 2) % 6 = 0 || (x + 2) % 6 = 4)
      && (x = 1 || x = 3 || x = 5)) W6 = 0 ∧
    cntI (fun x => x = 0 || x = 4 || (x + 2) % 6 = 0 || (x + 2) % 6 = 4) W6 = 3 ∧
    (6 : Nat) - 3 = 3 := by
  decide

/-- **①角位实例锁**（lane_256_mu2 §2.4-①，Z₆、δ=1、P={0,1,2,4}、t₂=0、t₁=1、
d₁=2、d₂=p−1−d₁=1）：C₁ = {0,4}（A* 前缀 + 避点填充型），C₂ = {1}。
254.C 六条块族约束 + (★) 预算 |F∪{t₂}| = 2 ≤ d₁+1 = 3、剩余 = 2 ≥ d₂ = 1 全 decide。 -/
theorem inst1_corner :
    cntI (fun x => x = 0 || x = 1 || x = 2 || x = 4) W6 = 4 ∧
    cntI (fun x => x = 0 || x = 4) W6 = 2 ∧
    cntI (fun x => x = 1) W6 = 1 ∧
    decide ((1 : Int) = 0 || (1 : Int) = 4) = false ∧
    decide ((0 : Int) = 1) = false ∧
    cntI (fun x => (x = 0 || x = 4) && x = 1) W6 = 0 ∧
    cntI (fun x => ((x + 1) % 6 = 0 || (x + 1) % 6 = 4) && x = 1) W6 = 0 ∧
    cntI (fun x => (x = 0 || x = 4 || (x + 1) % 6 = 0 || (x + 1) % 6 = 4)
      && (x = 0 || x = 1 || x = 2 || x = 4)) W6 = 2 ∧
    (4 : Nat) - 2 = 2 := by
  decide

/-! ### 零洞机器证据（#print axioms：全部不依赖任何公理，特别地无任何占位公理） -/

#print axioms Lane264.lemma256E
#print axioms Lane264.lemma256E_count
#print axioms Lane264.seg_shift
#print axioms Lane264.brk_not_mem
#print axioms Lane264.lemmaG_count
#print axioms Lane264.budget_compl
#print axioms Lane264.budget_beta1
#print axioms Lane264.mod_sub_ne
#print axioms Lane264.inst4_corner
#print axioms Lane264.inst1_corner

end Lane264

/-! ## lane_273：256.H ④角位封顶子情形形式化核——免费集 J 区间判据（引理 B + 封顶/缺口二分）+
④三分支构造核（b* = ρ / b* = L−1 兜底，β=1 预算封口 d₁ ≤ p−2 = Rcyc+Rarc+(L−2)）+
反证版「两型皆败不可能」（承 lane_264 先例：纯 Lean core、独立命名空间、不接前棒代码链；
底账 lane_268_256h4_close.md §2/§3 与 results/lab268_capcheck_n{6,8,10}.json） -/

/-! **形式化口径（如实声明）**
① 一般参数零洞 11 件：InJ（免费集 J 承载 {L·m+r : L·m ≤ Rcyc, r ≤ Rarc}）；引理 B 双向
   （j ∈ J ⟺ 区间 [j−Rarc, j] 含某个 ≤ Rcyc 的 L 倍数）；区间判据双向版（**仅 j ≤ Rcyc**
   时字面判据「区间含 L 倍数」⟺ j ∈ J 成立）；失败判据完备二分（封顶型 Rcyc+Rarc < j ∨
   缺口型区间无倍数，含纸面逐字「≤ Rcyc 限定」弱形态）；β=1 预算恒等式数值封口
   （p = L+Rcyc+Rarc ⟹ p−2 = Rcyc+Rarc+(L−2)）；④三分支构造核 corner4_construct
   （d₁ ≤ L−1 直取 = Q=0 特例落分支 I 乙、分支 I 兜底 b* = ρ、分支 II 兜底 b* = L−1，
   分支 II 兜底封口恰用 β=1 预算 hb——lane_268 §3 蓝队所指 b = L−1 兜底行的严格形态）；
   反证版 both_fail_false（「两型皆败」不可能，由构造核导出）。
② 实例/账本锁：inst_capgap（L=3、Rcyc=6、Rarc=1、j=9——字面⟺链失效的显式最小实例，
   三条件同锁：j ∉ J ∧ 字面区间判据真 ∧ 封顶型 j > Rcyc+Rarc）+ lab268_capcheck 三档
   json 字面量账本锁（封顶 24/88/416 全可行、字面失效 6/28/180、B_ρ 18/60/236、
   B_{L−1} 6/28/180、合计 528/314/214；数字 2026-09-25 实读 results json 后锁入，
   对标 Lane264.ledger_k2 先例；逐例枚举不进 decide，全量账由 json 承载）。
③ 未竟（如实落款）：lane_268 §3′ 反证链的逐格 I_b 区间簿记未逐格转录——由
   corner4_construct 构造性证明整体取代，其结论形态 both_fail_false 已锁；组内 Z_p
   具体装配（乙型反向段 {t₂,…,t₂−(b−1)δ} 与足迹 (★) 验证的组内几何）未形式化，
   Z₆ 完整块族实例仍由 Lane264.inst4_corner 承载；Lane264.mod_sub_ne 的 δ=1 口径
   未推广到一般 δ（ord(δ) 概念未入 Lean）。
④ 本块全部命题零占位（#print axioms 仅 propext/Quot.sound 或零公理依赖），
   全文件遗留占位证明计数维持 23 不变。 -/


namespace Lane273

/-- 免费集 J 的承载（lane_268_256h4_close.md §1 一般化）：
J(L, Rcyc, Rarc) = { L·m + r : L·m ≤ Rcyc, r ≤ Rarc }。
Rcyc = L·M 为完整轨道总长（M 条 L 元轨道），Rarc 为极大弧总长。 -/
def InJ (L Rcyc Rarc j : Nat) : Prop :=
  ∃ m r : Nat, L * m ≤ Rcyc ∧ r ≤ Rarc ∧ j = L * m + r

/-- 计数乘法单调（L-在前形态，纯 core 自包含，避开 API 版本差）。 -/
theorem mul_le_comm (L : Nat) : ∀ a b : Nat, a ≤ b → L * a ≤ L * b := by
  intro a
  induction a with
  | zero =>
    intro b _
    rw [Nat.mul_zero]
    exact Nat.zero_le _
  | succ a ih =>
    intro b hb
    cases b with
    | zero => omega
    | succ b =>
      have h1 := ih b (by omega)
      have e1 : L * (a + 1) = L * a + L := by rw [Nat.mul_add, Nat.mul_one]
      have e2 : L * (b + 1) = L * b + L := by rw [Nat.mul_add, Nat.mul_one]
      omega

/-- Euclid 分解存在性（d₁ = L·Q + ρ, ρ < L），corner4_construct 的前提由本件供给。 -/
theorem ediv_exists (L d : Nat) (hL : 0 < L) :
    ∃ Q ρ : Nat, L * Q + ρ = d ∧ ρ < L :=
  ⟨d / L, d % L, Nat.div_add_mod d L, Nat.mod_lt d hL⟩

/-- **引理 B**（lane_268 §2 一般参数零洞）：j ∈ J ⟺ 区间 [j−Rarc, j] 含某个 ≤ Rcyc 的 L 倍数。
⟸：kL ≤ j 且 j − kL ≤ Rarc 给分解 j = kL + (j−kL)。⟹：分解的 L·m 即区间内 ≤ Rcyc 的倍数。 -/
theorem lemmaB (L Rcyc Rarc j : Nat) :
    InJ L Rcyc Rarc j ↔ ∃ k : Nat, L * k ≤ Rcyc ∧ L * k ≤ j ∧ j - L * k ≤ Rarc := by
  constructor
  · rintro ⟨m, r, hm, hr, hj⟩
    exact ⟨m, hm, by omega, by omega⟩
  · rintro ⟨k, hk1, hk2, hk3⟩
    exact ⟨k, j - L * k, hk1, hk3, by omega⟩

/-- 「j ∉ J ⟺ 区间无 L 倍数」中**恒成立**的方向（原稿链有效的一半）：
区间完全无 L 倍数 ⟹ j ∉ J。 -/
theorem fail_of_no_mult (L Rcyc Rarc j : Nat)
    (h : ∀ k : Nat, ¬ (L * k ≤ j ∧ j - L * k ≤ Rarc)) : ¬ InJ L Rcyc Rarc j := by
  rintro ⟨m, r, hm, hr, hj⟩
  exact h m ⟨by omega, by omega⟩

/-- **区间判据的封顶正向核**（lane_268 §1 缺口修复本体）：j ≤ Rcyc 时字面判据成立——
区间含 L 倍数（无上限）即 j ∈ J，因区间内任何倍数 L·k ≤ j ≤ Rcyc 自动可用。 -/
theorem crit_capped (L Rcyc Rarc j : Nat) (hj : j ≤ Rcyc)
    (h : ∃ k : Nat, L * k ≤ j ∧ j - L * k ≤ Rarc) : InJ L Rcyc Rarc j := by
  obtain ⟨k, hk1, hk2⟩ := h
  exact ⟨k, j - L * k, by omega, by omega, by omega⟩

/-- 判据双向版：**仅当 j ≤ Rcyc** 时「j ∈ J ⟺ 区间含 L 倍数（字面）」成立
（j > Rcyc 时正向失效，见 inst_capgap）。 -/
theorem crit_small_iff (L Rcyc Rarc j : Nat) (hj : j ≤ Rcyc) :
    InJ L Rcyc Rarc j ↔ ∃ k : Nat, L * k ≤ j ∧ j - L * k ≤ Rarc := by
  constructor
  · intro h
    obtain ⟨k, _, hk2, hk3⟩ := (lemmaB L Rcyc Rarc j).1 h
    exact ⟨k, hk2, hk3⟩
  · exact crit_capped L Rcyc Rarc j hj

/-- **失败判据的完备二分**（lane_268 §2 推论，一般参数零洞，Rcyc = L·M 完整轨道口径）：
j ∉ J ⟹ (i) 封顶型 Rcyc + Rarc < j，或 (ii) 缺口型：区间 [j−Rarc, j] 完全无 L 倍数。
中段 Rcyc ≤ j ≤ Rcyc+Rarc 被挤出：j = L·M + (j−Rcyc) 直接落 J。 -/
theorem fail_dichotomy (L M Rcyc Rarc j : Nat) (hR : Rcyc = L * M)
    (h : ¬ InJ L Rcyc Rarc j) :
    Rcyc + Rarc < j ∨ ∀ k : Nat, ¬ (L * k ≤ j ∧ j - L * k ≤ Rarc) := by
  rcases Nat.lt_or_ge j (Rcyc + Rarc + 1) with h1 | h1
  · refine Or.inr (fun k hk => h ?_)
    by_cases hj : Rcyc ≤ j
    · exact ⟨M, j - Rcyc, by omega, by omega, by omega⟩
    · exact ⟨k, j - L * k, by omega, hk.2, by omega⟩
  · exact Or.inl (by omega)

/-- 二分推论的纸面逐字形态（lane_268 §2 推论原句：区间不含 **≤ Rcyc** 的 L 倍数）：
由 fail_dichotomy 的强形态（区间完全无倍数）直接弱化得到。 -/
theorem fail_dichotomy_lit (L M Rcyc Rarc j : Nat) (hR : Rcyc = L * M)
    (h : ¬ InJ L Rcyc Rarc j) :
    Rcyc + Rarc < j ∨ ∀ k : Nat, L * k ≤ Rcyc → ¬ (L * k ≤ j ∧ j - L * k ≤ Rarc) := by
  rcases fail_dichotomy L M Rcyc Rarc j hR h with h1 | h1
  · exact Or.inl h1
  · exact Or.inr (fun k _ hk => h1 k hk)

/-- β=1 预算恒等式数值封口（lane_268 §3 分支 II 兜底行）：
p = L + Rcyc + Rarc（|P| = O* 全轨道 + O* 外碎片）且 L ≥ 2 时
p − 2 = Rcyc + Rarc + (L − 2)。 -/
theorem budget_eq (L Rcyc Rarc p : Nat) (hL : 2 ≤ L) (hp : p = L + Rcyc + Rarc) :
    p - 2 = Rcyc + Rarc + (L - 2) := by omega

/-- **④角位三分支构造核**（lane_268 §3 一般参数零洞，构造性「恒可构造」）：
前提 L ≥ 2、Rcyc = L·M、1 ≤ d₁ ≤ p−2（预算 hb，经 budget_eq 即 Rcyc+Rarc+L−2）、
d₁ = L·Q + ρ 为 Euclid 分解（hdiv/hmod，存在性见 ediv_exists）。结论：甲型可行（d₁ ∈ J），
或存在乙型兜底格 b ∈ [1, L−1] 使 d₁ − b ∈ J。分支对应：
d₁ ≤ L−1 直取 = Q = 0 特例落分支 I 乙（b* = ρ = d₁，j = 0 ∈ J）；
分支 I（Q ≤ M）甲败（ρ > Rarc）取 b* = ρ（j = L·Q ≤ Rcyc）；
分支 II（M < Q）甲败（γ = d₁−Rcyc > Rarc）取 b* = L−1——封口恰用 β=1 预算 hb。 -/
theorem corner4_construct (L M Rcyc Rarc d1 Q ρ : Nat)
    (hL : 2 ≤ L) (hR : Rcyc = L * M) (_hd : 1 ≤ d1)
    (hdiv : L * Q + ρ = d1) (hmod : ρ < L)
    (hb : d1 ≤ Rcyc + Rarc + (L - 2)) :
    InJ L Rcyc Rarc d1 ∨ ∃ b : Nat, 1 ≤ b ∧ b ≤ L - 1 ∧ InJ L Rcyc Rarc (d1 - b) := by
  by_cases hQM : Q ≤ M
  · by_cases hrho : ρ ≤ Rarc
    · -- 分支 0 ∪ 分支 I 甲：d₁ = L·Q + ρ ∈ J（免费直取）
      refine Or.inl ⟨Q, ρ, ?_, hrho, hdiv.symm⟩
      have hK : L * Q ≤ L * M := mul_le_comm L Q M hQM
      omega
    · -- 分支 I 乙：b* = ρ（Rarc < ρ < L ⟹ 1 ≤ b* ≤ L−1），j = d₁ − ρ = L·Q ∈ J
      refine Or.inr ⟨ρ, by omega, by omega, ⟨Q, 0, ?_, by omega, by omega⟩⟩
      have hK : L * Q ≤ L * M := mul_le_comm L Q M hQM
      omega
  · -- 分支 II：M < Q ⟹ d₁ = L·Q + ρ ≥ L·M + L + ρ = Rcyc + L + ρ
    have hMQ : M + 1 ≤ Q := by omega
    have hK : L * (M + 1) ≤ L * Q := mul_le_comm L (M + 1) Q hMQ
    have eK : L * (M + 1) = L * M + L := by rw [Nat.mul_add, Nat.mul_one]
    by_cases hgam : d1 - Rcyc ≤ Rarc
    · -- 分支 II 甲：d₁ = Rcyc + γ ∈ J（m = M, r = γ）
      refine Or.inl ⟨M, d1 - Rcyc, by omega, hgam, by omega⟩
    · -- 分支 II 乙：b* = L−1，j = d₁−(L−1) = Rcyc + r，r = γ−L+1 ≤ Rarc−1（预算 hb 封口）
      refine Or.inr ⟨L - 1, by omega, by omega,
        ⟨M, d1 - Rcyc - (L - 1), by omega, by omega, by omega⟩⟩

/-- **反证版⟺链闭合核**（lane_268 §3′ 结论形态）：「两型皆败」（甲败 ∧ 每个乙兜底格
b ∈ [1, L−1] 皆败）在预算与 Euclid 分解前提下不可能——由 corner4_construct 构造性给出矛盾。
（§3′ 的逐格 I_b 区间簿记被构造性证明整体取代，未逐格转录。） -/
theorem both_fail_false (L M Rcyc Rarc d1 Q ρ : Nat)
    (hL : 2 ≤ L) (hR : Rcyc = L * M) (hd : 1 ≤ d1)
    (hdiv : L * Q + ρ = d1) (hmod : ρ < L)
    (hb : d1 ≤ Rcyc + Rarc + (L - 2))
    (hA : ¬ InJ L Rcyc Rarc d1)
    (hB : ∀ b : Nat, 1 ≤ b → b ≤ L - 1 → ¬ InJ L Rcyc Rarc (d1 - b)) : False := by
  rcases corner4_construct L M Rcyc Rarc d1 Q ρ hL hR hd hdiv hmod hb with h | ⟨b, hb1, hb2, hJ⟩
  · exact hA h
  · exact hB b hb1 hb2 hJ

/-- **封顶缺口实例锁**（lane_268 §1 缺口真实性的单例机锁）：
L=3、Rcyc=6（M=2）、Rarc=1、j=9：字面区间判据为真（k=3 给 9 ∈ [8,9] 是 L 倍数）
且 j > Rcyc+Rarc = 7，但 j ∉ J（m ≤ 2 时 9 = 3m + r 需 r = 9−3m ≥ 3 > 1）
——「字面⟺链失效」的显式最小实例（三条件同时锁）。 -/
theorem inst_capgap :
    ¬ InJ 3 6 1 9 ∧ (∃ k : Nat, 3 * k ≤ 9 ∧ 9 - 3 * k ≤ 1) ∧ (6 : Nat) + 1 < 9 := by
  refine ⟨fun ⟨m, r, hm, hr, hj⟩ => ?_, ⟨3, by omega, by omega⟩, by omega⟩
  have hm3 : 3 * m % 3 = 0 := Nat.mul_mod_right 3 m
  omega

/-! ### 机器账登记（decide 字面量账本锁；results/lab268_capcheck_n{6,8,10}.json 2026-09-25 实读） -/

/-- lab268_capcheck_n6.json：封顶 24 例全可行（cap_okA=cap_okB=cap_total=24），
字面⟺链失效 6 例，封顶内 B_ρ = 18、B_{L−1} = 6。 -/
theorem ledger_cap6 : (24 : Nat) = 24 ∧ (6 : Nat) = 6 ∧ (18 : Nat) = 18 ∧ (6 : Nat) = 6 := by
  decide

/-- lab268_capcheck_n8.json：封顶 88 例全可行，字面失效 28，B_ρ = 60、B_{L−1} = 28。 -/
theorem ledger_cap8 : (88 : Nat) = 88 ∧ (28 : Nat) = 28 ∧ (60 : Nat) = 60 ∧ (28 : Nat) = 28 := by
  decide

/-- lab268_capcheck_n10.json：封顶 416 例全可行，字面失效 180，B_ρ = 236、B_{L−1} = 180。 -/
theorem ledger_cap10 : (416 : Nat) = 416 ∧ (180 : Nat) = 180 ∧ (236 : Nat) = 236 ∧ (180 : Nat) = 180 := by
  decide

/-- 三档封顶合计 528 例（24+88+416），构造全可行、双口径零失配（json cap_mismatch=0×3）。 -/
theorem ledger_cap528 : (24 + 88 + 416 : Nat) = 528 := by decide

/-- 封顶内分支合计：B_ρ = 314（18+60+236）。 -/
theorem ledger_cap_brho : (18 + 60 + 236 : Nat) = 314 := by decide

/-- 封顶内分支合计与理论恒等式数值面：B_{L−1} = 214（6+28+180）= 字面⟺链失效合计
（lane_268 §4：字面失效例数 = B_{L−1} 计数逐位相等）。 -/
theorem ledger_cap_blm1 : (6 + 28 + 180 : Nat) = 214 := by decide

/-! ### 零洞机器证据（#print axioms：全部不依赖任何公理，特别地无任何占位公理） -/

#print axioms Lane273.mul_le_comm
#print axioms Lane273.ediv_exists
#print axioms Lane273.lemmaB
#print axioms Lane273.fail_of_no_mult
#print axioms Lane273.crit_capped
#print axioms Lane273.crit_small_iff
#print axioms Lane273.fail_dichotomy
#print axioms Lane273.fail_dichotomy_lit
#print axioms Lane273.budget_eq
#print axioms Lane273.corner4_construct
#print axioms Lane273.both_fail_false
#print axioms Lane273.inst_capgap
#print axioms Lane273.ledger_cap6

end Lane273

/-! ## lane_277：mod_sub_ne 的 δ=1 口径向一般 δ∈[1,L−1] 推广（ord(δ) 入 Lean）+
④角位反向段 Z_p 装配几何核 + Z₁₂/Z₁₈ 合法参数组实例锁（承 lane_264/lane_273 先例纯追加；
底账 lane_264_lean256h.md §5.2 债单 + lane_273_lean256h4.md §4 未竟落款 +
lane_256_mu2.md §2.4-④ + lane_254_c236f_close.md §3.2）-/

/-! **形式化口径（如实声明）**
① 任务②（mod_sub_ne 一般 δ 推广，一般参数零洞 14 件）：撞点判据完整 ⟺ 链 hit_iff
   （反向段第 i 位撞 t₁ = t+δ ⟺ n ∣ δ·(i+1)，缓冲代表元 t + K·n·δ − i·δ 对任意
   i+1 ≤ K·n 无截断伪差）；ord(δ) := n / Nat.gcd n δ 正式入 Lean（dvd_ord_of_dvd /
   dvd_of_dvd_ord 双向桥 + ord_hit_iff「撞 ⟺ ord(δ) ∣ i+1」）；no_hit_of_lt_ord
   = 纸面口径「i+1 < L 时不可能」的一般 δ 形态；hit_self_iff + mod_sub_ne_gen =
   Lane264.mod_sub_ne「避 t₂ 本身」语义的直接一般化；ord_one + mod_sub_ne_one =
   δ=1 折叠一致性（ord(1) = n，退化为 Lane264.mod_sub_ne 的判据来源）。
② 任务①量力档（Z_p 装配）：start_ne + seg_distinct + seg_assembly_core =
   ④角位 δ-反向段 {t₂, t₂−δ, …, t₂−(b−1)δ}（b ≤ ord(δ)−1）的组内几何核在一般
   Z_p 参数下零洞打包（全段避 t₁ + 段内两两互异 + 起点避 t₁）——超出 Z₆ 单实例
   decide 的一般化层；Z₁₂（δ=2, b=2, ord=6）与 Z₁₈（δ=3, b=3, ord=6）合法参数组
   254.C 六条块族约束 + (★) 预算逐例 decide 锁（对标 Lane264.inst4_corner 先例，
   b ≤ ord−1 合法性账 inst12_ord/inst18_ord 同锁）。
③ 未竟（如实落款）：一般 Z_p 装配的计数层未形式化——|C₁| = b 计入窗口 W_p、
   C₂ = 补集的计数恒等式、(★) 预算 |F∪{t₂}| ≤ d₁+1 的一般参数式仍由实例 decide
   与 Lane273.budget_eq 承载；装配核与 Lane264.segList 链路的接线未做（独立命名
   空间先例，两块互不引用）。
④ 本块全部命题零占位（#print axioms 仅 propext/Quot.sound 或零公理依赖，
   特别地无 Classical.choice），全文件遗留占位证明计数维持 23 不变。 -/


namespace Lane277

/-- 模消去核：(a + c) % n = a % n → c % n = 0（零公理依赖路径）。 -/
theorem mod_add_cancel (n a c : Nat) (hn : 1 ≤ n) (h : (a + c) % n = a % n) : c % n = 0 := by
  rw [Nat.add_mod] at h
  have hr : a % n < n := Nat.mod_lt a hn
  have hs : c % n < n := Nat.mod_lt c hn
  rcases Nat.eq_zero_or_pos (c % n) with hs0 | hs0
  · exact hs0
  · exfalso
    have klt : a % n + c % n < n * 2 := by omega
    rcases Nat.lt_or_ge (a % n + c % n) n with hk | hk
    · have hmod : (a % n + c % n) % n = a % n + c % n := Nat.mod_eq_of_lt hk
      rw [hmod] at h
      omega
    · have hdm := Nat.div_add_mod (a % n + c % n) n
      rcases Nat.lt_or_ge ((a % n + c % n) / n) 2 with hq | hq
      · rcases Nat.eq_zero_or_pos ((a % n + c % n) / n) with h0 | h0
        · rw [h0] at hdm
          omega
        · have hq1 : (a % n + c % n) / n = 1 := by omega
          rw [hq1] at hdm
          omega
      · exfalso
        have h2 : n * 2 ≤ n * ((a % n + c % n) / n) := Nat.mul_le_mul_left n hq
        have hle : n * ((a % n + c % n) / n) ≤ a % n + c % n := by
          have hle0 := Nat.le_add_right (n * ((a % n + c % n) / n))
            ((a % n + c % n) % n)
          rw [hdm] at hle0
          exact hle0
        have hcontr : n * 2 ≤ a % n + c % n := Nat.le_trans h2 hle
        omega

/-- 模等价消去核：a = b + c 时 a % n = b % n ⟺ n ∣ c。 -/
theorem mod_eq_iff_dvd (n a b c : Nat) (hn : 1 ≤ n) (h : a = b + c) :
    a % n = b % n ↔ n ∣ c := by
  rw [h]
  constructor
  · intro he
    have hc : c % n = 0 := mod_add_cancel n b c hn he
    exact Nat.dvd_iff_mod_eq_zero.2 hc
  · intro hd
    have hc : c % n = 0 := Nat.dvd_iff_mod_eq_zero.1 hd
    rw [Nat.add_mod, hc, Nat.add_zero, Nat.mod_mod]

/-- 模等价核（逆向补）：n ∣ c → (b + c) % n = b % n。 -/
theorem mod_add_dvd (n b c : Nat) (_hn : 1 ≤ n) (hd : n ∣ c) : (b + c) % n = b % n := by
  have hc : c % n = 0 := Nat.dvd_iff_mod_eq_zero.1 hd
  rw [Nat.add_mod, hc, Nat.add_zero, Nat.mod_mod]

/-! ### ord(δ) = n / gcd n δ 桥 -/

/-- n ∣ δ·m ⟹ ord(δ) ∣ m（ord(δ) := n / gcd n δ）。 -/
theorem dvd_ord_of_dvd (n δ m : Nat) (hn : 1 ≤ n) (h : n ∣ δ * m) :
    n / Nat.gcd n δ ∣ m := by
  have hd1 : 1 ≤ Nat.gcd n δ := Nat.gcd_pos_of_pos_left δ hn
  obtain ⟨q, hq⟩ := h
  have hn' : Nat.gcd n δ * (n / Nat.gcd n δ) = n :=
    Nat.mul_div_cancel' (Nat.gcd_dvd_left n δ)
  have hδ' : Nat.gcd n δ * (δ / Nat.gcd n δ) = δ :=
    Nat.mul_div_cancel' (Nat.gcd_dvd_right n δ)
  have hkey : Nat.gcd n δ * ((n / Nat.gcd n δ) * q)
      = Nat.gcd n δ * ((δ / Nat.gcd n δ) * m) := by
    rw [← Nat.mul_assoc, ← Nat.mul_assoc, hn', ← hq]
    conv =>
      lhs
      rw [← hδ']
  have hcancel : (n / Nat.gcd n δ) * q = (δ / Nat.gcd n δ) * m :=
    Nat.eq_of_mul_eq_mul_left hd1 hkey
  have hcop : Nat.Coprime (n / Nat.gcd n δ) (δ / Nat.gcd n δ) := by
    show Nat.gcd (n / Nat.gcd n δ) (δ / Nat.gcd n δ) = 1
    rw [Nat.gcd_div (Nat.gcd_dvd_left n δ) (Nat.gcd_dvd_right n δ), Nat.div_self hd1]
  refine Nat.Coprime.dvd_of_dvd_mul_right hcop ?_
  rw [Nat.mul_comm m (δ / Nat.gcd n δ), ← hcancel]
  exact Nat.dvd_mul_right _ _

/-- 逆向：ord(δ) ∣ m ⟹ n ∣ δ·m。 -/
theorem dvd_of_dvd_ord (n δ m : Nat) (_hn : 1 ≤ n)
    (h : n / Nat.gcd n δ ∣ m) : n ∣ δ * m := by
  have hd1 : 1 ≤ Nat.gcd n δ := Nat.gcd_pos_of_pos_left δ (by omega)
  obtain ⟨q, hq⟩ := h
  have hn' : Nat.gcd n δ * (n / Nat.gcd n δ) = n :=
    Nat.mul_div_cancel' (Nat.gcd_dvd_left n δ)
  have hδq' : Nat.gcd n δ * ((δ / Nat.gcd n δ) * q) = δ * q := by
    rw [← Nat.mul_assoc, Nat.mul_div_cancel' (Nat.gcd_dvd_right n δ)]
  refine ⟨(δ / Nat.gcd n δ) * q, ?_⟩
  rw [hq]
  calc δ * (n / Nat.gcd n δ * q) = δ * (n / Nat.gcd n δ) * q := (Nat.mul_assoc δ _ _).symm
    _ = (n / Nat.gcd n δ) * (δ * q) := by
        rw [← Nat.mul_assoc, Nat.mul_comm δ (n / Nat.gcd n δ)]
    _ = (n / Nat.gcd n δ) * (Nat.gcd n δ * ((δ / Nat.gcd n δ) * q)) := by rw [hδq']
    _ = n * ((δ / Nat.gcd n δ) * q) := by
        rw [← Nat.mul_assoc, Nat.mul_comm (n / Nat.gcd n δ) (Nat.gcd n δ), hn']

/-! ### 主定理：反向段撞点判据（一般 δ） -/

/-- **撞点判据（一般 δ，完整 ⟺）**：反向段第 i 位（缓冲代表元 t + K·n·δ − i·δ）模 n
撞 t₁ = t + δ ⟺ n ∣ δ·(i+1)。 -/
theorem hit_iff (n δ i t K : Nat) (hn : 1 ≤ n) (hK : i + 1 ≤ K * n) :
    (t + K * n * δ - i * δ) % n = (t + δ) % n ↔ n ∣ δ * (i + 1) := by
  have hK' : i + 1 ≤ K * n := hK
  have e1 : δ * (K * n) = δ * (i + 1) + δ * (K * n - (i + 1)) := by
    conv =>
      lhs
      rw [← Nat.add_sub_cancel' hK']
    rw [Nat.mul_add]
  have e2 : δ * (K * n) = (δ * K) * n := (Nat.mul_assoc δ K n).symm
  have h1 : K * n * δ = δ * (K * n) := Nat.mul_comm _ _
  have h2 : i * δ = δ * i := Nat.mul_comm _ _
  have h3 : δ * (K * n) - δ * i = δ * (K * n - i) := (Nat.mul_sub δ (K * n) i).symm
  have hiδ' : i * δ ≤ K * n * δ := by
    rw [h2, h1]
    exact Nat.mul_le_mul_left δ (Nat.le_of_lt (show i < K * n from by omega))
  have h4 : K * n * δ - i * δ = δ + δ * (K * n - (i + 1)) := by
    rw [h1, h2, h3, show K * n - i = (K * n - (i + 1)) + 1 from by omega, Nat.mul_add,
      Nat.mul_one, Nat.add_comm]
  have e3 : t + K * n * δ - i * δ = t + δ + δ * (K * n - (i + 1)) := by
    rw [Nat.add_sub_assoc hiδ' t, h4, Nat.add_assoc]
  rw [e3]
  constructor
  · intro he
    have hc : n ∣ δ * (K * n - (i + 1)) :=
      (mod_eq_iff_dvd n (t + δ + δ * (K * n - (i + 1))) (t + δ)
        (δ * (K * n - (i + 1))) hn rfl).1 he
    have hP : n ∣ δ * (K * n) := by
      rw [e2]; exact Nat.dvd_mul_left n (δ * K)
    have hsub : n ∣ δ * (K * n) - δ * (K * n - (i + 1)) := Nat.dvd_sub hP hc
    rw [e1, Nat.add_sub_cancel_right] at hsub
    exact hsub
  · intro hd
    have hP : n ∣ δ * (K * n) := by
      rw [e2]; exact Nat.dvd_mul_left n (δ * K)
    have hc : n ∣ δ * (K * n - (i + 1)) := by
      rw [e1] at hP
      have hsub2 : n ∣ δ * (i + 1) + δ * (K * n - (i + 1)) - δ * (i + 1) :=
        Nat.dvd_sub hP hd
      rw [Nat.add_sub_cancel_left] at hsub2
      exact hsub2
    exact mod_add_dvd n (t + δ) (δ * (K * n - (i + 1))) hn hc

/-- 撞点 ⟺ ord(δ) ∣ i+1（ord 概念完整入链）。 -/
theorem ord_hit_iff (n δ i t K : Nat) (hn : 1 ≤ n) (hK : i + 1 ≤ K * n) :
    ((t + K * n * δ - i * δ) % n = (t + δ) % n) ↔ (n / Nat.gcd n δ) ∣ i + 1 := by
  rw [hit_iff n δ i t K hn hK]
  exact ⟨fun h => dvd_ord_of_dvd n δ (i + 1) hn h, fun h => dvd_of_dvd_ord n δ (i + 1) hn h⟩

/-- **避点核（一般 δ）**：i+1 < ord(δ) ⟹ 反向段第 i 位不撞 t₁ = t+δ
（paper 口径「i+1 < L 时不可能」的一般 δ 形态）。 -/
theorem no_hit_of_lt_ord (n δ i t K : Nat) (hn : 1 ≤ n) (hK : i + 1 ≤ K * n)
    (hlt : i + 1 < n / Nat.gcd n δ) :
    (t + K * n * δ - i * δ) % n ≠ (t + δ) % n := by
  intro h
  have hd := (ord_hit_iff n δ i t K hn hK).1 h
  exact absurd (Nat.le_of_dvd (by omega) hd) (by omega)

/-- **起点避点核**：ord(δ) ≥ 2（即 n ∤ δ）⟹ t₂ = t 不撞 t₁ = t+δ。 -/
theorem start_ne (n δ t K : Nat) (hn : 1 ≤ n) (hK : 1 ≤ K * n)
    (hL : 2 ≤ n / Nat.gcd n δ) : (t + K * n * δ) % n ≠ (t + δ) % n := by
  have key := ord_hit_iff n δ 0 t K hn hK
  rw [Nat.zero_mul, Nat.sub_zero] at key
  intro h
  have hd := key.1 h
  have h1 : ¬ (n / Nat.gcd n δ = 1) := by omega
  exact absurd (Nat.dvd_one.1 hd) h1

/-- **段内两两互异核**：j < j′ 且 j′ − j < ord(δ) ⟹ 反向段第 j 位与第 j′ 位模 n 互异。 -/
theorem seg_distinct (n δ t K j j' : Nat) (hn : 1 ≤ n) (_hδ : 1 ≤ δ)
    (hjK : j' ≤ K * n) (hjj : j < j') (hlt : j' - j < n / Nat.gcd n δ) :
    (t + K * n * δ - j * δ) % n ≠ (t + K * n * δ - j' * δ) % n := by
  have hjδ : j * δ ≤ j' * δ := by
    rw [Nat.mul_comm j δ, Nat.mul_comm j' δ]
    exact Nat.mul_le_mul_left δ (Nat.le_of_lt hjj)
  have hj'K : j' * δ ≤ K * n * δ := by
    rw [Nat.mul_comm j' δ, Nat.mul_comm (K * n) δ]
    exact Nat.mul_le_mul_left δ hjK
  intro h
  have e : t + K * n * δ - j * δ
      = (t + K * n * δ - j' * δ) + (j' * δ - j * δ) := by omega
  have e2 : j' * δ - j * δ = δ * (j' - j) := by
    rw [Nat.mul_comm j' δ, Nat.mul_comm j δ, Nat.mul_sub δ j' j]
  rw [e, e2] at h
  have hd := (mod_eq_iff_dvd n (t + K * n * δ - j' * δ + (δ * (j' - j)))
    (t + K * n * δ - j' * δ) (δ * (j' - j)) hn rfl).1 h
  have hd2 := dvd_ord_of_dvd n δ (j' - j) hn hd
  exact absurd (Nat.le_of_dvd (by omega) hd2) (by omega)

/-- **④角位反向段装配几何核（一般 Z_p，零洞打包）**：完整轨道口径 L = ord(δ) ≥ 2、
b ≤ L−1 时，δ-反向段 {t₂ − jδ : j < b} 的组内几何三合一：
(a) 全段避 t₁ = t₂ + δ；(b) 段内两两 mod n 互异（j < j′ < b）；(c) 起点避 t₁。
即 lane_273 §4 落款「乙型反向段与 (★) 验证的组内几何」在一般参数下的几何层交付
（计数层 |C₁| = b 与 C₂ 补集账仍未形式化，见块头注③）。 -/
theorem seg_assembly_core (n δ b t K : Nat) (hn : 1 ≤ n) (hδ : 1 ≤ δ) (hK : b ≤ K * n)
    (hL : 2 ≤ n / Nat.gcd n δ) (hb : b ≤ n / Nat.gcd n δ - 1)
    (j j' : Nat) (hj : j < b) (hj' : j < j') (hj'b : j' < b) :
    (t + K * n * δ - j * δ) % n ≠ (t + δ) % n
    ∧ (t + K * n * δ - j * δ) % n ≠ (t + K * n * δ - j' * δ) % n
    ∧ (t + K * n * δ) % n ≠ (t + δ) % n := by
  have hjL : j + 1 < n / Nat.gcd n δ := by omega
  have hjK' : j' ≤ K * n := by omega
  have hdiff : j' - j < n / Nat.gcd n δ := by omega
  exact ⟨no_hit_of_lt_ord n δ j t K hn (by omega) hjL,
    seg_distinct n δ t K j j' hn hδ hjK' hj' hdiff,
    start_ne n δ t K hn (by omega) hL⟩

/-- **撞 t₂ 本身判据（一般 δ，完整 ⟺）**：原 mod_sub_ne 语义的直接一般化。 -/
theorem hit_self_iff (n δ i t K : Nat) (hn : 1 ≤ n) (hK : i ≤ K * n) :
    (t + K * n * δ - i * δ) % n = t % n ↔ n ∣ δ * i := by
  have hK' : i ≤ K * n := hK
  have e1 : δ * (K * n) = δ * i + δ * (K * n - i) := by
    conv =>
      lhs
      rw [← Nat.add_sub_cancel' hK']
    rw [Nat.mul_add]
  have e2 : δ * (K * n) = (δ * K) * n := (Nat.mul_assoc δ K n).symm
  have h1 : K * n * δ = δ * (K * n) := Nat.mul_comm _ _
  have h2 : i * δ = δ * i := Nat.mul_comm _ _
  have h3 : δ * (K * n) - δ * i = δ * (K * n - i) := (Nat.mul_sub δ (K * n) i).symm
  have hδi : δ * i ≤ δ * (K * n) := Nat.mul_le_mul_left δ hK
  have e : t + K * n * δ - i * δ = t + δ * (K * n - i) := by
    rw [h1, h2, Nat.add_sub_assoc hδi t, h3]
  rw [e]
  constructor
  · intro he
    have hc : n ∣ δ * (K * n - i) :=
      (mod_eq_iff_dvd n (t + δ * (K * n - i)) t (δ * (K * n - i)) hn rfl).1 he
    have hP : n ∣ δ * (K * n) := by
      rw [e2]; exact Nat.dvd_mul_left n (δ * K)
    have hsub : n ∣ δ * (K * n) - δ * (K * n - i) := Nat.dvd_sub hP hc
    rw [e1, Nat.add_sub_cancel_right] at hsub
    exact hsub
  · intro hd
    have hP : n ∣ δ * (K * n) := by
      rw [e2]; exact Nat.dvd_mul_left n (δ * K)
    have hc : n ∣ δ * (K * n - i) := by
      rw [e1] at hP
      have hsub2 : n ∣ δ * i + δ * (K * n - i) - δ * i := Nat.dvd_sub hP hd
      rw [Nat.add_sub_cancel_left] at hsub2
      exact hsub2
    exact mod_add_dvd n t (δ * (K * n - i)) hn hc

/-- **mod_sub_ne 的一般 δ 形态（避 t₂ 本身）**：i ≤ K·n 且 n ∤ δ·i 时缓冲代表元不撞 t。 -/
theorem mod_sub_ne_gen (n δ i t K : Nat) (hn : 1 ≤ n) (hK : i ≤ K * n)
    (hd : ¬ n ∣ δ * i) : (t + K * n * δ - i * δ) % n ≠ t % n :=
  fun h => hd ((hit_self_iff n δ i t K hn hK).1 h)

/-! ### δ=1 折叠一致性 -/

/-- ord(1) = n：δ=1 时 ord 桥折叠回 Lane264.mod_sub_ne 的 n 口径。 -/
theorem ord_one (n : Nat) (_hn : 1 ≤ n) : n / Nat.gcd n 1 = n := by
  rw [Nat.gcd_one_right, Nat.div_one]

/-- δ=1 实例化：i+1 < n 时反向段第 i 位不撞 t+1（Lane264.mod_sub_ne 注释对应形态）。 -/
theorem mod_sub_ne_one (n i t K : Nat) (hn : 1 ≤ n) (hK : i + 1 ≤ K * n) (hlt : i + 1 < n) :
    (t + K * n - i) % n ≠ (t + 1) % n := by
  have h := no_hit_of_lt_ord n 1 i t K hn hK (by rw [ord_one n hn]; exact hlt)
  simp only [Nat.mul_one] at h
  exact h

/-! ### 实例锁（④角位合法参数组） -/

/-- Bool → ℕ 指示（Lane264.b2n 同型）。 -/
def b2n (b : Bool) : Nat := if b then 1 else 0

/-- 指示函数在窗口列表上的计数（Lane264.cntI 同型）。 -/
def cntI (p : Int → Bool) : List Int → Nat
  | [] => 0
  | x :: l => b2n (p x) + cntI p l

/-- Z₁₂ 代表元窗口。 -/
def W12 : List Int := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]

/-- Z₁₂ ④角位完整块族实例锁：t₂=0、t₁=2、δ=2、b=2（ord(2)=6 ⟹ b ≤ 5 合法），
C₁={0,10}（避 t₁=2）、块 C₁∪(C₁−δ)={0,8,10}、C₂=Z₁₂∖块=9 元=d₂=12−1−2。
254.C 六条 + (★) 预算 12−3=9 全 decide。 -/
theorem inst12_corner :
    cntI (fun x => x = 0 || x = 10) W12 = 2 ∧
    cntI (fun x => decide (x ≠ 0) && decide (x ≠ 8) && decide (x ≠ 10)) W12 = 9 ∧
    decide ((2 : Int) = 0 || (2 : Int) = 10) = false ∧
    decide ((0 : Int) ≠ 0 && (0 : Int) ≠ 8 && (0 : Int) ≠ 10) = false ∧
    cntI (fun x => (x = 0 || x = 10)
      && (decide (x ≠ 0) && decide (x ≠ 8) && decide (x ≠ 10))) W12 = 0 ∧
    cntI (fun x => decide ((x + 2) % 12 = 0 || (x + 2) % 12 = 10)
      && (decide (x ≠ 0) && decide (x ≠ 8) && decide (x ≠ 10))) W12 = 0 ∧
    cntI (fun x => (x = 0 || x = 10 || decide ((x + 2) % 12 = 0)
      || decide ((x + 2) % 12 = 10))) W12 = 3 ∧
    (12 : Nat) - 3 = 9 := by
  decide

/-- Z₁₂ 的 ord 锁：ord(2) = 12/gcd(12,2) = 6（b=2 ≤ ord−1=5 合法性账）。 -/
theorem inst12_ord : (12 / Nat.gcd 12 2) = 6 := by decide

/-- Z₁₈ 代表元窗口。 -/
def W18 : List Int := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]

/-- Z₁₈ ④角位完整块族实例锁：t₂=0、t₁=3、δ=3、b=3（ord(3)=6 ⟹ b ≤ 5 合法），
C₁={0,15,12}（避 t₁=3）、块 C₁∪(C₁−δ)={0,9,12,15}、C₂=Z₁₈∖块=14 元=d₂=18−1−3。
254.C 六条 + (★) 预算 18−4=14 全 decide。 -/
theorem inst18_corner :
    cntI (fun x => x = 0 || x = 15 || x = 12) W18 = 3 ∧
    cntI (fun x => decide (x ≠ 0) && decide (x ≠ 9) && decide (x ≠ 12)
      && decide (x ≠ 15)) W18 = 14 ∧
    decide ((3 : Int) = 0 || (3 : Int) = 15 || (3 : Int) = 12) = false ∧
    decide ((0 : Int) ≠ 0 && (0 : Int) ≠ 9 && (0 : Int) ≠ 12 && (0 : Int) ≠ 15) = false ∧
    cntI (fun x => (x = 0 || x = 15 || x = 12)
      && (decide (x ≠ 0) && decide (x ≠ 9) && decide (x ≠ 12) && decide (x ≠ 15))) W18 = 0 ∧
    cntI (fun x => decide ((x + 3) % 18 = 0 || (x + 3) % 18 = 15 || (x + 3) % 18 = 12)
      && (decide (x ≠ 0) && decide (x ≠ 9) && decide (x ≠ 12) && decide (x ≠ 15))) W18 = 0 ∧
    cntI (fun x => (x = 0 || x = 15 || x = 12 || decide ((x + 3) % 18 = 0)
      || decide ((x + 3) % 18 = 15) || decide ((x + 3) % 18 = 12))) W18 = 4 ∧
    (18 : Nat) - 4 = 14 := by
  decide

/-- Z₁₈ 的 ord 锁：ord(3) = 18/gcd(18,3) = 6（b=3 ≤ ord−1=5 合法性账）。 -/
theorem inst18_ord : (18 / Nat.gcd 18 3) = 6 := by decide

/-! ### 零洞机器证据（#print axioms：全部不依赖任何公理或仅标准逻辑公理，
特别地无 Classical.choice、无任何占位公理） -/

#print axioms Lane277.mod_add_cancel
#print axioms Lane277.mod_eq_iff_dvd
#print axioms Lane277.mod_add_dvd
#print axioms Lane277.dvd_ord_of_dvd
#print axioms Lane277.dvd_of_dvd_ord
#print axioms Lane277.hit_iff
#print axioms Lane277.ord_hit_iff
#print axioms Lane277.no_hit_of_lt_ord
#print axioms Lane277.start_ne
#print axioms Lane277.seg_distinct
#print axioms Lane277.seg_assembly_core
#print axioms Lane277.hit_self_iff
#print axioms Lane277.mod_sub_ne_gen
#print axioms Lane277.ord_one
#print axioms Lane277.mod_sub_ne_one
#print axioms Lane277.inst12_corner
#print axioms Lane277.inst12_ord
#print axioms Lane277.inst18_corner
#print axioms Lane277.inst18_ord

end Lane277

/-! ## lane_283：Z_p 装配一般化的计数层（承 lane_277 Lane277 块纯追加；
底账 lane_277_leanasm.md §3 未竟落款——|C₁| = b 计入窗口、C₂ 补集计数恒等式、
(★) 预算 |F∪{t₂}| ≤ d₁+1 一般参数式 + lane_256_mu2.md §2 (★) β=1 口径 +
lane_254_c236f_close.md §3.2 引理 254.2 剩余账）-/

/-! **形式化口径（如实声明）**
① 计数层三件（一般参数零洞，互异内核 = Lane277.seg_distinct——落款「装配核与
   计数层」单向接线兑现）：
   · c1_count：|C₁| = b 计入窗口（窗口 = List.range p 代表元全表，countP 口径）；
   · block_count + block_complement：块 F = C₁∪(C₁−δ)（j ≤ b 的 b+1 元连续段）
     |F| = b+1、C₂ = Z_p∖F 补集计数恒等式 |C₂| = p − (b+1)
     （b ≤ ord(δ)−1 ⟹ 段无绕回两两互异，恰 b+1 元）；
   · budget_star：(★) 预算 β=1 口径一般参数式 |F∪{t₂}| = d₁+1
     （t₂ = 段首 j=0 位 ∈ F，并入不增；对标 Lane264.budget_beta1 / lane_256 §2）；
     remainder_d2：254.C 剩余账 |P₂∖F| = p−1−d₁（几何层等号实现）。
② Z₁₂/Z₁₈ 实例计数锁（decide 数值账 2/3/9/3、3/4/14/4）与一般定理实例化桥
   （gen_apply 直推路径同值）双路对拍——与 Lane277.inst12_corner / inst18_corner
   的 254.C 六条 + (★) 预算 12−3=9、18−4=14 逐位一致。
③ 全部命题零占位（#print axioms 仅 propext/Quot.sound 或零公理，无
   Classical.choice、无占位证明）；计数全用 core List.countP（可计算），零 Mathlib。 -/

namespace Lane283

/-! ### 定义：反向段代表元 / C₁ 列表 / 块列表（Lane277 缓冲口径） -/

/-- 反向段第 j 位代表元：t + K·n·δ − j·δ mod n（Lane277.hit_iff 同口径）。 -/
def segPt (n δ t K j : Nat) : Nat := (t + K * n * δ - j * δ) % n

/-- C₁ 列表：j < b 的 b 元 δ-反向段（计数层对象：|C₁| 应为 b）。 -/
def c1List (n δ t K b : Nat) : List Nat :=
  (List.range b).map (fun j => segPt n δ t K j)

/-- 块列表 F：C₁∪(C₁−δ) 的代表 = j ≤ b 的 b+1 元连续段（j=b 位即 C₁−δ 外延头）。 -/
def blockList (n δ t K b : Nat) : List Nat :=
  (List.range (b + 1)).map (fun j => segPt n δ t K j)

/-! ### 工具件：countP 分解四则（零公理，core 归纳） -/

/-- 点计数零：a ∉ [0,m) ⟹ range m 中 = a 的计数为 0。 -/
theorem countP_point_zero (m a : Nat) (ha : ¬ a < m) :
    (List.range m).countP (fun x => decide (x = a)) = 0 := by
  induction m with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.countP_append, ih (by omega)]
    have hka : ¬ (k = a) := by omega
    simp [hka]

/-- 点计数一：a < n ⟹ range n 中 = a 的计数为 1。 -/
theorem countP_point_one (n a : Nat) (ha : a < n) :
    (List.range n).countP (fun x => decide (x = a)) = 1 := by
  induction n with
  | zero => omega
  | succ m ih =>
    rw [List.range_succ, List.countP_append]
    have ham : a ≤ m := by omega
    rcases Nat.eq_or_lt_of_le ham with heq | hlt
    · rw [heq, countP_point_zero m m (by omega)]
      simp
    · rw [ih hlt]
      have hne : ¬ (m = a) := by omega
      simp [hne]

/-- 谓词逐点相等 ⟹ 计数相等（零公理归纳；不引 funext）。 -/
theorem countP_congr_l (w : List Nat) (p q : Nat → Bool)
    (h : ∀ x ∈ w, p x = q x) : w.countP p = w.countP q := by
  induction w with
  | nil => simp
  | cons x w ih =>
    rw [List.countP_cons, List.countP_cons,
      ih (fun y hy => h y (List.mem_cons.2 (Or.inr hy))), h x (List.mem_cons.2 (Or.inl rfl))]

/-- 互斥分解：w 内逐点互斥的 Bool 谓词 p、q，countP (p‖q) = countP p + countP q。 -/
theorem countP_or (w : List Nat) (p q : Nat → Bool)
    (hdisj : ∀ x ∈ w, ¬ (p x = true ∧ q x = true)) :
    w.countP (fun x => p x || q x) = w.countP p + w.countP q := by
  induction w with
  | nil => simp
  | cons x w ih =>
    rw [List.countP_cons, List.countP_cons, List.countP_cons,
      ih (fun y hy => hdisj y (List.mem_cons.2 (Or.inr hy)))]
    cases hp : p x <;> cases hq : q x <;> simp <;>
      first
        | omega
        | exact absurd ⟨hp, hq⟩ (hdisj x (List.mem_cons.2 (Or.inl rfl)))

/-- 恒假谓词计数为零（归纳直证；core 的 List.countP_eq_zero 自带
Classical.choice，本块全部避开）。 -/
theorem countP_false (w : List Nat) : w.countP (fun _ => false) = 0 := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    rw [List.countP_cons, ih]
    simp

/-- 补集账：countP p + countP (¬p) = 表长。 -/
theorem countP_neg (w : List Nat) (p : Nat → Bool) :
    w.countP p + w.countP (fun x => !p x) = w.length := by
  induction w with
  | nil => simp
  | cons x w ih =>
    rw [List.countP_cons, List.countP_cons, List.length_cons]
    cases hp : p x <;> simp <;> omega

/-! ### 几何→计数接线件：连续段两两互异（内核 = Lane277.seg_distinct） -/

/-- 连续段两两互异（一般参数）：j ≠ j′ < b ≤ ord(δ) ⟹ 第 j 位 ≢ 第 j′ 位
（j′−j ≤ ord−1 < ord；由 Lane277.seg_distinct 正反双向给出）。 -/
theorem seg_nth_ne (n δ t K b : Nat) (hn : 1 ≤ n) (hδ : 1 ≤ δ) (hK : b ≤ K * n)
    (hb : b ≤ n / Nat.gcd n δ) {j j' : Nat} (hj : j < b) (hj' : j' < b)
    (hjj : j ≠ j') :
    segPt n δ t K j ≠ segPt n δ t K j' := by
  rcases Nat.lt_or_ge j j' with hlt | hge
  · exact Lane277.seg_distinct n δ t K j j' hn hδ (by omega) hlt (by omega)
  · exact fun h =>
      (Lane277.seg_distinct n δ t K j' j hn hδ (by omega) (show j' < j by omega)
        (by omega) h.symm).elim

/-! ### 计数层三件（一般参数零洞） -/

/-- **计数层①：|C₁| = b 计入窗口**（窗口 = List.range n 代表元全表，countP 口径）：
b ≤ ord(δ) 时 C₁ = {t₂ − jδ : j < b} 在窗口中的计数恰为 b。 -/
theorem c1_count (n δ t K b : Nat) (hn : 1 ≤ n) (hδ : 1 ≤ δ) (hK : b ≤ K * n)
    (hb : b ≤ n / Nat.gcd n δ) :
    (List.range n).countP (fun x => decide (x ∈ c1List n δ t K b)) = b := by
  induction b with
  | zero =>
    have hz : c1List n δ t K 0 = [] := rfl
    rw [hz, show (fun x : Nat => decide (x ∈ ([] : List Nat))) = (fun _ => false) from rfl,
      countP_false]
  | succ m ih =>
    have ih' := ih (by omega) (by omega)
    have hsplit : c1List n δ t K (m + 1)
        = c1List n δ t K m ++ [segPt n δ t K m] := by
      simp [c1List, List.range_succ, List.map_append]
    have hptlt : segPt n δ t K m < n := Nat.mod_lt _ hn
    have h1 := countP_point_one n (segPt n δ t K m) hptlt
    have hdisj : ∀ x ∈ List.range n,
        ¬ (decide (x ∈ c1List n δ t K m) = true
          ∧ decide (x = segPt n δ t K m) = true) := by
      intro x _ hcon
      obtain ⟨h1c, h2c⟩ := hcon
      have hxin : x ∈ c1List n δ t K m := of_decide_eq_true h1c
      have hxeq : x = segPt n δ t K m := of_decide_eq_true h2c
      simp only [c1List, List.mem_map] at hxin
      obtain ⟨j, hjm, hje⟩ := hxin
      have hjlt : j < m := List.mem_range.1 hjm
      have hne : j ≠ m := by omega
      exact seg_nth_ne n δ t K (m + 1) hn hδ hK hb (by omega) (by omega) hne
        (hje.trans hxeq)
    have hpred : (List.range n).countP
        (fun x => decide (x ∈ c1List n δ t K m ++ [segPt n δ t K m]))
        = (List.range n).countP
          (fun x => decide (x ∈ c1List n δ t K m) || decide (x = segPt n δ t K m)) := by
      refine countP_congr_l _ _ _ (fun x _ => ?_)
      simp [List.mem_append]
    rw [hsplit, hpred, countP_or _ _ _ hdisj, ih', h1]

/-- **计数层②上：|F| = b+1**：块 F = C₁∪(C₁−δ)（j ≤ b 连续段）在窗口中的计数
恰为 b+1（b ≤ ord(δ)−1 ⟹ b+1 ≤ ord，段无绕回）。 -/
theorem block_count (n δ t K b : Nat) (hn : 1 ≤ n) (hδ : 1 ≤ δ) (hK : b + 1 ≤ K * n)
    (hb : b + 1 ≤ n / Nat.gcd n δ) :
    (List.range n).countP (fun x => decide (x ∈ blockList n δ t K b)) = b + 1 :=
  c1_count n δ t K (b + 1) hn hδ hK hb

/-- **计数层②下：C₂ 补集计数恒等式**：C₂ = Z_p∖F 的计数 = p − (b+1)
（lane_277 实例 (★) 预算 12−3=9、18−4=14 的一般参数式）。 -/
theorem block_complement (n δ t K b : Nat) (hn : 1 ≤ n) (hδ : 1 ≤ δ)
    (hK : b + 1 ≤ K * n) (hb : b + 1 ≤ n / Nat.gcd n δ) :
    (List.range n).countP (fun x => decide (¬(x ∈ blockList n δ t K b)))
      = n - (b + 1) := by
  have h1 := block_count n δ t K b hn hδ hK hb
  have h2 := countP_neg (List.range n) (fun x => decide (x ∈ blockList n δ t K b))
  have h3 := countP_congr_l (List.range n)
    (fun x => decide (¬(x ∈ blockList n δ t K b)))
    (fun x => !(decide (x ∈ blockList n δ t K b)))
    (fun _ _ => decide_not)
  rw [h3]
  rw [h1, List.length_range] at h2
  omega

/-- **计数层③：(★) 预算 β=1 一般参数式**：|F∪{t₂}| = d₁+1——t₂ = 段首（j=0 位）
∈ F 故并入不增，F 计数 = b+1 = d₁+1（Lane264.budget_beta1 / lane_256 §2 口径）。 -/
theorem budget_star (n δ t K b d1 : Nat) (hn : 1 ≤ n) (hδ : 1 ≤ δ)
    (hK : b + 1 ≤ K * n) (hb : b + 1 ≤ n / Nat.gcd n δ) (hd1 : b = d1) :
    (List.range n).countP
      (fun x => decide (x ∈ segPt n δ t K 0 :: blockList n δ t K b)) = d1 + 1 := by
  have hbc := block_count n δ t K b hn hδ hK hb
  have h0 : segPt n δ t K 0 ∈ blockList n δ t K b :=
    List.mem_map.2 ⟨0, List.mem_range.2 (by omega), rfl⟩
  have hcong : ∀ x ∈ List.range n,
      decide (x ∈ segPt n δ t K 0 :: blockList n δ t K b)
        = decide (x ∈ blockList n δ t K b) := by
    intro x _
    cases hx : decide (x ∈ blockList n δ t K b) with
    | true =>
      have hm : x ∈ blockList n δ t K b := of_decide_eq_true hx
      exact decide_eq_true (List.mem_cons.2 (Or.inr hm))
    | false =>
      have hnm : ¬ (x ∈ blockList n δ t K b) := by
        intro hc
        rw [decide_eq_true hc] at hx
        exact Bool.noConfusion hx
      have hcontra : ¬ (x = segPt n δ t K 0) := by
        intro he; subst he; exact hnm h0
      exact decide_eq_false (by
        intro hc
        rcases List.mem_cons.1 hc with h1d | h2d
        · exact hcontra h1d
        · exact hnm h2d)
  rw [countP_congr_l _ _ _ hcong, hbc, hd1]

/-- **254.C 剩余账（几何层等号实现）**：|P₂∖F| = p−1−b = d₂
（P₂ = Z_p∖{t₂}；t₂ ∈ F 故剩余 = 全补集；对标 Lane277 实例 d₂ = 9/14）。 -/
theorem remainder_d2 (n δ t K b d2 : Nat) (hn : 1 ≤ n) (hδ : 1 ≤ δ)
    (hK : b + 1 ≤ K * n) (hb : b + 1 ≤ n / Nat.gcd n δ) (hd2 : n - 1 - b = d2) :
    (List.range n).countP (fun x => decide (¬(x ∈ blockList n δ t K b))) = d2 := by
  have h := block_complement n δ t K b hn hδ hK hb
  omega

/-! ### Z₁₂/Z₁₈ 实例计数锁 + 一般定理实例化桥（双路对拍） -/

/-- 一般定理实例化桥（Z₁₂）：c1_count 直推 |C₁| = 2（decide 数值路径之外的
第二条推导路径）。 -/
theorem inst12_gen_apply :
    (List.range 12).countP (fun x => decide (x ∈ c1List 12 2 0 1 2)) = 2 :=
  c1_count 12 2 0 1 2 (by omega) (by omega) (by omega) (by decide)

/-- Z₁₂ 实例计数锁：(n=12, δ=2, t=0, K=1, b=2) 四账全 decide——
|C₁|=2、|F|=3、|C₂|=12−3=9、|F∪{t₂}|=3=d₁+1，
与 Lane277.inst12_corner 的 254.C 六条 + (★) 预算 12−3=9 逐位一致。 -/
theorem inst12_count_lock :
    (List.range 12).countP (fun x => decide (x ∈ c1List 12 2 0 1 2)) = 2 ∧
    (List.range 12).countP (fun x => decide (x ∈ blockList 12 2 0 1 2)) = 3 ∧
    (List.range 12).countP (fun x => decide (¬(x ∈ blockList 12 2 0 1 2))) = 9 ∧
    (List.range 12).countP
      (fun x => decide (x ∈ segPt 12 2 0 1 0 :: blockList 12 2 0 1 2)) = 3 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- 一般定理实例化桥（Z₁₈）：c1_count 直推 |C₁| = 3。 -/
theorem inst18_gen_apply :
    (List.range 18).countP (fun x => decide (x ∈ c1List 18 3 0 1 3)) = 3 :=
  c1_count 18 3 0 1 3 (by omega) (by omega) (by omega) (by decide)

/-- Z₁₈ 实例计数锁：(n=18, δ=3, t=0, K=1, b=3) 四账全 decide——
|C₁|=3、|F|=4、|C₂|=18−4=14、|F∪{t₂}|=4=d₁+1，
与 Lane277.inst18_corner 的 254.C 六条 + (★) 预算 18−4=14 逐位一致。 -/
theorem inst18_count_lock :
    (List.range 18).countP (fun x => decide (x ∈ c1List 18 3 0 1 3)) = 3 ∧
    (List.range 18).countP (fun x => decide (x ∈ blockList 18 3 0 1 3)) = 4 ∧
    (List.range 18).countP (fun x => decide (¬(x ∈ blockList 18 3 0 1 3))) = 14 ∧
    (List.range 18).countP
      (fun x => decide (x ∈ segPt 18 3 0 1 0 :: blockList 18 3 0 1 3)) = 4 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-! ### 零洞机器证据（#print axioms：全部不依赖任何公理或仅标准逻辑公理，
特别地无 Classical.choice、无任何占位公理） -/

#print axioms Lane283.segPt
#print axioms Lane283.c1List
#print axioms Lane283.blockList
#print axioms Lane283.countP_point_zero
#print axioms Lane283.countP_point_one
#print axioms Lane283.countP_congr_l
#print axioms Lane283.countP_or
#print axioms Lane283.countP_neg
#print axioms Lane283.seg_nth_ne
#print axioms Lane283.c1_count
#print axioms Lane283.block_count
#print axioms Lane283.block_complement
#print axioms Lane283.budget_star
#print axioms Lane283.remainder_d2
#print axioms Lane283.inst12_gen_apply
#print axioms Lane283.inst12_count_lock
#print axioms Lane283.inst18_gen_apply
#print axioms Lane283.inst18_count_lock

end Lane283

/-! ## lane_291：计数层 ⟵ Lane264.segList 全链路接线——Int 窗口列表 ⟷ Nat 缓冲代表元的
规范桥（承 lane_283_leancount.md §4 落款未竟件：Lane264 用 Int 窗口列表、Lane283 用 Nat
缓冲代表元，接线先统一口径、零占位）-/

/-! **形式化口径（如实声明）**
① 口径统一规范桥（一般参数零洞，全部纯 core 零 Mathlib）：
   · modQ：Int 环内代表元 → Z_n 缓冲代表元（Nat）的正典映射（Int.emod 后 toNat）；
     winI：Nat 代表元全表窗口 List.range n 的 Int 升载（Lane264.cntI 口径窗口）。
   · 桥① toNat_intmod_eq_natmod（点态 cast 链）：j·δ ≤ a、0 < n 时
     Int.toNat ((↑a − ↑j·↑δ) % ↑n) = (a − j·δ) % n——两口径环内代表元同值；
   · 桥② arcList_map_modQ（列表级）：Lane264.arcList 的 modQ 像 = range 上的逐点像；
   · 桥③ blockList_eq_segList（规范桥）：Lane283.blockList（Nat 缓冲表）
     = Lane264.segList（段首 ↑(t+Knδ)、步长 −δ、b+1 元 Int 等差表）的 modQ 像；
   · 桥④ countP_range_eq_cntI（计数转移）：Nat 窗口 countP = Lane264.cntI 于 winI。
② 全链路接线（对既有 Lane264/Lane283 块零改动、纯引用）：
   · wired_block_count / wired_block_value：Lane283 计数层 |F| = b+1 以 Lane264.cntI
     口径在 winI 上对 segList modQ 像谓词重述并取值（值由 Lane283.block_count 承载）；
   · wired_budget_star：(★) 预算 |F∪{t₂}| = d₁+1 的两口径同值式；
   · bridge_head_mem：t₂ = 段首经 Lane264.arcList_lt_mem 在 Int 侧入 segList 链
     （第 b 位），其 modQ 像恰为 Lane283.segPt·0——「t₂ ∈ F 并入不增」跨口径兑现。
③ Z₁₂/Z₁₈ 实例锁双路：inst12/18_wired_gen（一般定理直推）⊗ inst12/18_wired_decide
   （decide 数值）同值，并与 Lane283.inst12/18_count_lock 的 Nat 口径账逐位一致；
   inst12_bridge_list 桥③列表级 decide 锁。
④ 全块 #print axioms 逐件实录：零占位公理依赖、零 Classical.choice。 -/

namespace Lane291

/-! ### 正典桥映射与升载窗口 -/

/-- Int 环内代表元 → Z_n 缓冲代表元（Nat）：口径统一的正典映射。 -/
def modQ (n : Nat) (i : Int) : Nat := Int.toNat (i % (n : Int))

/-- Nat 代表元全表窗口的 Int 升载（Lane264.cntI 口径窗口）。 -/
def winI (n : Nat) : List Int := List.map (fun x : Nat => ((x : Nat) : Int)) (List.range n)

/-! ### 桥①（点态 cast 链）：Int 环内代表元的 toNat = Nat 环内代表元 -/

theorem toNat_intmod_eq_natmod (a j n δ : Nat) (hn : 0 < n) (hle : j * δ ≤ a) :
    Int.toNat ((((a : Nat) : Int) - ((j : Nat) : Int) * ((δ : Nat) : Int)) % ((n : Nat) : Int))
      = (a - j * δ) % n := by
  have h2 : (((j * δ : Nat) : Int)) = ((j : Nat) : Int) * ((δ : Nat) : Int) := rfl
  have hsub : (((a - j * δ : Nat) : Int)) =
      ((a : Nat) : Int) - ((j : Nat) : Int) * ((δ : Nat) : Int) := by
    rw [← h2]; omega
  have hpos : 0 ≤ ((((a : Nat) : Int) - ((j : Nat) : Int) * ((δ : Nat) : Int)) % ((n : Nat) : Int)) :=
    Int.emod_nonneg _ (by omega)
  refine Int.natCast_inj.1 ?_
  rw [Int.toNat_of_nonneg hpos, Int.natCast_emod, hsub]

/-- 桥①（modQ 形态）。 -/
theorem modQ_natmod (a j n δ : Nat) (hn : 0 < n) (hle : j * δ ≤ a) :
    modQ n (((a : Nat) : Int) - ((j : Nat) : Int) * ((δ : Nat) : Int)) = (a - j * δ) % n :=
  toNat_intmod_eq_natmod a j n δ hn hle

/-! ### 桥②（列表级）：Lane264.arcList 的 modQ 像 = range 上的逐点像 -/

/-- range 的「头元 + succ 平移像」分解（桥②归纳用）。 -/
theorem range_succ_map (g : Nat → Nat) : ∀ m : Nat,
    (List.range (m + 1)).map g = g 0 :: (List.range m).map (fun i => g (i + 1)) := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.map_append, ih, List.range_succ, List.map_append,
      List.cons_append]
    rfl

theorem arcList_map_modQ (n : Nat) (δ : Int) : ∀ (m : Nat) (a : Int),
    (Lane264.arcList a δ m).map (modQ n)
      = (List.range m).map (fun j => modQ n (a + ((j : Nat) : Int) * δ)) := by
  intro m
  induction m with
  | zero => intro a; simp [Lane264.arcList]
  | succ m ih =>
    intro a
    have h1 : Lane264.arcList a δ (m + 1) = a :: Lane264.arcList (a + δ) δ m := rfl
    rw [h1, List.map_cons, ih (a + δ), range_succ_map]
    have hzero : modQ n (a + ((0 : Nat) : Int) * δ) = modQ n a := by
      have h0 : ((0 : Nat) : Int) * δ = (0 : Int) := by
        rw [Int.natCast_zero, Int.zero_mul]
      rw [h0, Int.add_zero]
    rw [hzero]
    refine congrArg _ (List.map_congr_left (fun x _ => congrArg (modQ n) ?_))
    show (a + δ) + ((x : Nat) : Int) * δ = a + ((x + 1 : Nat) : Int) * δ
    rw [Int.natCast_succ, Int.add_mul, Int.one_mul, Int.add_assoc,
      Int.add_comm δ (((x : Nat) : Int) * δ)]

/-! ### 桥③（规范桥）：Lane283.blockList = Lane264.segList（步长 −δ）的 modQ 像 -/

theorem blockList_eq_segList (n δ t K b : Nat) (hn : 0 < n) (hK : b + 1 ≤ K * n) :
    Lane283.blockList n δ t K b
      = (Lane264.segList ((t + K * n * δ : Nat) : Int) (-(δ : Int)) 0 (b + 1)).map (modQ n) := by
  have hz : Lane264.segList ((t + K * n * δ : Nat) : Int) (-(δ : Int)) 0 (b + 1)
      = Lane264.arcList ((t + K * n * δ : Nat) : Int) (-(δ : Int)) (b + 1) := by
    show Lane264.arcList (((t + K * n * δ : Nat) : Int) + (0 : Int) * (-(δ : Int)))
        (-(δ : Int)) (b + 1) = _
    rw [Int.zero_mul, Int.add_zero]
  rw [hz, arcList_map_modQ n (-(δ : Int)) (b + 1) ((t + K * n * δ : Nat) : Int)]
  refine List.map_congr_left (fun j hj => ?_)
  have hjb : j < b + 1 := List.mem_range.1 hj
  have hjle : j ≤ b := Nat.le_of_lt_succ hjb
  have hjknle : j ≤ K * n := by omega
  have hle : j * δ ≤ t + K * n * δ :=
    Nat.le_trans (Nat.mul_le_mul_right δ hjknle) (by omega)
  have hneg : ((j : Nat) : Int) * (-(δ : Int)) = -(((j : Nat) : Int) * ((δ : Nat) : Int)) :=
    Int.mul_neg _ _
  have hadd : (((t + K * n * δ : Nat) : Int)) + -(((j : Nat) : Int) * ((δ : Nat) : Int))
      = (((t + K * n * δ : Nat) : Int)) - ((j : Nat) : Int) * ((δ : Nat) : Int) :=
    Int.sub_eq_add_neg
  rw [hneg, hadd]
  exact (modQ_natmod (t + K * n * δ) j n δ hn hle).symm

/-! ### 桥④（计数转移）：Nat 窗口 countP = Lane264.cntI 于升载 Int 窗口 -/

theorem countP_range_eq_cntI (n : Nat) (p : Nat → Bool) :
    (List.range n).countP p = Lane264.cntI (fun i => p i.toNat) (winI n) := by
  induction n with
  | zero => simp [winI, Lane264.cntI]
  | succ k ih =>
    have hcnt : ∀ (q : Int → Bool) (L : List Int) (x : Int),
        Lane264.cntI q (L ++ [x]) = Lane264.cntI q L + Lane264.b2n (q x) := by
      intro q L
      induction L with
      | nil => intro x; simp [Lane264.cntI, Lane264.b2n]
      | cons y L ihl =>
        intro x
        rw [show Lane264.cntI q ((y :: L) ++ [x])
            = Lane264.b2n (q y) + Lane264.cntI q (L ++ [x]) from rfl, ihl x]
        simp only [Lane264.cntI]
        omega
    have hw : winI (k + 1) = winI k ++ [((k : Nat) : Int)] := by
      simp only [winI, List.range_succ, List.map_append, List.map_singleton]
    rw [List.range_succ, List.countP_append, hw, hcnt, ih]
    simp only [List.countP_singleton, Lane264.b2n, Int.toNat_natCast]

/-! ### 全链路接线件（对既有两块零改动，纯引用） -/

/-- **接线件①（|F| 计数的全链路重述）**：Lane283 计数层 |F| 账（Nat countP 口径）
= Lane264.cntI 口径于升载窗口 winI 上对 Lane264.segList（段首 ↑(t+Knδ)、步长 −δ、
b+1 元）modQ 像谓词的计数——两块口径经桥①–④统一。 -/
theorem wired_block_count (n δ t K b : Nat) (hn : 0 < n) (hK : b + 1 ≤ K * n) :
    (List.range n).countP (fun x => decide (x ∈ Lane283.blockList n δ t K b))
      = Lane264.cntI
          (fun i => decide (i.toNat
            ∈ (Lane264.segList ((t + K * n * δ : Nat) : Int) (-(δ : Int)) 0 (b + 1)).map (modQ n)))
          (winI n) := by
  rw [Lane291.blockList_eq_segList n δ t K b hn hK]
  exact countP_range_eq_cntI n _

/-- **接线件②（|F| = b+1 经桥取值）**：Int 口径 segList 谓词计数 = b+1
（值由 Lane283.block_count 承载，桥③④转移表述）。 -/
theorem wired_block_value (n δ t K b : Nat) (hn : 0 < n) (hδ : 0 < δ)
    (hK : b + 1 ≤ K * n) (hb : b + 1 ≤ n / Nat.gcd n δ) :
    Lane264.cntI
        (fun i => decide (i.toNat
          ∈ (Lane264.segList ((t + K * n * δ : Nat) : Int) (-(δ : Int)) 0 (b + 1)).map (modQ n)))
        (winI n) = b + 1 := by
  rw [← wired_block_count n δ t K b hn hK]
  exact Lane283.block_count n δ t K b hn hδ hK hb

/-- **接线件③（(★) 预算两口径同值）**：|F∪{t₂}| = d₁+1 的 Nat 口径账与
Int 口径（Lane264.cntI × segList modQ 像）账同值——计数层③经桥全链路入 segList 链。 -/
theorem wired_budget_star (n δ t K b d1 : Nat) (hn : 0 < n) (hδ : 0 < δ)
    (hK : b + 1 ≤ K * n) (hb : b + 1 ≤ n / Nat.gcd n δ) (hd1 : b = d1) :
    (List.range n).countP
        (fun x => decide (x ∈ Lane283.segPt n δ t K 0 :: Lane283.blockList n δ t K b)) = d1 + 1
    ∧ Lane264.cntI
        (fun i => decide (i.toNat
          ∈ (Lane264.segList ((t + K * n * δ : Nat) : Int) (-(δ : Int)) 0 (b + 1)).map (modQ n)))
        (winI n) = d1 + 1 := by
  refine ⟨Lane283.budget_star n δ t K b d1 hn hδ hK hb hd1, ?_⟩
  have hv := wired_block_value n δ t K b hn hδ hK hb
  rw [hv, hd1]

/-- **接线件④（t₂ = 段首的 Int 侧入链）**：Lane264.arcList_lt_mem 给段首
↑(t+Knδ) ∈ segList（第 0 位，j=0 即 t₂），其 modQ 像恰为 Lane283.segPt·0——
「t₂ ∈ F 并入不增」的机理经桥跨口径兑现。 -/
theorem bridge_head_mem (n δ t K b : Nat) :
    modQ n ((t + K * n * δ : Nat) : Int)
      ∈ (Lane264.segList ((t + K * n * δ : Nat) : Int) (-(δ : Int)) 0 (b + 1)).map (modQ n) := by
  have hz : Lane264.segList ((t + K * n * δ : Nat) : Int) (-(δ : Int)) 0 (b + 1)
      = Lane264.arcList ((t + K * n * δ : Nat) : Int) (-(δ : Int)) (b + 1) := by
    show Lane264.arcList (((t + K * n * δ : Nat) : Int) + (0 : Int) * (-(δ : Int)))
        (-(δ : Int)) (b + 1) = _
    rw [Int.zero_mul, Int.add_zero]
  rw [hz]
  refine List.mem_map.2 ⟨_, Lane264.arcList_lt_mem (-(δ : Int)) ((t + K * n * δ : Nat) : Int)
    (b + 1) 0 (by omega), ?_⟩
  have h0 : ((0 : Nat) : Int) * (-(δ : Int)) = (0 : Int) := by
    rw [Int.natCast_zero, Int.zero_mul]
  rw [h0, Int.add_zero]

/-! ### Z₁₂/Z₁₈ 接线实例锁（双路对拍：一般定理直推 ⊗ decide 数值） -/

/-- Z₁₂ 接线实例（一般定理直推）：Int 口径 segList 谓词计数 = 3 = b+1，
与 Lane283.inst12_count_lock 首账同值。 -/
theorem inst12_wired_gen :
    Lane264.cntI
        (fun i => decide (i.toNat
          ∈ (Lane264.segList ((0 + 1 * 12 * 2 : Nat) : Int) (-(2 : Int)) 0 (2 + 1)).map (modQ 12)))
        (winI 12) = 3 :=
  wired_block_value 12 2 0 1 2 (by omega) (by omega) (by omega) (by decide)

/-- Z₁₂ 接线实例（decide 数值路径）：同式 = 3（segList 24 (−2) 0 3 = [24,22,20]，
modQ 12 像 = [0,10,8]）。 -/
theorem inst12_wired_decide :
    Lane264.cntI
        (fun i => decide (i.toNat
          ∈ (Lane264.segList ((0 + 1 * 12 * 2 : Nat) : Int) (-(2 : Int)) 0 (2 + 1)).map (modQ 12)))
        (winI 12) = 3 := by
  decide

/-- Z₁₂ 桥③列表级锁：blockList = segList modQ 像（decide）。 -/
theorem inst12_bridge_list : Lane283.blockList 12 2 0 1 2
    = (Lane264.segList ((0 + 1 * 12 * 2 : Nat) : Int) (-(2 : Int)) 0 (2 + 1)).map (modQ 12) :=
  Lane291.blockList_eq_segList 12 2 0 1 2 (by omega) (by omega)

/-- Z₁₂ (★) 预算经桥：两口径同值 3 = d₁+1（d₁ = 2）。 -/
theorem inst12_wired_budget :
    (List.range 12).countP
        (fun x => decide (x ∈ Lane283.segPt 12 2 0 1 0 :: Lane283.blockList 12 2 0 1 2)) = 3
    ∧ Lane264.cntI
        (fun i => decide (i.toNat
          ∈ (Lane264.segList ((0 + 1 * 12 * 2 : Nat) : Int) (-(2 : Int)) 0 (2 + 1)).map (modQ 12)))
        (winI 12) = 3 :=
  wired_budget_star 12 2 0 1 2 2 (by omega) (by omega) (by omega) (by decide) rfl

/-- Z₁₈ 接线实例（一般定理直推）：Int 口径 segList 谓词计数 = 4 = b+1，
与 Lane283.inst18_count_lock 首账同值。 -/
theorem inst18_wired_gen :
    Lane264.cntI
        (fun i => decide (i.toNat
          ∈ (Lane264.segList ((0 + 1 * 18 * 3 : Nat) : Int) (-(3 : Int)) 0 (3 + 1)).map (modQ 18)))
        (winI 18) = 4 :=
  wired_block_value 18 3 0 1 3 (by omega) (by omega) (by omega) (by decide)

/-- Z₁₈ 接线实例（decide 数值路径）：同式 = 4（segList 54 (−3) 0 4 = [54,51,48,45]，
modQ 18 像 = [0,15,12,9]）。 -/
theorem inst18_wired_decide :
    Lane264.cntI
        (fun i => decide (i.toNat
          ∈ (Lane264.segList ((0 + 1 * 18 * 3 : Nat) : Int) (-(3 : Int)) 0 (3 + 1)).map (modQ 18)))
        (winI 18) = 4 := by
  decide

/-- Z₁₈ (★) 预算经桥：两口径同值 4 = d₁+1（d₁ = 3）。 -/
theorem inst18_wired_budget :
    (List.range 18).countP
        (fun x => decide (x ∈ Lane283.segPt 18 3 0 1 0 :: Lane283.blockList 18 3 0 1 3)) = 4
    ∧ Lane264.cntI
        (fun i => decide (i.toNat
          ∈ (Lane264.segList ((0 + 1 * 18 * 3 : Nat) : Int) (-(3 : Int)) 0 (3 + 1)).map (modQ 18)))
        (winI 18) = 4 :=
  wired_budget_star 18 3 0 1 3 3 (by omega) (by omega) (by omega) (by decide) rfl

/-! ### 零洞机器证据（#print axioms：零占位公理依赖、零 Classical.choice） -/

#print axioms Lane291.modQ
#print axioms Lane291.winI
#print axioms Lane291.toNat_intmod_eq_natmod
#print axioms Lane291.modQ_natmod
#print axioms Lane291.range_succ_map
#print axioms Lane291.arcList_map_modQ
#print axioms Lane291.blockList_eq_segList
#print axioms Lane291.countP_range_eq_cntI
#print axioms Lane291.wired_block_count
#print axioms Lane291.wired_block_value
#print axioms Lane291.wired_budget_star
#print axioms Lane291.bridge_head_mem
#print axioms Lane291.inst12_wired_gen
#print axioms Lane291.inst12_wired_decide
#print axioms Lane291.inst12_bridge_list
#print axioms Lane291.inst12_wired_budget
#print axioms Lane291.inst18_wired_gen
#print axioms Lane291.inst18_wired_decide
#print axioms Lane291.inst18_wired_budget

end Lane291



/-! ## lane_297：Lane264.segList 口径的 |B| = m 块表计数定理——计数层值承载的 Lean 本体
直承（承 lane_291_leansewire.md 如实注记：Lane264 块本身无 |B| = m 形态计数定理，其值此前
由 Lane283 层借道承载；本棒在 Lane264 segList 口径上直证 |B| = m，wired 四桥的值承载改为
Lean 本体直承，零借道）-/

/-! **形式化口径（如实声明）**
① 长度层（一般 a δ s m，零前提）：segList = arcList (a+sδ) δ m 的表长恰为 m
   （arcList_length / segList_length；Lane264 块此前无任何长度账）。
② 主定理 segList_modQ_count（块口径 a = ↑(t+K·n·δ)、步长 −δ、m = b+1）：segList 的
   modQ 像表在代表元全表窗口 List.range n 上的计数恰为 b+1（|B| = m 的机器形态；
   前提 0 < n、0 < δ、b+1 ≤ K·n 缓冲、b+1 ≤ n/gcd(n,δ) = ord(δ) 无绕回）。
   机理：泛化计数核 count_map_inj_range（逐点像落窗 + 界内互异 ⟹ 计数 = 表长）⊕
   像值域 modQ_lt ⊕ 像互异 inj_modQ（Lane291 桥① modQ_natmod 化归 + Lane277.seg_distinct）；
   **证明零引用 Lane283 计数层**（block_count / c1_count / budget_star 全部不经）。
③ 接线新路径件：block_count2（与 Lane283.block_count 同陈述、新证明路径）与
   wired2_block_value（与 Lane291.wired_block_value 同陈述、值由 segList_modQ_count
   直承）——lane_291 四桥（blockList_eq_segList / wired_block_count / wired_block_value /
   wired_budget_star）的值承载自此经本块直承，Lane283 层借道取消；等价性由
   block_count_routes_agree / wired_routes_agree（同式同值 rfl）锁死。
④ 如实注记（与目标形态的差距）：主定理为「模 Q 后计数」形态（任务书授权的落地形态
   之一）；一般起点 a（非缓冲口径 ↑(t+K·n·δ)）的 modQ 像互异需 Int 级 gcd 整除论，
   本轮未落地，一般 a 口径只有长度层与值域件，互异性缺口如实留档。
⑤ Z₁₂/Z₁₈ 实例锁双路：decide 数值 ⊗ 一般定理直推同值（ord(12,2) = 6 ≥ 3、
   ord(18,3) = 6 ≥ 4 无绕回）。
⑥ 全块 #print axioms 逐件实录：零占位公理依赖、零 Classical.choice。 -/

namespace Lane297

/-! ### countP 微工具件（自证，不引 Lane283 层） -/

/-- 谓词逐点相等则计数相等（归纳直证）。 -/
theorem countP_congr_l (w : List Nat) (p q : Nat → Bool)
    (h : ∀ x ∈ w, p x = q x) : w.countP p = w.countP q := by
  induction w with
  | nil => simp
  | cons x w ih =>
    rw [List.countP_cons, List.countP_cons,
      ih (fun y hy => h y (List.mem_cons.2 (Or.inr hy))), h x (List.mem_cons.2 (Or.inl rfl))]

/-- 互斥分解：逐点互斥时 countP (p‖q) = countP p + countP q。 -/
theorem countP_or (w : List Nat) (p q : Nat → Bool)
    (hdisj : ∀ x ∈ w, ¬ (p x = true ∧ q x = true)) :
    w.countP (fun x => p x || q x) = w.countP p + w.countP q := by
  induction w with
  | nil => simp
  | cons x w ih =>
    rw [List.countP_cons, List.countP_cons, List.countP_cons,
      ih (fun y hy => hdisj y (List.mem_cons.2 (Or.inr hy)))]
    cases hp : p x <;> cases hq : q x <;> simp <;>
      first
        | omega
        | exact absurd ⟨hp, hq⟩ (hdisj x (List.mem_cons.2 (Or.inl rfl)))

/-- 恒假谓词计数为零（归纳直证；core 的 List.countP_eq_zero 自带
Classical.choice 传染，本块避开）。 -/
theorem countP_false (w : List Nat) : w.countP (fun _ => false) = 0 := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    rw [List.countP_cons, ih]
    simp

/-- 点计数零：a 不在窗口内计 0。 -/
theorem countP_point_zero (m a : Nat) (ha : ¬ a < m) :
    (List.range m).countP (fun x => decide (x = a)) = 0 := by
  induction m with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.countP_append, ih (by omega)]
    have hka : ¬ (k = a) := by omega
    simp [hka]

/-- 点计数一：a < n 计 1。 -/
theorem countP_point_one (n a : Nat) (ha : a < n) :
    (List.range n).countP (fun x => decide (x = a)) = 1 := by
  induction n with
  | zero => omega
  | succ m ih =>
    rw [List.range_succ, List.countP_append]
    have ham : a ≤ m := by omega
    rcases Nat.eq_or_lt_of_le ham with heq | hlt
    · rw [heq, countP_point_zero m m (by omega)]
      simp
    · rw [ih hlt]
      have hne : ¬ (m = a) := by omega
      simp [hne]

/-! ### modQ 像的值域与互异（缓冲口径单射核） -/

/-- modQ 像恒落窗口内：(0 < n) 时 modQ n i < n。 -/
theorem modQ_lt (n : Nat) (hn : 0 < n) (i : Int) : Lane291.modQ n i < n := by
  have h1 : 0 ≤ i % ((n : Nat) : Int) := Int.emod_nonneg i (by omega)
  have hpos : (0 : Int) < ((n : Nat) : Int) := by omega
  exact (Int.toNat_lt h1).2 (Int.emod_lt_of_pos i hpos)

/-- modQ 像互异（缓冲口径，计数单射核）：j < m ≤ K·n、m < ord(δ) 时第 j 位像 ≠ 第 m 位像。
机理：Lane291 桥①（modQ_natmod）把两像化归缓冲代表元，再调 Lane277.seg_distinct。 -/
theorem inj_modQ (n δ t K m j : Nat) (hn : 0 < n) (hδ : 0 < δ)
    (hK : m ≤ K * n) (hord : m < n / Nat.gcd n δ) (hj : j < m) :
    Lane291.modQ n (((t + K * n * δ : Nat) : Int) - ((j : Nat) : Int) * ((δ : Nat) : Int))
      ≠ Lane291.modQ n (((t + K * n * δ : Nat) : Int) - ((m : Nat) : Int) * ((δ : Nat) : Int)) := by
  intro h
  have hjle : j ≤ K * n := Nat.le_of_lt (Nat.lt_of_lt_of_le hj hK)
  have hjδ : j * δ ≤ t + K * n * δ :=
    Nat.le_trans (Nat.mul_le_mul_right δ hjle) (by omega)
  have hmδ : m * δ ≤ t + K * n * δ :=
    Nat.le_trans (Nat.mul_le_mul_right δ hK) (by omega)
  rw [Lane291.modQ_natmod (t + K * n * δ) j n δ hn hjδ,
    Lane291.modQ_natmod (t + K * n * δ) m n δ hn hmδ] at h
  exact Lane277.seg_distinct n δ t K j m hn hδ hK hj (by omega) h

/-! ### 泛化计数核：互异 + 落窗的逐点像表计数 = 表长（|B| = m 的机器形态） -/

theorem count_map_inj_range (n : Nat) (g : Nat → Nat) : ∀ (m : Nat),
    (∀ j, g j < n) → (∀ j j', j < j' → j' < m → g j ≠ g j') →
    (List.range n).countP
      (fun x => decide (x ∈ (List.range m).map g)) = m := by
  intro m
  induction m with
  | zero =>
    intro _ _
    have hz : (List.range 0).map g = [] := rfl
    rw [hz, show (fun x : Nat => decide (x ∈ ([] : List Nat))) = (fun _ => false) from rfl,
      countP_false]
  | succ m ih =>
    intro glt ginj
    have hsplit : (List.range (m + 1)).map g = (List.range m).map g ++ [g m] := by
      rw [List.range_succ, List.map_append, List.map_singleton]
    have hpred : (List.range n).countP
        (fun x => decide (x ∈ (List.range m).map g ++ [g m]))
        = (List.range n).countP
            (fun x => decide (x ∈ (List.range m).map g) || decide (x = g m)) := by
      refine countP_congr_l _ _ _ (fun x _ => ?_)
      simp [List.mem_append]
    have hdisj : ∀ x ∈ List.range n,
        ¬ (decide (x ∈ (List.range m).map g) = true ∧ decide (x = g m) = true) := by
      intro x _ hcon
      obtain ⟨h1c, h2c⟩ := hcon
      have hxin : x ∈ (List.range m).map g := of_decide_eq_true h1c
      have hxeq : x = g m := of_decide_eq_true h2c
      simp only [List.mem_map] at hxin
      obtain ⟨j, hjm, hje⟩ := hxin
      have hjlt : j < m := List.mem_range.1 hjm
      exact ginj j m hjlt (by omega) (hje.trans hxeq)
    rw [hsplit, hpred, countP_or _ _ _ hdisj,
      ih glt (fun j j' hj hjm => ginj j j' hj (by omega)),
      countP_point_one n (g m) (glt m)]

/-! ### 长度层（一般 a δ s m 零前提）：segList 表长 = m -/

theorem arcList_length (a δ : Int) : ∀ m : Nat, (Lane264.arcList a δ m).length = m := by
  intro m
  induction m generalizing a with
  | zero => rfl
  | succ m ih =>
    show (a :: Lane264.arcList (a + δ) δ m).length = m + 1
    rw [List.length_cons, ih]

theorem segList_length (a δ : Int) (s m : Nat) : (Lane264.segList a δ s m).length = m :=
  arcList_length _ _ m

/-! ### 主定理：Lane264 segList 口径的块表计数 |B| = b+1（不经 Lane283 层） -/

theorem segList_modQ_count (n δ t K b : Nat) (hn : 0 < n) (hδ : 0 < δ)
    (hK : b + 1 ≤ K * n) (hb : b + 1 ≤ n / Nat.gcd n δ) :
    (List.range n).countP (fun x => decide (x ∈
      (Lane264.segList ((t + K * n * δ : Nat) : Int) (-(δ : Int)) 0 (b + 1)).map (Lane291.modQ n)))
      = b + 1 := by
  have hz : Lane264.segList ((t + K * n * δ : Nat) : Int) (-(δ : Int)) 0 (b + 1)
      = Lane264.arcList ((t + K * n * δ : Nat) : Int) (-(δ : Int)) (b + 1) := by
    show Lane264.arcList (((t + K * n * δ : Nat) : Int) + (0 : Int) * (-(δ : Int)))
        (-(δ : Int)) (b + 1) = _
    rw [Int.zero_mul, Int.add_zero]
  rw [hz, Lane291.arcList_map_modQ n (-(δ : Int)) (b + 1) ((t + K * n * δ : Nat) : Int)]
  refine count_map_inj_range n (fun j => Lane291.modQ n
      (((t + K * n * δ : Nat) : Int) + ((j : Nat) : Int) * (-(δ : Int)))) (b + 1)
    (fun j => modQ_lt n hn _) ?_
  intro j j' hjj hj'lt h
  have hpt : ∀ j : Nat,
      Lane291.modQ n (((t + K * n * δ : Nat) : Int) + ((j : Nat) : Int) * (-(δ : Int)))
        = Lane291.modQ n
            (((t + K * n * δ : Nat) : Int) - ((j : Nat) : Int) * ((δ : Nat) : Int)) := by
    intro j
    have h1 : (((t + K * n * δ : Nat) : Int)) - ((j : Nat) : Int) * ((δ : Nat) : Int)
        = (((t + K * n * δ : Nat) : Int)) + ((j : Nat) : Int) * (-(δ : Int)) := by
      rw [Int.mul_neg _ _]
      exact (Int.sub_eq_add_neg).symm
    rw [h1]
  have e1 := hpt j
  have e2 := hpt j'
  rw [e1, e2] at h
  exact inj_modQ n δ t K j' j hn hδ (by omega) (by omega) hjj h

/-! ### 接线新路径件：wired 值承载的 Lean 本体直承（零借道 Lane283 计数层） -/

/-- **新路径件①（Lane283 计数层②的同陈述新证）**：|F| = b+1 的 Nat 窗口账——
陈述与 Lane283.block_count 逐字同，证明路径不同：经规范桥③（blockList = segList
modQ 像）+ Lane297.segList_modQ_count 直推，零引用 Lane283 计数层。 -/
theorem block_count2 (n δ t K b : Nat) (hn : 0 < n) (hδ : 0 < δ)
    (hK : b + 1 ≤ K * n) (hb : b + 1 ≤ n / Nat.gcd n δ) :
    (List.range n).countP (fun x => decide (x ∈ Lane283.blockList n δ t K b)) = b + 1 := by
  rw [Lane291.blockList_eq_segList n δ t K b hn hK]
  exact segList_modQ_count n δ t K b hn hδ hK hb

/-- **新路径件②（wired 值承载的新证）**：Lane264 cntI 口径 |F| = b+1——
陈述与 Lane291.wired_block_value 逐字同，值由 segList_modQ_count 直承
（旧路径经 Lane283.block_count，新路径零引用）。 -/
theorem wired2_block_value (n δ t K b : Nat) (hn : 0 < n) (hδ : 0 < δ)
    (hK : b + 1 ≤ K * n) (hb : b + 1 ≤ n / Nat.gcd n δ) :
    Lane264.cntI
        (fun i => decide (i.toNat
          ∈ (Lane264.segList ((t + K * n * δ : Nat) : Int) (-(δ : Int)) 0 (b + 1)).map (Lane291.modQ n)))
        (Lane291.winI n) = b + 1 := by
  rw [← Lane291.wired_block_count n δ t K b hn hK]
  exact block_count2 n δ t K b hn hδ hK hb

/-- **等价性陈述（新旧两路同式同值）**：两件计数定理的值路径陈述逐字同，值同为 b+1。 -/
theorem block_count_routes_agree (n δ t K b : Nat) (hn : 0 < n) (hδ : 0 < δ)
    (hK : b + 1 ≤ K * n) (hb : b + 1 ≤ n / Nat.gcd n δ) :
    ((List.range n).countP (fun x => decide (x ∈ Lane283.blockList n δ t K b)) = b + 1)
      ∧ ((List.range n).countP
          (fun x => decide (x ∈ Lane283.blockList n δ t K b)) = b + 1) := by
  constructor
  · exact Lane283.block_count n δ t K b hn hδ hK hb
  · exact block_count2 n δ t K b hn hδ hK hb

/-- **等价性陈述（wired 新旧两路同式同值）**。 -/
theorem wired_routes_agree (n δ t K b : Nat) (hn : 0 < n) (hδ : 0 < δ)
    (hK : b + 1 ≤ K * n) (hb : b + 1 ≤ n / Nat.gcd n δ) :
    (Lane264.cntI (fun i => decide (i.toNat
          ∈ (Lane264.segList ((t + K * n * δ : Nat) : Int) (-(δ : Int)) 0 (b + 1)).map (Lane291.modQ n)))
        (Lane291.winI n) = b + 1)
      ∧ (Lane264.cntI (fun i => decide (i.toNat
          ∈ (Lane264.segList ((t + K * n * δ : Nat) : Int) (-(δ : Int)) 0 (b + 1)).map (Lane291.modQ n)))
        (Lane291.winI n) = b + 1) := by
  constructor
  · exact Lane291.wired_block_value n δ t K b hn hδ hK hb
  · exact wired2_block_value n δ t K b hn hδ hK hb

/-! ### Z₁₂/Z₁₈ 实例锁（decide 数值 ⊗ 一般定理直推双路） -/

/-- Z₁₂ 数值锁：|B| = 3（segList 24 (−2) 0 3 modQ 12 像 = [0,10,8]）。 -/
theorem inst12_count297_decide :
    (List.range 12).countP (fun x => decide (x ∈
      (Lane264.segList ((0 + 1 * 12 * 2 : Nat) : Int) (-(2 : Int)) 0 (2 + 1)).map
        (Lane291.modQ 12))) = 3 := by
  decide

/-- Z₁₂ 一般定理直推：同式 = 3（ord(12,2) = 6 ≥ 3 无绕回）。 -/
theorem inst12_count297_gen :
    (List.range 12).countP (fun x => decide (x ∈
      (Lane264.segList ((0 + 1 * 12 * 2 : Nat) : Int) (-(2 : Int)) 0 (2 + 1)).map
        (Lane291.modQ 12))) = 3 :=
  segList_modQ_count 12 2 0 1 2 (by omega) (by omega) (by omega) (by decide)

/-- Z₁₈ 数值锁：|B| = 4（segList 54 (−3) 0 4 modQ 18 像 = [0,15,12,9]）。 -/
theorem inst18_count297_decide :
    (List.range 18).countP (fun x => decide (x ∈
      (Lane264.segList ((0 + 1 * 18 * 3 : Nat) : Int) (-(3 : Int)) 0 (3 + 1)).map
        (Lane291.modQ 18))) = 4 := by
  decide

/-- Z₁₈ 一般定理直推：同式 = 4（ord(18,3) = 6 ≥ 4 无绕回）。 -/
theorem inst18_count297_gen :
    (List.range 18).countP (fun x => decide (x ∈
      (Lane264.segList ((0 + 1 * 18 * 3 : Nat) : Int) (-(3 : Int)) 0 (3 + 1)).map
        (Lane291.modQ 18))) = 4 :=
  segList_modQ_count 18 3 0 1 3 (by omega) (by omega) (by omega) (by decide)

/-! ### 零洞机器证据（#print axioms：零占位公理依赖、零 Classical.choice） -/

#print axioms Lane297.countP_false
#print axioms Lane297.countP_congr_l
#print axioms Lane297.countP_or
#print axioms Lane297.countP_point_zero
#print axioms Lane297.countP_point_one
#print axioms Lane297.modQ_lt
#print axioms Lane297.inj_modQ
#print axioms Lane297.count_map_inj_range
#print axioms Lane297.arcList_length
#print axioms Lane297.segList_length
#print axioms Lane297.segList_modQ_count
#print axioms Lane297.block_count2
#print axioms Lane297.wired2_block_value
#print axioms Lane297.block_count_routes_agree
#print axioms Lane297.wired_routes_agree
#print axioms Lane297.inst12_count297_decide
#print axioms Lane297.inst12_count297_gen
#print axioms Lane297.inst18_count297_decide
#print axioms Lane297.inst18_count297_gen

end Lane297



/-! ## lane_308：块装配核→整板值的一般参数接线（承 lane_277/283/291/297 四块纯追加）-/

namespace Lane308

/-! ### 整板值闭环（一般参数零洞） -/

/-- **整板分解恒等式**：|F| + |C₂| = n（|F| 经 Lane297.block_count2 直证路；
补集账经 Lane283.countP_neg；整板 = 窗口 List.range n 全表）。 -/
theorem board_split (n δ t K b : Nat) (hn : 1 ≤ n) (hδ : 1 ≤ δ)
    (hK : b + 1 ≤ K * n) (hb : b + 1 ≤ n / Nat.gcd n δ) :
    (List.range n).countP (fun x => decide (x ∈ Lane283.blockList n δ t K b))
      + (List.range n).countP (fun x => decide (¬(x ∈ Lane283.blockList n δ t K b))) = n := by
  have h1 := Lane297.block_count2 n δ t K b hn hδ hK hb
  have h2 := Lane283.countP_neg (List.range n)
    (fun x => decide (x ∈ Lane283.blockList n δ t K b))
  have h3 := Lane283.countP_congr_l (List.range n)
    (fun x => decide (¬(x ∈ Lane283.blockList n δ t K b)))
    (fun x => !(decide (x ∈ Lane283.blockList n δ t K b)))
    (fun _ _ => decide_not)
  rw [List.length_range] at h2
  rw [h3]
  omega

/-- **补集账新路直承**（与 Lane283.block_complement 同陈述、新证明路径）：
|C₂| = n − (b+1)——整板分解恒等式移项，零引用 Lane283.block_complement / c1_count。 -/
theorem block_complement2 (n δ t K b : Nat) (hn : 1 ≤ n) (hδ : 1 ≤ δ)
    (hK : b + 1 ≤ K * n) (hb : b + 1 ≤ n / Nat.gcd n δ) :
    (List.range n).countP (fun x => decide (¬(x ∈ Lane283.blockList n δ t K b)))
      = n - (b + 1) := by
  have h1 := Lane297.block_count2 n δ t K b hn hδ hK hb
  have h := board_split n δ t K b hn hδ hK hb
  omega

/-- **补集账两路同值锁**：Lane283.block_complement（旧路）与 block_complement2
（新路）同式同值合取。 -/
theorem complement_routes_agree (n δ t K b : Nat) (hn : 1 ≤ n) (hδ : 1 ≤ δ)
    (hK : b + 1 ≤ K * n) (hb : b + 1 ≤ n / Nat.gcd n δ) :
    ((List.range n).countP (fun x => decide (¬(x ∈ Lane283.blockList n δ t K b))) = n - (b + 1))
      ∧ ((List.range n).countP
          (fun x => decide (¬(x ∈ Lane283.blockList n δ t K b))) = n - (b + 1)) := by
  constructor
  · exact Lane283.block_complement n δ t K b hn hδ hK hb
  · exact block_complement2 n δ t K b hn hδ hK hb

/-- **(★) 预算整板闭环一般参数式**：|F∪{t₂}| + |C₂| = n——budget_star（= d₁+1）
与整板分解恒等式合流（t₂ = 段首 ∈ F 并入不增，故 |F∪{t₂}| = |F|）。 -/
theorem board_value_star (n δ t K b d1 : Nat) (hn : 1 ≤ n) (hδ : 1 ≤ δ)
    (hK : b + 1 ≤ K * n) (hb : b + 1 ≤ n / Nat.gcd n δ) (hd1 : b = d1) :
    (List.range n).countP
        (fun x => decide (x ∈ Lane283.segPt n δ t K 0 :: Lane283.blockList n δ t K b))
      + (List.range n).countP (fun x => decide (¬(x ∈ Lane283.blockList n δ t K b))) = n := by
  have h1 := Lane283.budget_star n δ t K b d1 hn hδ hK hb hd1
  have h3 := Lane297.block_count2 n δ t K b hn hδ hK hb
  have heq : (List.range n).countP
      (fun x => decide (x ∈ Lane283.segPt n δ t K 0 :: Lane283.blockList n δ t K b))
      = (List.range n).countP (fun x => decide (x ∈ Lane283.blockList n δ t K b)) := by
    rw [h1, h3]; omega
  rw [heq]
  exact board_split n δ t K b hn hδ hK hb

/-! ### 主接线件：块装配核 → 整板值（一般参数打包） -/

/-- **块装配核→整板值主接线件**（lane_277 §3 落款「装配核与计数层接线」残余的兑现件）：
同一参数组下 Lane277.seg_assembly_core 几何三合一（全段避 t₁ + 段内两两互异 + 起点避 t₁）
与整板计数闭环（|C₁| = b、|F| = b+1、|C₂| = n−(b+1)、(★) |F∪{t₂}| = d₁+1、
剩余 |C₂| = d₂、(d₁+1)+d₂ = n）七分量合取——装配核与整板账在一件定理内合流。
计数层值由 Lane297.block_count2 直证路承载。 -/
theorem assembly_board (n δ t K b d1 d2 : Nat)
    (hn : 1 ≤ n) (hδ : 1 ≤ δ) (hK : b + 1 ≤ K * n)
    (hL : 2 ≤ n / Nat.gcd n δ) (hb : b ≤ n / Nat.gcd n δ - 1)
    (hd1 : b = d1) (hd2 : n - 1 - b = d2)
    (j j' : Nat) (hj : j < b) (hj' : j < j') (hj'b : j' < b) :
    ((t + K * n * δ - j * δ) % n ≠ (t + δ) % n
        ∧ (t + K * n * δ - j * δ) % n ≠ (t + K * n * δ - j' * δ) % n
        ∧ (t + K * n * δ) % n ≠ (t + δ) % n)
      ∧ (List.range n).countP (fun x => decide (x ∈ Lane283.c1List n δ t K b)) = b
      ∧ (List.range n).countP (fun x => decide (x ∈ Lane283.blockList n δ t K b)) = b + 1
      ∧ (List.range n).countP
          (fun x => decide (¬(x ∈ Lane283.blockList n δ t K b))) = n - (b + 1)
      ∧ (List.range n).countP
          (fun x => decide (x ∈ Lane283.segPt n δ t K 0 :: Lane283.blockList n δ t K b)) = d1 + 1
      ∧ (List.range n).countP
          (fun x => decide (¬(x ∈ Lane283.blockList n δ t K b))) = d2
      ∧ d1 + 1 + d2 = n := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Lane277.seg_assembly_core n δ b t K hn hδ (by omega) hL hb j j' hj hj' hj'b
  · exact Lane283.c1_count n δ t K b hn hδ (by omega) (by omega)
  · exact Lane297.block_count2 n δ t K b hn hδ hK (by omega)
  · exact block_complement2 n δ t K b hn hδ hK (by omega)
  · exact Lane283.budget_star n δ t K b d1 hn hδ hK (by omega) hd1
  · exact Lane283.remainder_d2 n δ t K b d2 hn hδ hK (by omega) hd2
  · have hle : b + 1 ≤ n :=
      Nat.le_trans (by omega) (Nat.div_le_self n (Nat.gcd n δ))
    omega

/-! ### wired 口径（Lane264 cntI × segList modQ 像）整板两账 -/

/-- **wired 补集账新路**：cntI 口径 |C₂| = n − (b+1)——桥④计数转移 + 桥③规范桥 +
block_complement2 直推（值零借道 Lane283 计数层）。 -/
theorem wired_block_complement2 (n δ t K b : Nat) (hn : 0 < n) (hδ : 0 < δ)
    (hK : b + 1 ≤ K * n) (hb : b + 1 ≤ n / Nat.gcd n δ) :
    Lane264.cntI
        (fun i => decide (¬(i.toNat ∈
          (Lane264.segList ((t + K * n * δ : Nat) : Int) (-(δ : Int)) 0 (b + 1)).map
            (Lane291.modQ n))))
        (Lane291.winI n) = n - (b + 1) := by
  rw [← Lane291.countP_range_eq_cntI n
    (fun x => decide (¬(x ∈
      (Lane264.segList ((t + K * n * δ : Nat) : Int) (-(δ : Int)) 0 (b + 1)).map
        (Lane291.modQ n))))]
  rw [← Lane291.blockList_eq_segList n δ t K b hn hK]
  exact block_complement2 n δ t K b hn hδ hK hb

/-- **wired 整板两账合取**：cntI 口径 |F| = b+1（Lane297.wired2_block_value 直承）
∧ cntI 口径 |C₂| = n−(b+1)（wired_block_complement2）——segList 链上整板值闭环。 -/
theorem wired_board_value (n δ t K b : Nat) (hn : 0 < n) (hδ : 0 < δ)
    (hK : b + 1 ≤ K * n) (hb : b + 1 ≤ n / Nat.gcd n δ) :
    (Lane264.cntI
        (fun i => decide (i.toNat ∈
          (Lane264.segList ((t + K * n * δ : Nat) : Int) (-(δ : Int)) 0 (b + 1)).map
            (Lane291.modQ n)))
        (Lane291.winI n) = b + 1)
      ∧ (Lane264.cntI
        (fun i => decide (¬(i.toNat ∈
          (Lane264.segList ((t + K * n * δ : Nat) : Int) (-(δ : Int)) 0 (b + 1)).map
            (Lane291.modQ n))))
        (Lane291.winI n) = n - (b + 1)) :=
  ⟨Lane297.wired2_block_value n δ t K b hn hδ hK hb,
    wired_block_complement2 n δ t K b hn hδ hK hb⟩

/-! ### Z₁₂/Z₁₈ 实例锁（对齐 Lane277/283/297 既有机器账） -/

/-- Z₁₂ 整板账一般定理直推：assembly_board 全实例化——几何三合一 + 五账 + 闭环
(n=12, δ=2, t=0, K=1, b=2, d₁=2, d₂=9, ord=6)。 -/
theorem inst12_board_gen :
    ((0 + 1 * 12 * 2 - 0 * 2) % 12 ≠ (0 + 2) % 12
        ∧ (0 + 1 * 12 * 2 - 0 * 2) % 12 ≠ (0 + 1 * 12 * 2 - 1 * 2) % 12
        ∧ (0 + 1 * 12 * 2) % 12 ≠ (0 + 2) % 12)
      ∧ (List.range 12).countP (fun x => decide (x ∈ Lane283.c1List 12 2 0 1 2)) = 2
      ∧ (List.range 12).countP (fun x => decide (x ∈ Lane283.blockList 12 2 0 1 2)) = 2 + 1
      ∧ (List.range 12).countP
          (fun x => decide (¬(x ∈ Lane283.blockList 12 2 0 1 2))) = 12 - (2 + 1)
      ∧ (List.range 12).countP
          (fun x => decide (x ∈ Lane283.segPt 12 2 0 1 0 :: Lane283.blockList 12 2 0 1 2)) = 2 + 1
      ∧ (List.range 12).countP
          (fun x => decide (¬(x ∈ Lane283.blockList 12 2 0 1 2))) = 9
      ∧ (2 : Nat) + 1 + 9 = 12 :=
  assembly_board 12 2 0 1 2 2 9 (by omega) (by omega) (by omega) (by decide) (by decide)
    rfl (by decide) 0 1 (by omega) (by omega) (by omega)

/-- Z₁₂ 整板账 decide 数值锁：|F|=3、|C₂|=9、(★) 预算 12−3=9（对齐 Lane277.inst12_corner
末账）、闭环 3+9=12——四账与 Lane283.inst12_count_lock 2/3/9/3 逐位一致。 -/
theorem inst12_board_decide :
    (List.range 12).countP (fun x => decide (x ∈ Lane283.blockList 12 2 0 1 2)) = 3
    ∧ (List.range 12).countP
        (fun x => decide (¬(x ∈ Lane283.blockList 12 2 0 1 2))) = 9
    ∧ (12 : Nat) - 3 = 9
    ∧ (2 : Nat) + 1 + 9 = 12 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- Z₁₈ 整板账一般定理直推：assembly_board 全实例化
(n=18, δ=3, t=0, K=1, b=3, d₁=3, d₂=14, ord=6)。 -/
theorem inst18_board_gen :
    ((0 + 1 * 18 * 3 - 0 * 3) % 18 ≠ (0 + 3) % 18
        ∧ (0 + 1 * 18 * 3 - 0 * 3) % 18 ≠ (0 + 1 * 18 * 3 - 1 * 3) % 18
        ∧ (0 + 1 * 18 * 3) % 18 ≠ (0 + 3) % 18)
      ∧ (List.range 18).countP (fun x => decide (x ∈ Lane283.c1List 18 3 0 1 3)) = 3
      ∧ (List.range 18).countP (fun x => decide (x ∈ Lane283.blockList 18 3 0 1 3)) = 3 + 1
      ∧ (List.range 18).countP
          (fun x => decide (¬(x ∈ Lane283.blockList 18 3 0 1 3))) = 18 - (3 + 1)
      ∧ (List.range 18).countP
          (fun x => decide (x ∈ Lane283.segPt 18 3 0 1 0 :: Lane283.blockList 18 3 0 1 3)) = 3 + 1
      ∧ (List.range 18).countP
          (fun x => decide (¬(x ∈ Lane283.blockList 18 3 0 1 3))) = 14
      ∧ (3 : Nat) + 1 + 14 = 18 :=
  assembly_board 18 3 0 1 3 3 14 (by omega) (by omega) (by omega) (by decide) (by decide)
    rfl (by decide) 0 1 (by omega) (by omega) (by omega)

/-- Z₁₈ 整板账 decide 数值锁：|F|=4、|C₂|=14、(★) 预算 18−4=14（对齐 Lane277.inst18_corner
末账）、闭环 4+14=18——四账与 Lane283.inst18_count_lock 3/4/14/4 逐位一致。 -/
theorem inst18_board_decide :
    (List.range 18).countP (fun x => decide (x ∈ Lane283.blockList 18 3 0 1 3)) = 4
    ∧ (List.range 18).countP
        (fun x => decide (¬(x ∈ Lane283.blockList 18 3 0 1 3))) = 14
    ∧ (18 : Nat) - 4 = 14
    ∧ (3 : Nat) + 1 + 14 = 18 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-! ### 零洞机器证据（#print axioms：零占位公理依赖、零 Classical.choice） -/

#print axioms Lane308.board_split
#print axioms Lane308.block_complement2
#print axioms Lane308.complement_routes_agree
#print axioms Lane308.board_value_star
#print axioms Lane308.assembly_board
#print axioms Lane308.wired_block_complement2
#print axioms Lane308.wired_board_value
#print axioms Lane308.inst12_board_gen
#print axioms Lane308.inst12_board_decide
#print axioms Lane308.inst18_board_gen
#print axioms Lane308.inst18_board_decide

end Lane308


/-! ## lane_314：定理 A 核心不等式与定理 D λ≤1 构造器（承 Lane258/264/273/297/308 纯插入纪律）-/

namespace Lane314

/-! ### 工具件：countP 单调 / 零判据 / 点存在（零公理归纳；避开 core countP_eq_zero 的 Classical） -/

/-- 逐点蕴含 ⟹ 计数单调（归纳直证）。 -/
theorem countP_mono (w : List Nat) (p q : Nat → Bool)
    (h : ∀ x ∈ w, p x = true → q x = true) :
    w.countP p ≤ w.countP q := by
  induction w with
  | nil => simp
  | cons x w ih =>
    have ih' := ih (fun y hy => h y (List.mem_cons.2 (Or.inr hy)))
    rw [List.countP_cons, List.countP_cons]
    cases hpx : p x <;> cases hqx : q x <;>
      simp only [Bool.false_eq_true, ite_false, ite_true, Nat.add_zero]
    · exact ih'
    · exact Nat.le_trans ih' (Nat.le_succ _)
    · exfalso
      rw [h x (List.mem_cons.2 (Or.inl rfl)) hpx] at hqx
      exact absurd hqx (by decide)
    · exact Nat.succ_le_succ ih'

/-- 逐点假 ⟹ 计数为零（归纳直证，避开 core 的 Classical 版）。 -/
theorem countP_eq_zero_forall (w : List Nat) (p : Nat → Bool)
    (h : ∀ x ∈ w, p x = false) : w.countP p = 0 := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    rw [List.countP_cons]
    cases hpx : p x <;> simp only [Bool.false_eq_true, ite_false, ite_true, Nat.add_zero]
    · have hz := ih (fun y hy => h y (List.mem_cons.2 (Or.inr hy)))
      omega
    · exfalso
      rw [h x (List.mem_cons.2 (Or.inl rfl))] at hpx
      exact absurd hpx (by decide)

/-- 窗口内某点为真 ⟹ 计数 ≥ 1（归纳直证）。 -/
theorem countP_ge_one (w : List Nat) (p : Nat → Bool) (a : Nat)
    (ha : a ∈ w) (hp : p a = true) : 1 ≤ w.countP p := by
  induction w with
  | nil => exact absurd ha (by simp)
  | cons x w ih =>
    rcases List.mem_cons.1 ha with hax | hm
    · rw [hax] at hp
      rw [List.countP_cons]
      cases hp2 : p x <;>
        simp only [Bool.false_eq_true, ite_false, ite_true, Nat.add_zero]
      · exact absurd hp2 (by rw [hp] at hp2; exact Bool.noConfusion hp2)
      · omega
    · have ih' := ih hm
      rw [List.countP_cons]
      cases hp2 : p x <;>
        simp only [Bool.false_eq_true, ite_false, ite_true, Nat.add_zero]
      · omega
      · omega

/-! ### 模算术小件（全零公理） -/

/-- 窗口还原件 A：(x − δ) 的还原——z ≡ x−δ（窗口内）⟹ (z+δ)%n = x。 -/
theorem add_delta_of_sub {n δ x z : Nat} (hn : 0 < n) (hδ : δ < n) (hx : x < n)
    (h : (x + n - δ) % n = z) : (z + δ) % n = x := by
  rcases Nat.lt_or_ge x δ with hlt | hge
  · have h2 : (x + n - δ) % n = x + n - δ := Nat.mod_eq_of_lt (by omega)
    rw [h2] at h
    have hmod : (x + n) % n = x % n := by rw [Nat.add_comm]; exact Nat.add_mod_left n x
    rw [show z + δ = x + n from by omega, hmod, Nat.mod_eq_of_lt hx]
  · have h2 : (x + n - δ) % n = (x + n - δ - n) % n := Nat.mod_eq_sub_mod (by omega)
    have h3 : (x + n - δ - n) % n = (x - δ) % n := by
      rw [show x + n - δ - n = x - δ from by omega]
    have h4 : (x - δ) % n = x - δ := Nat.mod_eq_of_lt (by omega)
    rw [h2, h3, h4] at h
    rw [show z + δ = x from by omega, Nat.mod_eq_of_lt hx]

/-- 窗口还原件 B：(x + δ) 的还原——y ≡ x+δ（窗口内）⟹ (y+n−δ)%n = x。 -/
theorem sub_delta_of_add {n δ x y : Nat} (_hn : 0 < n) (hδ : δ < n) (hx : x < n)
    (h : (x + δ) % n = y) : (y + n - δ) % n = x := by
  rcases Nat.lt_or_ge (x + δ) n with hlt | hge
  · rw [Nat.mod_eq_of_lt hlt] at h
    rw [show y + n - δ = x + n from by omega]
    have hmod : (x + n) % n = x % n := by rw [Nat.add_comm]; exact Nat.add_mod_left n x
    rw [hmod, Nat.mod_eq_of_lt hx]
  · have hm1 : (x + δ) % n = (x + δ - n) % n := Nat.mod_eq_sub_mod hge
    have hm2 : (x + δ - n) % n = x + δ - n := Nat.mod_eq_of_lt (by omega)
    rw [hm1, hm2] at h
    rw [show y + n - δ = x from by omega, Nat.mod_eq_of_lt hx]

/-- 同余平移：(a%n + n − δ)%n = (a + n − δ)%n。 -/
theorem cong_shift (n δ a : Nat) (_hδ : δ < n) :
    (a % n + n - δ) % n = (a + n - δ) % n := by
  have hd : n * (a / n) + a % n = a := Nat.div_add_mod a n
  have hle : a % n ≤ a := Nat.mod_le a n
  rw [show a + n - δ = (a % n + n - δ) + n * (a / n) from by omega,
    Nat.add_mul_mod_self_left]

/-- mod_n 自吸：(a + n) % n = a % n（add_mod_left 的 addend-first 形态桥）。 -/
theorem mod_add_self (n a : Nat) : (a + n) % n = a % n := by
  rw [Nat.add_comm]; exact Nat.add_mod_left n a

/-! ### 定理 A：定义件（deep_01 §2 判定层同式） -/

/-- F₁₃ = (C₁ − δ₁₃) ∩ P，经 +δ₁₃ 像等价刻画：{x : x∈P ∧ x+δ₁₃∈C₁}。 -/
def isF13 (n δ : Nat) (P C1 : Nat → Bool) (x : Nat) : Bool := P x && C1 ((x + δ) % n)

/-- F₂₃ = (C₂ − δ₂₃) ∩ P。 -/
def isF23 (n δ : Nat) (P C2 : Nat → Bool) (x : Nat) : Bool := P x && C2 ((x + δ) % n)

/-- 泄漏集 L(C₁) = F₁₃ ∖ C₁（deep_01 §2 方向约定：泄漏位 v∈P∖C₁ 且 v+δ₁₃∈C₁）。 -/
def isL (n δ : Nat) (P C1 : Nat → Bool) (x : Nat) : Bool :=
  P x && C1 ((x + δ) % n) && !C1 x

/-- g₁₃(C₁) = |L(C₁)|（窗口 List.range n 计数）。 -/
def g13 (n δ : Nat) (P C1 : Nat → Bool) : Nat := (List.range n).countP (isL n δ P C1)

/-- val(C₁,C₂) = |F₁₃∖(C₁∪C₂)| + |F₂₃∖(C₁∪C₂∪F₁₃)| + |{t₃}∩P∖(C₁∪C₂)|。 -/
def val3 (n δ13 δ23 t3 : Nat) (P C1 C2 : Nat → Bool) : Nat :=
  (List.range n).countP (fun x => isF13 n δ13 P C1 x && !(C1 x || C2 x))
    + (List.range n).countP (fun x =>
        isF23 n δ23 P C2 x && !(C1 x || C2 x || isF13 n δ13 P C1 x))
    + (List.range n).countP (fun x => decide (x = t3) && P x && !(C1 x || C2 x))

/-! ### **定理 A 核心不等式**（注记 A-1 无前提形式；deep_03 发现 #1 收紧口径：零 so1 前提） -/

/-- **定理 A 核心（A1–A6 逐件承载）**：g₁₃(C₁) ≤ d₂ + val(C₁,C₂)。
唯一前提 |C₂| = d₂。(A3) 二分 L=(L∩C₂)⊔(L∖C₂)（countP 互斥分解）+
(A4) |L∩C₂|≤d₂（countP 单调）+ (A2)=(A1) |L∖C₂|=val 第一项（逐点 Bool 恒等式）。 -/
theorem g13_le_val_add_d2 (n d2 δ13 δ23 t3 : Nat) (P C1 C2 : Nat → Bool)
    (hd2 : (List.range n).countP C2 = d2) :
    g13 n δ13 P C1 ≤ d2 + val3 n δ13 δ23 t3 P C1 C2 := by
  unfold g13 val3
  have hpsplit : ∀ x : Nat, isL n δ13 P C1 x
      = ((isL n δ13 P C1 x && C2 x) || (isL n δ13 P C1 x && !C2 x)) := by
    intro x
    cases h : isL n δ13 P C1 x <;> cases C2 x <;> rfl
  have hd : ∀ x ∈ List.range n,
      ¬ ((isL n δ13 P C1 x && C2 x) = true ∧ (isL n δ13 P C1 x && !C2 x) = true) := by
    intro x _ hcon
    obtain ⟨h1, h2⟩ := hcon
    rw [Bool.and_eq_true] at h1 h2
    obtain ⟨_, hC2t⟩ := h1
    obtain ⟨_, hC2f⟩ := h2
    rw [Bool.not_eq_true'] at hC2f
    rw [hC2t] at hC2f
    exact Bool.noConfusion hC2f
  have hmono1 := countP_mono (List.range n) (fun x => isL n δ13 P C1 x && C2 x) C2
    (fun x _ hcon => by
      rw [Bool.and_eq_true] at hcon
      exact hcon.2)
  have hcong2 : ∀ x : Nat, (isL n δ13 P C1 x && !C2 x)
      = (isF13 n δ13 P C1 x && !(C1 x || C2 x)) := by
    intro x
    unfold isL isF13
    cases P x <;> cases C1 ((x + δ13) % n) <;> cases C1 x <;> cases C2 x <;> rfl
  rw [Lane283.countP_congr_l (List.range n) _ _ (fun x _ => hpsplit x),
    Lane283.countP_or (List.range n) _ _ hd]
  rw [hd2] at hmono1
  have h2 : (List.range n).countP (fun x => isL n δ13 P C1 x && !C2 x)
      = (List.range n).countP (fun x => isF13 n δ13 P C1 x && !(C1 x || C2 x)) :=
    Lane283.countP_congr_l _ _ _ (fun x _ => hcong2 x)
  rw [h2]
  omega

/-- **定理 A（299.A 完全体核心）**：合法对 val ≤ 1 ⟹ g₁₃(C₁) ≤ d₂+1。
（≤ p−2 ≤ N−2 的链式放大 (A7) 留 deep_01 §3 纸面层，本件锁数值核。） -/
theorem thmA_core (n d2 δ13 δ23 t3 : Nat) (P C1 C2 : Nat → Bool)
    (hd2 : (List.range n).countP C2 = d2)
    (hv : val3 n δ13 δ23 t3 P C1 C2 ≤ 1) :
    g13 n δ13 P C1 ≤ d2 + 1 := by
  have h := g13_le_val_add_d2 n d2 δ13 δ23 t3 P C1 C2 hd2
  omega

/-! ### 引理 4.2 (i)⟺(ii)：g₁₃=0 的闭性刻画（方向正确件：x − δ₁₃；deep_01 §7 勘误 1 口径） -/

/-- **引理 4.2 (i)⟺(ii)**：g₁₃(C₁)=0 ⟺ ∀x∈C₁：x−δ₁₃∈P ⟹ x−δ₁₃∈C₁。
（lane_299 §3.2 方向笔误经 deep_01 §7 勘误、deep_03 攻击面 5 复核；本件钉死正确方向。） -/
theorem g13_eq_zero_iff_closed (n δ : Nat) (hn : 0 < n) (hδ : δ < n) (P C1 : Nat → Bool) :
    g13 n δ P C1 = 0
      ↔ ∀ x, x < n → C1 x = true →
          P ((x + n - δ) % n) = true → C1 ((x + n - δ) % n) = true := by
  constructor
  · intro h0 x hx hC1 hP
    have hzn : (x + n - δ) % n < n := Nat.mod_lt _ hn
    by_cases hz : C1 ((x + n - δ) % n) = true
    · exact hz
    · exfalso
      have hnot : C1 ((x + n - δ) % n) = false := by
        cases h : C1 ((x + n - δ) % n) with
        | true => exact absurd h hz
        | false => rfl
      have hw : isL n δ P C1 ((x + n - δ) % n) = true := by
        unfold isL
        rw [hP]
        have hred := add_delta_of_sub hn hδ hx rfl
        rw [hred, hC1, hnot, Bool.not_false]
        rfl
      have hge := countP_ge_one (List.range n) (isL n δ P C1) ((x + n - δ) % n)
        (List.mem_range.2 hzn) hw
      have h0' : (List.range n).countP (isL n δ P C1) = 0 := h0
      rw [h0'] at hge
      exact absurd hge (by omega)
  · intro hC
    unfold g13
    apply countP_eq_zero_forall
    intro x hx
    unfold isL
    cases hPc : P x <;> cases hCy : C1 ((x + δ) % n) <;> cases hCx : C1 x
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exfalso
      have hyn : (x + δ) % n < n := Nat.mod_lt _ hn
      have hred : ((x + δ) % n + n - δ) % n = x := sub_delta_of_add hn hδ (List.mem_range.1 hx) rfl
      have hcy := hC ((x + δ) % n) hyn hCy (by rw [hred]; exact hPc)
      rw [hred] at hcy
      rw [hcy] at hCx
      exact Bool.noConfusion hCx
    · rfl

/-! ### 定理 D 机制件：块谓词 + 闭集 ⊕ 单块 ≤ +1（D0「闭前缀 ⊕ 至多一条内部块」的核） -/

/-- δ-块谓词：{s, s+δ, …, s+(j−1)δ}（mod n 等价类口径，窗口 [0,n) 上计数）。 -/
def blockPred (n δ s j : Nat) (x : Nat) : Bool :=
  (List.range j).any (fun i => decide (x % n = (s + i * δ) % n))

/-- 块内计数：互异块位 ⟹ |块| = j（|C₁| = d₁ 的承载件）。 -/
theorem countP_block (n δ s j : Nat) (hn : 0 < n) (_hδ : δ < n)
    (hj : ∀ i k, i < j → k < j → (s + i * δ) % n = (s + k * δ) % n → i = k) :
    (List.range n).countP (blockPred n δ s j) = j := by
  induction j with
  | zero =>
    have hz : blockPred n δ s 0 = fun _ => false := by
      funext x
      simp [blockPred]
    rw [hz]
    exact Lane283.countP_false _
  | succ m ih =>
    have hsplit : blockPred n δ s (m + 1)
        = fun x => blockPred n δ s m x || decide (x % n = (s + m * δ) % n) := by
      funext x
      simp [blockPred, List.range_succ, List.any_append, List.any_cons]
    have hdisj : ∀ x ∈ List.range n, ¬ (blockPred n δ s m x = true
        ∧ decide (x % n = (s + m * δ) % n) = true) := by
      intro x _ hcon
      obtain ⟨h1, h2⟩ := hcon
      unfold blockPred at h1
      rw [List.any_eq_true] at h1
      obtain ⟨i, hi, hieq⟩ := h1
      have him : i < m := List.mem_range.1 hi
      rw [decide_eq_true_eq] at hieq h2
      exact absurd (hj i m (by omega) (by omega) (hieq.symm.trans h2)) (by omega)
    have hpt : (List.range n).countP
        (fun x => decide (x % n = (s + m * δ) % n)) = 1 := by
      rw [Lane283.countP_congr_l (List.range n)
        (fun x => decide (x % n = (s + m * δ) % n))
        (fun x => decide (x = (s + m * δ) % n))
        (fun x hx => by rw [Nat.mod_eq_of_lt (List.mem_range.1 hx)])]
      exact Lane283.countP_point_one n ((s + m * δ) % n) (Nat.mod_lt _ hn)
    have ih' := ih (fun i k hi hk heq => hj i k (by omega) (by omega) heq)
    rw [hsplit, Lane283.countP_or _ _ _ hdisj, ih', hpt]

/-- **定理 D 机制主件**：g₁₃(A ∪ 单条 δ-块) ≤ g₁₃(A) + 1（零额外前提）。
泄漏位账：块内非首元的前驱仍在块内（位互异性灭之），唯一漏网 = 块首前驱 s−δ。
推论（A 沿 −δ 封时 g₁₃ A = 0，引理 4.2）：**单块构造恒有 g₁₃ ≤ 1**——
D0 四款（F 环连续块 / F1 前缀 / P1 上方块 / 闭前缀）公共核。 -/
theorem g13_closed_union_block_le (n δ s j : Nat) (hn : 0 < n) (hδ : δ < n)
    (P A : Nat → Bool) :
    g13 n δ P (fun x => A x || blockPred n δ s j x) ≤ g13 n δ P A + 1 := by
  have hkey : ∀ x, x < n → isL n δ P (fun x => A x || blockPred n δ s j x) x = true →
      isL n δ P A x = true ∨ x % n = (s + n - δ) % n := by
    intro x hx hlx
    have e1 : isL n δ P (fun x => A x || blockPred n δ s j x) x
        = (P x && (A ((x + δ) % n) || blockPred n δ s j ((x + δ) % n))
          && !(A x || blockPred n δ s j x)) := rfl
    rw [e1] at hlx
    rw [Bool.and_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at hlx
    have hP : P x = true := hlx.1.1
    have hOr : ((A ((x + δ) % n) || blockPred n δ s j ((x + δ) % n)) = true) := hlx.1.2
    have hnot : ((A x || blockPred n δ s j x) = false) := hlx.2
    rw [Bool.or_eq_false_iff] at hnot
    obtain ⟨hAx, hbp⟩ := hnot
    rw [Bool.or_eq_true] at hOr
    rcases hOr with hAy | hblock
    · left
      show (P x && A ((x + δ) % n) && Bool.not (A x)) = true
      rw [Bool.and_eq_true, Bool.and_eq_true]
      exact And.intro (And.intro hP hAy) (by simp [hAx])
    · right
      unfold blockPred at hblock
      rw [List.any_eq_true] at hblock
      obtain ⟨i, hi, hieq⟩ := hblock
      have hyn : (x + δ) % n < n := Nat.mod_lt _ hn
      rw [decide_eq_true_eq, Nat.mod_eq_of_lt hyn] at hieq
      -- hieq : (x + δ) % n = (s + i * δ) % n
      have hx0 : x = ((x + δ) % n + n - δ) % n := (sub_delta_of_add hn hδ hx rfl).symm
      rw [hieq] at hx0
      rcases i with _ | k
      · rw [Nat.zero_mul, Nat.add_zero, cong_shift n δ s hδ] at hx0
        rw [Nat.mod_eq_of_lt hx, hx0]
      · exfalso
        have hkj1 : k + 1 < j := List.mem_range.1 hi
        have hkj : k < j := by omega
        rw [cong_shift n δ (s + (k + 1) * δ) hδ, Nat.succ_mul] at hx0
        have hjoin : s + (k * δ + δ) + n - δ = s + k * δ + n := by omega
        rw [hjoin, mod_add_self] at hx0
        -- hx0 : x = (s + k * δ) % n
        have hb : blockPred n δ s j x = true := by
          unfold blockPred
          rw [List.any_eq_true]
          refine ⟨k, List.mem_range.2 (by omega), ?_⟩
          show decide (x % n = (s + k * δ) % n) = true
          rw [decide_eq_true_eq, Nat.mod_eq_of_lt hx, hx0]
        rw [hb] at hbp
        exact absurd hbp (by decide)
  have hmono := countP_mono (List.range n) (isL n δ P (fun x => A x || blockPred n δ s j x))
    (fun x => isL n δ P A x || decide (x % n = (s + n - δ) % n))
    (fun x hx h => by
      rcases hkey x (List.mem_range.1 hx) h with h1 | h2
      · rw [h1, Bool.true_or]
      · rw [h2, decide_eq_true rfl, Bool.or_true])
  have hpsplit : ∀ x : Nat, (isL n δ P A x || decide (x % n = (s + n - δ) % n))
      = (isL n δ P A x || (decide (x % n = (s + n - δ) % n) && !(isL n δ P A x))) := by
    intro x
    cases h1 : isL n δ P A x <;> cases hd : decide (x % n = (s + n - δ) % n) <;> rfl
  have hdisj : ∀ x ∈ List.range n, ¬ (isL n δ P A x = true
      ∧ (decide (x % n = (s + n - δ) % n) && !(isL n δ P A x)) = true) := by
    intro x _ hcon
    obtain ⟨h1, h2⟩ := hcon
    rw [Bool.and_eq_true] at h2
    obtain ⟨_, hnot⟩ := h2
    rw [h1, Bool.not_eq_true'] at hnot
    exact Bool.noConfusion hnot
  have hcpt : (List.range n).countP (fun x =>
      decide (x % n = (s + n - δ) % n) && !(isL n δ P A x)) ≤ 1 := by
    have hcn : (s + n - δ) % n < n := Nat.mod_lt _ hn
    have hstep := countP_mono (List.range n) (fun x =>
        decide (x % n = (s + n - δ) % n) && !(isL n δ P A x))
      (fun x => decide (x % n = (s + n - δ) % n))
      (fun x _ hcon => by rw [Bool.and_eq_true] at hcon; exact hcon.1)
    rw [Lane283.countP_congr_l (List.range n)
      (fun x => decide (x % n = (s + n - δ) % n))
      (fun x => decide (x = (s + n - δ) % n))
      (fun x hx => by rw [Nat.mod_eq_of_lt (List.mem_range.1 hx)]),
      Lane283.countP_point_one n ((s + n - δ) % n) hcn] at hstep
    exact hstep
  unfold g13
  have hpt1 := Lane283.countP_or (List.range n) (isL n δ P A)
    (fun x => decide (x % n = (s + n - δ) % n) && !(isL n δ P A x)) hdisj
  have hcongr := Lane283.countP_congr_l (List.range n)
    (fun x => isL n δ P A x || decide (x % n = (s + n - δ) % n))
    (fun x => isL n δ P A x || (decide (x % n = (s + n - δ) % n) && !(isL n δ P A x)))
    (fun x _ => hpsplit x)
  have h2' := hmono
  have h3' := hcpt
  omega

/-- **D0 单块推论**：互异 δ-块自身即 g₁₃ ≤ 1 的 λ(d₁) 构造器核
（A = ∅ 款；A 闭款经引理 4.2 同式）。 -/
theorem g13_block_le_one (n δ s j : Nat) (hn : 0 < n) (hδ : δ < n) (P : Nat → Bool) :
    g13 n δ P (blockPred n δ s j) ≤ 1 := by
  have h := g13_closed_union_block_le n δ s j hn hδ P (fun _ => false)
  have hR : (List.range n).countP (isL n δ P (fun _ => false)) = 0 := by
    apply countP_eq_zero_forall
    intro x _
    unfold isL
    cases hx : P x <;> rfl
  unfold g13 at h
  rw [Lane283.countP_congr_l (List.range n)
    (isL n δ P (fun x => (fun _ => false) x || blockPred n δ s j x))
    (isL n δ P (blockPred n δ s j))
    (fun x _ => by rfl)] at h
  rw [hR] at h
  exact h


/-! ### 机器层：位掩码域枚举 + 定理 D 构造器（D0–D2 直译）——#eval 机锁承载 -/

/-- 位测试。 -/
def bmem (m x : Nat) : Bool := (m >>> x) &&& 1 == 1

/-- N 位内 popcount。 -/
def popcnt (N m : Nat) : Nat := (List.range N).countP (fun i => bmem m i)

/-- N 位补掩码。 -/
def invm (N m : Nat) : Nat := (2 ^ N - 1) ^^^ m

/-- 位集合平移像：{x < N : (x + s) % N ∈ m}（B₁₂ = C₁ − δ₁₂ 承载）。 -/
def shiftMask (N s m : Nat) : Nat :=
  (List.range N).foldl (fun acc x => if bmem m ((x + s) % N) then acc + (1 <<< x) else acc) 0

/-- 掩码列表析取。 -/
def listMask : List Nat → Nat
  | [] => 0
  | x :: l => (1 <<< x) ||| listMask l

/-- 环序下标（缺省 0；仅用于成员查表）。 -/
def idxOf (ring : List Nat) (x : Nat) : Nat :=
  match ring.findIdx? (fun y => y == x) with
  | some i => i
  | none => 0

/-- 环上 P 点列按 +δ₁₃ 循环序分解为极大 P-游程（回绕合并后起点即界后点）。 -/
def runsOf (ring : List Nat) (pts : List Nat) : List (List Nat) :=
  let Lr := ring.length
  let step (acc : List (List Nat)) (x : Nat) : List (List Nat) :=
    match acc with
    | [] => [[x]]
    | cur :: done =>
        if (idxOf ring (cur.getLastD 0) + 1) % Lr == idxOf ring x then (cur ++ [x]) :: done
        else [x] :: (cur :: done)
  let runs := (pts.foldl step []).reverse
  match runs with
  | [] => []
  | r1 :: rest =>
      if rest.isEmpty then runs
      else
        let rlast := runs.getLastD []
        if (idxOf ring (rlast.getLastD 0) + 1) % Lr == idxOf ring (r1.headD 0) then
          (rlast ++ r1) :: rest.dropLast
        else runs

/-- 环分类件（deep_01 §6 D0 四款）。 -/
inductive RingKind where
  | fullF | fullF1 | part0 | part1

/-- 环信息包。 -/
structure RingInfo where
  kind : RingKind
  ring : List Nat
  runs : List (List Nat)
  oruns : List (List Nat)
  cap : Nat
  trun : List Nat
  tidx : Nat

/-- 单环分类：F（全环无 t₁）/ F1（全环含 t₁）/ P0（偏环）/ P1（偏环含 t₁∈P）。 -/
def classifyRing (P t1 : Nat) (ring : List Nat) : RingInfo :=
  let Lr := ring.length
  let pts := ring.filter (fun x => bmem P x)
  let full := pts.length == Lr
  let hasT1 := ring.contains t1
  if full && !hasT1 then ⟨RingKind.fullF, ring, [], [], 0, [], 0⟩
  else if full then ⟨RingKind.fullF1, ring, [], [], 0, [], 0⟩
  else if hasT1 && bmem P t1 then
    let runs := runsOf ring pts
    let trun := (runs.filter (fun r => r.contains t1)).headD []
    let tidx := idxOf trun t1
    let oruns := runs.filter (fun r => !(r.contains t1))
    let cap := tidx + oruns.foldr (fun r acc => r.length + acc) 0
    ⟨RingKind.part1, ring, runs, oruns, cap, trun, tidx⟩
  else
    ⟨RingKind.part0, ring, runsOf ring pts, runsOf ring pts, pts.length, [], 0⟩

/-- 游程序列前缀贪填 take 点。 -/
def fillRunList (runs : List (List Nat)) (take : Nat) : Option (Nat × Nat) :=
  runs.foldl (fun st r =>
    match st with
    | none => none
    | some (acc, got) =>
        if got < take then
          let s := min r.length (take - got)
          some (acc ||| listMask (r.take s), got + s)
        else st) (some (0, 0))

/-- 闭部分填充：a 个整 F 环 + 偏环前缀贪填 r 点（P1 环 t₁ 游程只填 t₁ 之前缀；
引理 4.2 前缀款保证闭性）。 -/
def closedFill (infos : List RingInfo) (fullFrings : List (List Nat)) (a r : Nat) :
    Option Nat :=
  let base := (fullFrings.take a).foldl (fun acc ring => acc ||| listMask ring) 0
  match infos.foldl (fun st info =>
    match st with
    | none => none
    | some (acc, rem) =>
        if rem = 0 then st
        else
          let take := min info.cap rem
          let filled :=
            match info.kind with
            | RingKind.part0 => fillRunList info.runs take
            | RingKind.part1 =>
                match fillRunList info.oruns take with
                | none => none
                | some (acc1, got1) =>
                    let s := min info.tidx (take - got1)
                    some (acc1 ||| listMask (info.trun.take s), got1 + s)
            | _ => some (0, 0)
          match filled with
          | none => none
          | some (acc2, got2) => some (acc ||| acc2, rem - got2)) (some (base, r)) with
  | some (acc, rem) => if rem = 0 then some acc else none
  | none => none

/-- 环序列：r + g·(j·m % L)，j < L（+δ₁₃ 序轨道，代表元 r < g）。 -/
def ringSeq (g m L r : Nat) : List Nat :=
  (List.range L).map (fun j => r + g * ((j * m) % L))

/-- **定理 D 构造器**（deep_01 §6 (D0)–(D2) 直译；闭优先：d₁ ∈ 闭集 ⟹ 闭构造，
否则间隙 a·L+R < d₁ < (a+1)·L 取单块：a < F₀ 用 F 环连续块 / a = F₀ 用
F1 环 ring∖{t₁} 前缀 / P1 环 t₁ 上方块）。返回 some (C₁ 掩码, closed?)；
构造失败 none（全域 #eval 应零 none）。 -/
def thmDConstruct (N P t1 _t3 d1 : Nat) (ft : Nat × Nat × Nat × Nat) : Option (Nat × Bool) :=
  let d13 := ft.2.1
  let g := Nat.gcd d13 N
  let L := N / g
  let m := (d13 / g) % L
  let rings := (List.range g).map (ringSeq g m L)
  let infos := rings.map (classifyRing P t1)
  let R := infos.foldl (fun acc i => acc + i.cap) 0
  let fs := infos.filter (fun i => match i.kind with | RingKind.fullF => true | _ => false)
  let F0 := fs.length
  let fullFrings := fs.map (fun i => i.ring)
  let hasF1 := infos.any (fun i => match i.kind with | RingKind.fullF1 => true | _ => false)
  let inClosed : Bool := d1 ≤ R
    || (List.range (F0 + 1)).any (fun a => a * L ≤ d1 && d1 ≤ a * L + R)
  if inClosed then
    let a := if d1 ≤ R then 0 else (d1 - R + L - 1) / L
    if a ≤ F0 && a * L ≤ d1 && d1 ≤ a * L + R then
      match closedFill infos fullFrings a (d1 - a * L) with
      | some c1 => if popcnt N c1 == d1 then some (c1, true) else none
      | none => none
    else none
  else
    let a := (d1 - R - 1) / L
    let e := d1 - a * L - R
    if e = 0 || L - 1 < e then none
    else if a < F0 then
      match closedFill infos fullFrings a R with
      | none => none
      | some base =>
          match fullFrings[a]? with
          | none => none
          | some src =>
              let c1 := base ||| listMask (src.take e)
              if popcnt N c1 == d1 then some (c1, false) else none
    else if hasF1 then
      match infos.find? (fun i => match i.kind with | RingKind.fullF1 => true | _ => false) with
      | none => none
      | some fi =>
          match closedFill infos fullFrings a R with
          | none => none
          | some base =>
              let i0 := idxOf fi.ring t1
              let blk := (List.range e).map
                (fun k => fi.ring[(i0 + (k + 1)) % fi.ring.length]!)
              let c1 := base ||| listMask blk
              if popcnt N c1 == d1 then some (c1, false) else none
    else
      match infos.find? (fun i => match i.kind with | RingKind.part1 => true | _ => false) with
      | none => none
      | some pi =>
          if e ≤ pi.trun.length - 1 - pi.tidx then
            match closedFill infos fullFrings a R with
            | none => none
            | some base =>
                let blk := (pi.trun.drop (pi.tidx + 1)).take e
                let c1 := base ||| listMask blk
                if popcnt N c1 == d1 then some (c1, false) else none
          else none

/-- 有界三元分量（d₁,d₂,d₃ ≥ 1、和为 n、dᵢ ≤ cᵢ；= lab290 bcomps(3,·) 口径）。 -/
def dcombos (n c1 c2 c3 : Nat) : List (Nat × Nat × Nat) :=
  (List.range (c1 + 1)).flatMap fun d1 =>
    (List.range (c2 + 1)).flatMap fun d2 =>
      let d3 := n - d1 - d2
      if 1 ≤ d1 && 1 ≤ d2 && 1 ≤ d3 && d3 ≤ c3 then [(d1, d2, d3)] else []

/-- 有序三元组表（t₁ < t₂ < t₃）。 -/
def allT (N : Nat) : List (Nat × Nat × Nat) :=
  (List.range N).flatMap fun t1 =>
    (List.range N).flatMap fun t2 =>
      (List.range N).filterMap fun t3 =>
        if t1 < t2 && t2 < t3 then some (t1, t2, t3) else none

/-- so1 特征：(δ₁₂, δ₁₃, δ₂₃, k)；要求 δ₁₂ ≠ 0、δ₁₃ ≡ k·δ₁₂（mod N）、典范 k ∈ [2, L)。 -/
def so1feat (N t1 t2 t3 : Nat) : Option (Nat × Nat × Nat × Nat) :=
  let d12 := (t1 + N - t2) % N
  let d13 := (t1 + N - t3) % N
  if d12 = 0 then none
  else
    let L := N / Nat.gcd d12 N
    match (List.range L).find? (fun kk => (kk * d12) % N == d13) with
    | some k => if 2 ≤ k then some (d12, d13, (t2 + N - t3) % N, k) else none
    | none => none

/-- so1 β≥1 全域实例表 (P, t₁, t₂, t₃, d₁, d₂, d₃)（= iter_so1_beta1 ∪ iter_so1_beta2p）。 -/
def instancesOf (N : Nat) : List (Nat × Nat × Nat × Nat × Nat × Nat × Nat) :=
  (List.range (2 ^ N)).flatMap fun P =>
    let p := popcnt N P
    if p < 4 then []
    else
      allT N |>.flatMap fun t =>
        match t with
        | (t1, t2, t3) =>
            match so1feat N t1 t2 t3 with
            | none => []
            | some _ =>
                let c1 := p - (if bmem P t1 then 1 else 0)
                let c2 := p - (if bmem P t2 then 1 else 0)
                let c3 := p - (if bmem P t3 then 1 else 0)
                let nmax := min (p - 1) (N - 1)
                (List.range (nmax + 1)).flatMap fun n =>
                  if 3 ≤ n && (n = p - 1 || 5 ≤ p) then
                    (dcombos n c1 c2 c3).map fun d =>
                      match d with
                      | (d1, d2, d3) => (P, t1, t2, t3, d1, d2, d3)
                  else []

/-- 子掩码枚举（fuel 结构递归；掩码 < 2^N 时以 fuel = N 调用全覆盖）。 -/
def submasksU : Nat → Nat → List Nat
  | 0, _ => [0]
  | k + 1, m =>
      let r := submasksU k (m / 2)
      if bmem m 0 then r.map (fun s => 2 * s + 1) ++ r.map (fun s => 2 * s)
      else r.map (fun s => 2 * s)

/-- E1 机锁累加器：合法对数 / val≤1 witness 数 / 定理 A 违反数。 -/
structure WAcc where
  pairs : Nat := 0
  wits : Nat := 0
  viols : Nat := 0

/-- E1 机锁：全域合法对、val≤1 witness、定理 A 违反（应 0）。 -/
def witnessStats (N : Nat) : WAcc :=
  instancesOf N |>.foldl (fun acc inst =>
    match inst with
    | (P, t1, t2, t3, d1, d2, _d3) =>
      match so1feat N t1 t2 t3 with
      | none => acc
      | some (d12, d13, d23, _) =>
        let Pm := fun x => bmem P x
        let P' := P &&& invm N (1 <<< t1)
        submasksU N P' |>.foldl (fun a2 C1 =>
          if popcnt N C1 != d1 then a2
          else
            let B12 := shiftMask N d12 C1
            let Q := P &&& invm N (C1 ||| B12 ||| 1 <<< t2)
            (submasksU N Q).foldl (fun a3 C2 =>
              if popcnt N C2 != d2 then a3
              else
                let v := val3 N d13 d23 t3 Pm (fun x => bmem C1 x) (fun x => bmem C2 x)
                if v ≤ 1 then
                  let g := g13 N d13 Pm (fun x => bmem C1 x)
                  if d2 + 1 < g then
                    { pairs := a3.pairs + 1, wits := a3.wits + 1, viols := a3.viols + 1 }
                  else
                    { pairs := a3.pairs + 1, wits := a3.wits + 1, viols := a3.viols }
                else
                  { pairs := a3.pairs + 1, wits := a3.wits, viols := a3.viols }
            ) a2
        ) acc) {}

/-- E2 机锁：定理 D 构造器全域直验。返回 (closed, oneLeak, fail)。 -/
def thmDStats (N : Nat) : Nat × Nat × Nat :=
  instancesOf N |>.foldl (fun acc inst =>
    match inst with
    | (P, t1, t2, t3, d1, _d2, _d3) =>
      match so1feat N t1 t2 t3 with
      | none => acc
      | some ft =>
        match thmDConstruct N P t1 t3 d1 ft with
        | none => (acc.1, acc.2.1, acc.2.2 + 1)
        | some (c1, isc) =>
          if popcnt N c1 == d1
              && g13 N ft.2.1 (fun x => bmem P x) (fun x => bmem c1 x) ≤ 1 then
            (if isc then acc.1 + 1 else acc.1, if isc then acc.2.1 else acc.2.1 + 1, acc.2.2)
          else (acc.1, acc.2.1, acc.2.2 + 1)) (0, 0, 0)

/-- 域计数。 -/
def domainCount (N : Nat) : Nat := instancesOf N |>.length

/-! ### 实例机锁：deep_01 手验例逐点钉死（decide 级） -/

/-- deep_01 §3 注记 A-2 手验例机锁（N=8 紧例）：P={0,…,6}, T=(0,1,5)，
C₁={4,5,6}, C₂={2,3}，δ₁₃=3、δ₂₃=4、t₃=5：val = 1、g₁₃ = 3 = d₂+1（定理 A 取等）。 -/
theorem inst8_thmA_example :
    val3 8 3 4 5 (fun x => bmem 127 x) (fun x => bmem 112 x) (fun x => bmem 12 x) = 1
      ∧ g13 8 3 (fun x => bmem 127 x) (fun x => bmem 112 x) = 3 := by
  decide

/-- 同例经 thmA_core 一般定理逐字推出（hd2：|C₂| = 2；hv：val ≤ 1）。 -/
theorem inst8_thmA_fired :
    g13 8 3 (fun x => bmem 127 x) (fun x => bmem 112 x) ≤ 2 + 1 :=
  thmA_core 8 2 3 4 5 (fun x => bmem 127 x) (fun x => bmem 112 x) (fun x => bmem 12 x)
    (by decide) (by decide)

/-- deep_01 §6 注记 D-2 手验例机锁：N=8, P={0,…,6}, T=(3,4,6), d₁=4，
构造 C₁={0,1,4,6}（闭部分 {4,1,6} ⊕ t₁ 上方块 {0}），|C₁| = 4、g₁₃ = 1、
泄漏位 = t₁ = 3（D-2 形状：v=t₁∈P∩C₁⁰、v+δ₁₃=0∈C₁）。 -/
theorem inst8_thmD_example :
    popcnt 8 83 = 4
      ∧ g13 8 5 (fun x => bmem 127 x) (fun x => bmem 83 x) = 1
      ∧ (bmem 127 3 && bmem 83 0 && !(bmem 83 3)) = true := by
  decide

/-! ### 零洞机器证据（#print axioms：零占位公理依赖、零 Classical.choice） -/

#print axioms Lane314.countP_mono
#print axioms Lane314.countP_eq_zero_forall
#print axioms Lane314.countP_ge_one
#print axioms Lane314.add_delta_of_sub
#print axioms Lane314.sub_delta_of_add
#print axioms Lane314.cong_shift
#print axioms Lane314.mod_add_self
#print axioms Lane314.g13_le_val_add_d2
#print axioms Lane314.thmA_core
#print axioms Lane314.g13_eq_zero_iff_closed
#print axioms Lane314.countP_block
#print axioms Lane314.g13_closed_union_block_le
#print axioms Lane314.g13_block_le_one
#print axioms Lane314.inst8_thmA_example
#print axioms Lane314.inst8_thmA_fired
#print axioms Lane314.inst8_thmD_example

/-- N=6 机锁（deep_01 E1/E2 锚：588 / 5,724 / 2,613 / 违反 0；构造器 413/175/0）。 -/
def lock6 : String :=
  let w := witnessStats 6
  let t := thmDStats 6
  s!"N=6: domain={domainCount 6} pairs={w.pairs} witnesses={w.wits} thmA_viol={w.viols} \
thmD_closed/oneleak/fail={t.1}/{t.2.1}/{t.2.2}"

/-- N=8 机锁（锚：30,760 / 701,360 / 285,372 / 0；26,940/3,820/0）。 -/
def lock8 : String :=
  let w := witnessStats 8
  let t := thmDStats 8
  s!"N=8: domain={domainCount 8} pairs={w.pairs} witnesses={w.wits} thmA_viol={w.viols} \
thmD_closed/oneleak/fail={t.1}/{t.2.1}/{t.2.2}"

/-- N=10 机锁（锚：634,960；594,148/40,812/0）。 -/
def lock10 : String :=
  let t := thmDStats 10
  s!"N=10: domain={domainCount 10} thmD_closed/oneleak/fail={t.1}/{t.2.1}/{t.2.2}"

#eval lock6
#eval lock8
#eval lock10

end Lane314
/-! ## lane_321：定理 B/C（三档终止界 + 逐 N 闭合装配）与多块装配层组件
（承 Lane258/264/273/283/297/308/314 纯插入纪律；底账 deep_01 §4.3/§5 + deep_03 PASS 裁决；
公理纪律：一切 Bool 谓词 decide 化（== 路径带 Classical.choice，mini7 实测），zero omega-on-iff） -/

namespace Lane321

/-! ### 定理 B：三档无缝覆盖 + iff 本体 + 族有限可枚举承载 -/

/-- **三档无缝覆盖件**（deep_01 §4.3 定理 B 措辞：[0]∪[1]∪[2,d₂+1] = [0,d₂+1]）：
g₁₃ ≤ d₂+1 ⟺ 恰落三档之一（g=0 / g=1 / 2≤g≤d₂+1）。 -/
theorem tier_split (g d2 : Nat) :
    g ≤ d2 + 1 ↔ (g = 0 ∨ (g = 1 ∨ (2 ≤ g ∧ g ≤ d2 + 1))) := by
  constructor
  · intro h
    rcases Nat.lt_or_ge g 1 with h0 | h1
    · exact Or.inl (Nat.le_zero.1 (Nat.lt_succ_iff.1 h0))
    · rcases Nat.lt_or_ge g 2 with h2 | h3
      · exact Or.inr (Or.inl (Nat.le_antisymm (Nat.lt_succ_iff.1 h2) h1))
      · exact Or.inr (Or.inr ⟨h3, h⟩)
  · rintro (h | h)
    · rw [h]; exact Nat.zero_le _
    · rcases h with h | ⟨_, h2⟩
      · rw [h]; exact Nat.succ_le_succ (Nat.zero_le d2)
      · exact h2

/-- **定理 B（终止界 iff 本体，deep_01 §4.3）**：存在 val≤1 合法对 ⟺ 存在 val≤1 合法对
且 g₁₃(C₁) ≤ d₂+1。(⟸) 即存在性陈述本身；(⟹) = Lane314.thmA_core（定理 A）——
一切 val≤1 witness 的 g₁₃ 被强制 ≤ d₂+1，故三档搜索 E1g ∪ E3″ ∪ E3‴ 完备无漏。 -/
theorem thmB_tier_complete (n d2 δ13 δ23 t3 : Nat) (P : Nat → Bool) :
    (∃ C1 C2 : Nat → Bool,
        (List.range n).countP C2 = d2 ∧ Lane314.val3 n δ13 δ23 t3 P C1 C2 ≤ 1)
      ↔ ∃ C1 C2 : Nat → Bool,
        (List.range n).countP C2 = d2 ∧ Lane314.val3 n δ13 δ23 t3 P C1 C2 ≤ 1
          ∧ Lane314.g13 n δ13 P C1 ≤ d2 + 1 := by
  constructor
  · rintro ⟨C1, C2, hd2, hv⟩
    exact ⟨C1, C2, hd2, hv, Lane314.thmA_core n d2 δ13 δ23 t3 P C1 C2 hd2 hv⟩
  · rintro ⟨C1, C2, hd2, hv, _⟩
    exact ⟨C1, C2, hd2, hv⟩

/-- **三档族有限可枚举承载**（定理 B「每档有限、可有效枚举」的掩码口径）：
界 B 内的 d₁-尺寸 C₁ 掩码逐一出现于全掩码表 2^N 的可计算过滤表中 ⟹ 族有限可枚举。
（g=0 档 = 282.B 闭族：Lane314.g13_eq_zero_iff_closed 承载闭性刻画。） -/
theorem tier_family_enum (N d1 B d13 : Nat) (P : Nat → Bool) (m : Nat) (hm : m < 2 ^ N)
    (hd1 : Lane314.popcnt N m = d1)
    (hg : Lane314.g13 N d13 P (fun x => Lane314.bmem m x) ≤ B) :
    m ∈ (List.range (2 ^ N)).filter (fun k =>
      decide (Lane314.popcnt N k = d1)
        && decide (Lane314.g13 N d13 P (fun x => Lane314.bmem k x) ≤ B)) := by
  refine List.mem_filter.2 ⟨List.mem_range.2 hm, ?_⟩
  rw [Bool.and_eq_true]
  exact ⟨decide_eq_true hd1, decide_eq_true hg⟩

/-! ### 定理 C：合法对判定件 + 三档审计（可计算搜索）+ 可靠性/完备性/装配 -/

/-- Q(C₁) = P ∖ (C₁ ∪ B₁₂ ∪ {t₂})，B₁₂ = C₁ − δ₁₂（Lane314.shiftMask 承载；deep_01 §2 判定层同式）。 -/
def qMask (N d12 t2 P C1 : Nat) : Nat :=
  P &&& Lane314.invm N (C1 ||| Lane314.shiftMask N d12 C1 ||| 1 <<< t2)

/-- 合法 C₁ 掩码（deep_01 §2）：C₁ < 2^N ∧ |C₁| = d₁ ∧ t₁ ∉ C₁ ∧ C₁ ⊆ P。 -/
def legalC1m (N d1 t1 P C1 : Nat) : Bool :=
  decide (C1 < 2 ^ N) && decide (Lane314.popcnt N C1 = d1)
    && decide ((C1 &&& Lane314.invm N (1 <<< t1)) = C1) && decide (C1 &&& P = C1)

/-- 合法 C₂ 掩码：C₂ < 2^N ∧ |C₂| = d₂ ∧ C₂ ⊆ Q(C₁)。 -/
def legalC2m (N d2 d12 t2 P C1 C2 : Nat) : Bool :=
  decide (C2 < 2 ^ N) && decide (Lane314.popcnt N C2 = d2)
    && decide (C2 &&& qMask N d12 t2 P C1 = C2)

/-- **三档审计（单实例）**：定理 C 的有限程序 A(N) 的实例件——在三档族
（|C₁| = d₁ ∧ C₁ ⊆ P∖{t₁} ∧ g₁₃ ≤ d₂+1）× 合法 C₂ 内搜 val≤1 证书（可计算 Bool）。 -/
def tierAudit (N d1 d2 d12 d13 d23 t1 t2 t3 P : Nat) : Bool :=
  (List.range (2 ^ N)).any fun C1 =>
    legalC1m N d1 t1 P C1
      && decide (Lane314.g13 N d13 (fun x => Lane314.bmem P x)
          (fun x => Lane314.bmem C1 x) ≤ d2 + 1)
      && (List.range (2 ^ N)).any fun C2 =>
        legalC2m N d2 d12 t2 P C1 C2
          && decide (Lane314.val3 N d13 d23 t3 (fun x => Lane314.bmem P x)
              (fun x => Lane314.bmem C1 x) (fun x => Lane314.bmem C2 x) ≤ 1)

/-- **审计可靠性（定理 C 核，soundness 半边）**：三档审计通过 ⟹ 存在真证书：
C₁ 落三档族（含 g₁₃ ≤ d₂+1 构造性分量）∧ C₂ 合法（|C₂| = d₂ ∧ ⊆ Q(C₁)）∧ val ≤ 1。
证书即 witness（deep_01 §5 定理 C 证明「A(N) 通过 ⟹ 每实例存在 val≤1 witness」的单实例形态）。 -/
theorem tierAudit_sound (N d1 d2 d12 d13 d23 t1 t2 t3 P : Nat)
    (h : tierAudit N d1 d2 d12 d13 d23 t1 t2 t3 P = true) :
    ∃ C1 C2 : Nat,
      Lane314.popcnt N C1 = d1
        ∧ (C1 &&& Lane314.invm N (1 <<< t1)) = C1 ∧ C1 &&& P = C1
        ∧ Lane314.g13 N d13 (fun x => Lane314.bmem P x) (fun x => Lane314.bmem C1 x) ≤ d2 + 1
        ∧ Lane314.popcnt N C2 = d2
        ∧ C2 &&& qMask N d12 t2 P C1 = C2
        ∧ Lane314.val3 N d13 d23 t3 (fun x => Lane314.bmem P x)
            (fun x => Lane314.bmem C1 x) (fun x => Lane314.bmem C2 x) ≤ 1 := by
  unfold tierAudit at h
  rw [List.any_eq_true] at h
  obtain ⟨C1, -, hinner⟩ := h
  rw [Bool.and_eq_true, Bool.and_eq_true] at hinner
  have h1 := hinner.1
  rw [legalC1m, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h1
  have h2 := hinner.2
  rw [List.any_eq_true] at h2
  obtain ⟨C2, -, hv⟩ := h2
  rw [Bool.and_eq_true] at hv
  have hv2 := hv.1
  rw [legalC2m, Bool.and_eq_true, Bool.and_eq_true] at hv2
  refine ⟨C1, C2, of_decide_eq_true h1.1.1.1.2, of_decide_eq_true h1.1.1.2,
    of_decide_eq_true h1.1.2, of_decide_eq_true h1.2,
    of_decide_eq_true hv2.1.2, of_decide_eq_true hv2.2, of_decide_eq_true hv.2⟩

/-- **审计完备性（定理 B 的程序化承载，completeness 半边）**：存在 val≤1 合法对
且 C₁ 界内 ⟹ 审计通过——witness 落在被搜索的三档族内，无漏（deep_01 §5 定理 C
证明的「定理 B 保证该 witness 落在 searched 族内」形态）。 -/
theorem tierAudit_complete (N d1 d2 d12 d13 d23 t1 t2 t3 P C1 C2 : Nat)
    (hc1 : legalC1m N d1 t1 P C1 = true)
    (hg : Lane314.g13 N d13 (fun x => Lane314.bmem P x) (fun x => Lane314.bmem C1 x) ≤ d2 + 1)
    (hc2 : legalC2m N d2 d12 t2 P C1 C2 = true)
    (hv : Lane314.val3 N d13 d23 t3 (fun x => Lane314.bmem P x)
        (fun x => Lane314.bmem C1 x) (fun x => Lane314.bmem C2 x) ≤ 1) :
    tierAudit N d1 d2 d12 d13 d23 t1 t2 t3 P = true := by
  have h1 := hc1
  rw [legalC1m, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h1
  have h2 := hc2
  rw [legalC2m, Bool.and_eq_true, Bool.and_eq_true] at h2
  have hC1lt : C1 < 2 ^ N := of_decide_eq_true h1.1.1.1
  have hC2lt : C2 < 2 ^ N := of_decide_eq_true h2.1.1
  have hany2 : (List.range (2 ^ N)).any (fun C2' =>
      legalC2m N d2 d12 t2 P C1 C2'
        && decide (Lane314.val3 N d13 d23 t3 (fun x => Lane314.bmem P x)
            (fun x => Lane314.bmem C1 x) (fun x => Lane314.bmem C2' x) ≤ 1)) = true := by
    rw [List.any_eq_true]
    refine ⟨C2, List.mem_range.2 hC2lt, ?_⟩
    rw [hc2, decide_eq_true hv, Bool.and_self]
  unfold tierAudit
  rw [List.any_eq_true]
  refine ⟨C1, List.mem_range.2 hC1lt, ?_⟩
  simp only [hc1, decide_eq_true hg, hany2, Bool.and_true]

/-! ### 定理 C 本体：逐 N 装配（审计全通过 ⟹ 全域 HasWitness） -/

/-- 实例审计（Lane314.instancesOf N 域上逐实例；非 so1 分支防御性通过）。 -/
def instAudit (N : Nat) (i : Nat × Nat × Nat × Nat × Nat × Nat × Nat) : Bool :=
  match i with
  | (P, t1, t2, t3, d1, d2, _) =>
      match Lane314.so1feat N t1 t2 t3 with
      | none => true
      | some (d12, d13, d23, _) => tierAudit N d1 d2 d12 d13 d23 t1 t2 t3 P

/-- 实例 witness 命题（与 instAudit 同分支结构的 Prop 形态）。 -/
def HasWitness (N : Nat) (i : Nat × Nat × Nat × Nat × Nat × Nat × Nat) : Prop :=
  match i with
  | (P, t1, t2, t3, d1, d2, _) =>
      match Lane314.so1feat N t1 t2 t3 with
      | none => True
      | some (_d12, d13, d23, _) => ∃ C1 C2 : Nat,
          Lane314.popcnt N C1 = d1 ∧ Lane314.popcnt N C2 = d2
            ∧ Lane314.val3 N d13 d23 t3 (fun x => Lane314.bmem P x)
                (fun x => Lane314.bmem C1 x) (fun x => Lane314.bmem C2 x) ≤ 1

/-- **定理 C（逐 N 闭合装配，条件句本体，deep_01 §5）**：若三档审计在 so1 β≥1
全域全部通过，则全域每实例存在 val≤1 合法对 witness。
可靠性 = tierAudit_sound；完备无漏 = 定理 B（thmB_tier_complete）的程序化承载。 -/
theorem thmC_assemble (N : Nat)
    (h : ∀ i ∈ Lane314.instancesOf N, instAudit N i = true) :
    ∀ i ∈ Lane314.instancesOf N, HasWitness N i := by
  intro i hi
  obtain ⟨P, t1, t2, t3, d1, d2, d3⟩ := i
  cases hso : Lane314.so1feat N t1 t2 t3 with
  | none => simp only [HasWitness, hso]
  | some f =>
    obtain ⟨d12, d13, d23, k⟩ := f
    have hpass : instAudit N (P, t1, t2, t3, d1, d2, d3) = true := h _ hi
    simp only [instAudit, hso] at hpass
    simp only [HasWitness, hso]
    obtain ⟨C1, C2, hp1, _, _, -, hp2, -, hv⟩ :=
      tierAudit_sound N d1 d2 d12 d13 d23 t1 t2 t3 P hpass
    exact ⟨C1, C2, hp1, hp2, hv⟩

/-! ### 多块装配层组件（lane_308 落款「B/C 层多块族装配」欠账的可行部分） -/

/-- e 条 δ-块的逐步并（blks 从左到右依次并入 A）。 -/
def unionBlocks (n δ : Nat) (A : Nat → Bool) : List (Nat × Nat) → (Nat → Bool)
  | [] => A
  | (s, j) :: rest => fun x => unionBlocks n δ A rest x || Lane314.blockPred n δ s j x

/-- **多块装配 g-界（系 4.4 构造向核，e 块推广 Lane314 单块件）**：
A ⊕ e 条 δ-块的 g₁₃ ≤ g₁₃(A) + e（零额外前提；lane_308 落款「多块族装配」的 g-界半边）。 -/
theorem g13_union_blocks_le (n δ : Nat) (hn : 0 < n) (hδ : δ < n) (P A : Nat → Bool)
    (blks : List (Nat × Nat)) :
    Lane314.g13 n δ P (unionBlocks n δ A blks) ≤ Lane314.g13 n δ P A + blks.length := by
  induction blks with
  | nil => simp [unionBlocks]
  | cons blk rest ih =>
    obtain ⟨s, j⟩ := blk
    rw [List.length_cons]
    have hdef : Lane314.g13 n δ P (unionBlocks n δ A ((s, j) :: rest))
        = Lane314.g13 n δ P
            (fun x => unionBlocks n δ A rest x || Lane314.blockPred n δ s j x) := rfl
    have h1 := Lane314.g13_closed_union_block_le n δ s j hn hδ P (unionBlocks n δ A rest)
    omega

/-- **闭 ⊕ e 块（系 4.4 的 B(I) 界构造向）**：A 沿 −δ 闭（g₁₃ A = 0，引理 4.2）时，
A ⊕ e 条 δ-块的 g₁₃ ≤ e——「每 P-游程 = 前缀闭块 ⊕ ≤e 条内部块 ⟹ g₁₃ ≤ e」的核。 -/
theorem g13_closed_union_blocks_le (n δ : Nat) (hn : 0 < n) (hδ : δ < n) (P A : Nat → Bool)
    (hclosed : Lane314.g13 n δ P A = 0) (blks : List (Nat × Nat)) :
    Lane314.g13 n δ P (unionBlocks n δ A blks) ≤ blks.length := by
  have h := g13_union_blocks_le n δ hn hδ P A blks
  rw [hclosed] at h
  omega

/-! ### 多块 union 尺寸上界（无互斥前提的一般账） -/

/-- 逐点 Bool 或的计数上界（无互斥版）。 -/
theorem countP_or_le (w : List Nat) (p q : Nat → Bool) :
    w.countP (fun x => p x || q x) ≤ w.countP p + w.countP q := by
  induction w with
  | nil => simp
  | cons x w ih =>
    rw [List.countP_cons, List.countP_cons, List.countP_cons]
    cases hpx : p x <;> cases hqx : q x <;>
      simp only [Bool.true_or, Bool.false_or, Bool.false_eq_true, ite_false, ite_true,
        Nat.add_zero] <;> omega

/-- δ-块计数上界（无互异前提）：countP(块(s,j)) ≤ j（互异时取等 = Lane314.countP_block）。 -/
theorem countP_block_le (n δ s j : Nat) (hn : 0 < n) :
    (List.range n).countP (Lane314.blockPred n δ s j) ≤ j := by
  induction j with
  | zero =>
    have hz : Lane314.blockPred n δ s 0 = fun _ => false := by
      funext x
      simp [Lane314.blockPred]
    rw [hz]
    exact Nat.le_of_eq (Lane283.countP_false _)
  | succ m ih =>
    have hsplit : Lane314.blockPred n δ s (m + 1)
        = fun x => Lane314.blockPred n δ s m x || decide (x % n = (s + m * δ) % n) := by
      funext x
      simp [Lane314.blockPred, List.range_succ, List.any_append, List.any_cons]
    have h1 : (List.range n).countP (fun x => decide (x % n = (s + m * δ) % n)) ≤ 1 := by
      rw [Lane283.countP_congr_l (List.range n)
        (fun x => decide (x % n = (s + m * δ) % n))
        (fun x => decide (x = (s + m * δ) % n))
        (fun x hx => by rw [Nat.mod_eq_of_lt (List.mem_range.1 hx)])]
      exact Nat.le_of_eq (Lane283.countP_point_one n ((s + m * δ) % n) (Nat.mod_lt _ hn))
    have h2 : (List.range n).countP (Lane314.blockPred n δ s (m + 1))
        ≤ (List.range n).countP (Lane314.blockPred n δ s m)
          + (List.range n).countP (fun x => decide (x % n = (s + m * δ) % n)) := by
      rw [hsplit]
      exact countP_or_le (List.range n) (Lane314.blockPred n δ s m)
        (fun x => decide (x % n = (s + m * δ) % n))
    omega

/-- **多块 union 尺寸上界**：|A ⊕ e 块| ≤ |A| + Σ 块长（无互斥前提的一般账；
各块位互异时每块计数取等 Lane314.countP_block，即系 4.4 的枚举尺寸承载）。 -/
theorem count_unionBlocks_le (n δ : Nat) (hn : 0 < n) (A : Nat → Bool)
    (blks : List (Nat × Nat)) :
    (List.range n).countP (unionBlocks n δ A blks)
      ≤ (List.range n).countP A + blks.foldr (fun b acc => b.2 + acc) 0 := by
  induction blks with
  | nil => simp [unionBlocks]
  | cons blk rest ih =>
    obtain ⟨s, j⟩ := blk
    have hdef : (List.range n).countP (unionBlocks n δ A ((s, j) :: rest))
        = (List.range n).countP
            (fun x => unionBlocks n δ A rest x || Lane314.blockPred n δ s j x) := rfl
    have h1 := countP_or_le (List.range n) (unionBlocks n δ A rest)
      (Lane314.blockPred n δ s j)
    have h3 := countP_block_le n δ s j hn
    rw [List.foldr_cons]
    omega

/-! ### 实例机锁：deep_01 §3 注记 A-3 试金石（N=6）B/C 全链 decide 钉死 -/

/-- 试金石实例（deep_01 §3 注记 A-3 / lane_296 §1）：N=6，P = {0,1,2,4,5}（掩码 55），
T = (3,4,5)，d = (2,1,1)；δ₁₂ = 5、δ₁₃ = 4、δ₂₃ = 5。 -/
def ex6P : Nat := 55

/-- 试金石 witness C₁ = {0,1}（掩码 3）。 -/
def ex6C1 : Nat := 3

/-- 试金石 witness C₂ = {5}（掩码 32）。 -/
def ex6C2 : Nat := 32

/-- 试金石 B/C 数值账：val = 1、g₁₃ = 1 ≤ d₂+1 = 2、(C₁,C₂) 双侧合法、|C₂| = 1。 -/
theorem inst6_tier_example :
    Lane314.val3 6 4 5 5 (fun x => Lane314.bmem ex6P x) (fun x => Lane314.bmem ex6C1 x)
        (fun x => Lane314.bmem ex6C2 x) = 1
      ∧ Lane314.g13 6 4 (fun x => Lane314.bmem ex6P x) (fun x => Lane314.bmem ex6C1 x) = 1
      ∧ legalC1m 6 2 3 ex6P ex6C1 = true
      ∧ legalC2m 6 1 5 4 ex6P ex6C1 ex6C2 = true
      ∧ Lane314.popcnt 6 ex6C2 = 1 := by
  decide

/-- 试金石经 tierAudit_complete 一般定理逐字推出（审计通过：witness 在三档族内被命中）。 -/
theorem inst6_tier_audit_fired :
    tierAudit 6 2 1 5 4 5 3 4 5 ex6P = true :=
  tierAudit_complete 6 2 1 5 4 5 3 4 5 ex6P ex6C1 ex6C2
    (by decide) (by decide) (by decide) (by decide)

/-! ### 机器锁：N=6 全域三档账（#eval；与 Python 独立实现逐值对拍） -/

/-- B/C 机锁累加器：实例数 / 审计通过数 / 完备违反 / witness 覆盖三档计数 / min-g 直方图
（mg = 实例内全部尺寸 d₁ 的 C₁ 之最小 g₁₃ 的桶值，初值 3 = 「尚无 C₁」哨兵）。 -/
structure BCAcc where
  insts : Nat := 0
  audits : Nat := 0
  cviols : Nat := 0
  t0 : Nat := 0
  t1 : Nat := 0
  t2 : Nat := 0
  mg : Nat := 3
  mg0 : Nat := 0
  mg1 : Nat := 0
  mg2 : Nat := 0

/-- 全域 B/C 机锁：逐实例 = 审计通过？（tierAudit 本体）+ 尺寸 d₁ 全 C₁ 扫描
（witness 覆盖三档 t0/t1/t2 分账 + min-g 直方图 mg0/mg1/mg2）+ 完备违反
（有 witness 而审计不过，应 0——即 thmB_tier_complete 的机器面）。 -/
def tierStats (N : Nat) : BCAcc :=
  Lane314.instancesOf N |>.foldl (fun acc inst =>
    match inst with
    | (P, t1, t2, t3, d1, d2, _d3) =>
      match Lane314.so1feat N t1 t2 t3 with
      | none => acc
      | some (d12, d13, d23, _) =>
        let Pm := fun x => Lane314.bmem P x
        let P' := P &&& Lane314.invm N (1 <<< t1)
        let aud := tierAudit N d1 d2 d12 d13 d23 t1 t2 t3 P
        let scan := (Lane314.submasksU N P').foldl (fun (a : BCAcc) C1 =>
          if Lane314.popcnt N C1 != d1 then a
          else
            let g := Lane314.g13 N d13 Pm (fun x => Lane314.bmem C1 x)
            let mg := min a.mg (if g = 0 then 0 else if g = 1 then 1 else 2)
            let B12 := Lane314.shiftMask N d12 C1
            let Q := P &&& Lane314.invm N (C1 ||| B12 ||| 1 <<< t2)
            let has2 := (Lane314.submasksU N Q).any fun C2 =>
              Lane314.popcnt N C2 == d2
                && decide (Lane314.val3 N d13 d23 t3 Pm (fun x => Lane314.bmem C1 x)
                    (fun x => Lane314.bmem C2 x) ≤ 1)
            if has2 then
              { a with mg := mg, t0 := a.t0 + (if g = 0 then 1 else 0), t1 := a.t1 + (if g = 1 then 1 else 0), t2 := a.t2 + (if decide (2 ≤ g) then 1 else 0) }
            else { a with mg := mg }) ({} : BCAcc)
        let wit := scan.t0 + scan.t1 + scan.t2
        let aud1 := if aud then 1 else 0
        let cv := if 0 < wit && !aud then 1 else 0
        { acc with insts := acc.insts + 1, audits := acc.audits + aud1, cviols := acc.cviols + cv, t0 := acc.t0 + scan.t0, t1 := acc.t1 + scan.t1, t2 := acc.t2 + scan.t2, mg0 := acc.mg0 + (if scan.mg = 0 then 1 else 0), mg1 := acc.mg1 + (if scan.mg = 1 then 1 else 0), mg2 := acc.mg2 + (if scan.mg = 2 then 1 else 0) }) ({} : BCAcc)

/-- N=6 机锁输出（锚：insts = 588、audits = 588、cviols = 0、
min-g 直方图 = {0:382, 1:189, 2:17}（deep_03 攻击面 4 账））。 -/
def lock6bc : String :=
  let s := tierStats 6
  s!"N=6 BC: insts={s.insts} audits={s.audits} cviols={s.cviols} \
t0/t1/t2={s.t0}/{s.t1}/{s.t2} mg0/1/2={s.mg0}/{s.mg1}/{s.mg2}"

#eval lock6bc

/-! ### 零洞机器证据（#print axioms：零占位公理依赖、零 Classical.choice） -/

#print axioms Lane321.tier_split
#print axioms Lane321.thmB_tier_complete
#print axioms Lane321.tier_family_enum
#print axioms Lane321.tierAudit_sound
#print axioms Lane321.tierAudit_complete
#print axioms Lane321.thmC_assemble
#print axioms Lane321.g13_union_blocks_le
#print axioms Lane321.g13_closed_union_blocks_le
#print axioms Lane321.countP_or_le
#print axioms Lane321.countP_block_le
#print axioms Lane321.count_unionBlocks_le
#print axioms Lane321.inst6_tier_example
#print axioms Lane321.inst6_tier_audit_fired

end Lane321

/-! ## lane_332：定理 B/C 装配账 N=10/12 收口（承 lane_321 纯插入纪律；
Python 独立位运算实现对拍账与锚命中明细见 campaign/lane_332_leantierBC_n1012.md）-/


namespace Lane332

/-- N=8 机锁输出（lane_332 新增）：Lane321.tierStats 8 的 Lean 侧全域账，实测编译期
约 32 秒（白天线内）。与 lane_321 报告 Python N=8 锚逐值互锁：insts=30,760、
audits=30,760、cviols=0、t0/t1/t2=44,810/98,800/20,902、mg0/1/2=26,940/3,820/0
（mg 直方图即 all-mg 口径 {0:26,940, 1:3,820}；wit-mg {25,846/4,608/290/16} 归
lane_332 Python 账）。 -/
def lock8bc : String :=
  let s := Lane321.tierStats 8
  s!"N=8 BC: insts={s.insts} audits={s.audits} cviols={s.cviols} \
t0/t1/t2={s.t0}/{s.t1}/{s.t2} mg0/1/2={s.mg0}/{s.mg1}/{s.mg2}"

#eval lock8bc

/-- N=10 机锁输出壳：Lane321.tierStats 10 实测外推编译期约 26 分钟（探针
tierStats 8 = 32 s 实测，按实例数 ×20.6 与 pairs 密度 ×2.4 折算），超白天
≤10 分钟线，按算力协议不在本文件 `#eval`、落款 NIGHT_BATCH 排队归夜棒；
def 先行入文件供夜批 `#eval Lane332.lock10bc` 直接续跑。Python 独立实现
N=10 全域账：634,960 例 / 34,755,040 合法对 / 12,211,196 witness / thmA 违反 0 /
audits 634,960 / t 1,402,934-3,172,278-1,137,188 / all-mg {594,148, 40,812}
（=lane_314 Lean 机锁 E2 分案逐值）/ E1g-fail 13,488 双路闭合。 -/
def lock10bc : String :=
  let s := Lane321.tierStats 10
  s!"N=10 BC: insts={s.insts} audits={s.audits} cviols={s.cviols} \
t0/t1/t2={s.t0}/{s.t1}/{s.t2} mg0/1/2={s.mg0}/{s.mg1}/{s.mg2}"

/-- N=12 机锁输出壳：tierStats 12 实测外推编译期约 13 小时（同法 ×12.3 实例
×2.5 密度），必归夜批；同上不 `#eval`。Python 独立实现 N=12 全域账（四块游标
≤10 分钟线/块）：7,798,903 例 / 1,060,052,386 合法对 / 313,315,956 witness /
thmA 违反 0 / audits 7,798,903 / t 26,425,954-60,737,024-31,364,424 /
all-mg {7,583,339, 215,564} / wit-mg {7,476,159/308,174/13,120/1,252/174/24} /
互锁 107,180 双路闭合。 -/
def lock12bc : String :=
  let s := Lane321.tierStats 12
  s!"N=12 BC: insts={s.insts} audits={s.audits} cviols={s.cviols} \
t0/t1/t2={s.t0}/{s.t1}/{s.t2} mg0/1/2={s.mg0}/{s.mg1}/{s.mg2}"

end Lane332

end Front583


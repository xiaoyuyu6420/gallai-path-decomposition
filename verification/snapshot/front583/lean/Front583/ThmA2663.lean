/-
  ThmA2663.lean — 定理 A 完全证明形式化（Lean 五步之第二步【定理 A 完全证明】，deep_L2 棒）
  底账：front583/campaign/deep_01_holechain_bound.md §3（定理 A 七步 A1–A7，终审 deep_03 PASS）
  + deep_L1_lean_core.md（底座 2663Core.lean：Inst2663/wf/so1/LegalPair/判定层零漂移别名）。
  本件把底座装配件 thmA2663（直呼 Lane314.thmA_core 的指针装配）升级为自含完整证明：
  - A1–A6 全链在本件内从 List.countP 原语独立重证（工具件五式亦本件自含，零借用
    Lane314.countP_mono / Lane283.countP_or 等现成引理，不调 thmA_core）；
  - A7 链式放大首次 Lean 化，前提 d₁≥1 ∧ d₃≥1 ∧ β≥1 显式化（stepA7_chain）；
  - so1 前提冗余口径承 deep_03 发现 #1：定理 A 陈述不取 so1（断言实际更强）。
  底座零触碰：本件纯新增，不 import 进 Front583.lean，不改 2663Core.lean 任何既有定义；
  A-2/A-3 断言在本件重断言由 kernel 本次重检（底座 olean 缓存命中时不重跑 example）。
-/
import Front583.«2663Core»

namespace F2663

/-! ### 0. 工具件（countP 五式，全部本件自含归纳直证；承 Lane314 同型战术骨架） -/

/-- T1 逐点相等 ⟹ 窗口计数相等。 -/
theorem tA_countP_congr (w : List Nat) (p q : Nat → Bool)
    (h : ∀ x ∈ w, p x = q x) : w.countP p = w.countP q := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    have ih' := ih (fun y hy => h y (List.mem_cons.2 (Or.inr hy)))
    rw [List.countP_cons, List.countP_cons, h x (List.mem_cons.2 (Or.inl rfl))]
    rw [ih']

/-- T2 逐点假 ⟹ 计数为零。 -/
theorem tA_countP_eq_zero (w : List Nat) (p : Nat → Bool)
    (h : ∀ x ∈ w, p x = false) : w.countP p = 0 := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    rw [List.countP_cons]
    cases hpx : p x <;> simp only [Bool.false_eq_true, ite_false, ite_true, Nat.add_zero]
    · exact ih (fun y hy => h y (List.mem_cons.2 (Or.inr hy)))
    · rw [h x (List.mem_cons.2 (Or.inl rfl))] at hpx
      exact absurd hpx (by decide)

/-- T3 逐点蕴含 ⟹ 计数单调。 -/
theorem tA_countP_mono (w : List Nat) (p q : Nat → Bool)
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

/-- T4 逐点互斥析取 ⟹ 计数可加。 -/
theorem tA_countP_or (w : List Nat) (p1 p2 : Nat → Bool)
    (hd : ∀ x ∈ w, ¬ ((p1 x = true) ∧ (p2 x = true))) :
    w.countP (fun x => p1 x || p2 x) = w.countP p1 + w.countP p2 := by
  induction w with
  | nil => simp
  | cons x w ih =>
    have ih' := ih (fun y hy => hd y (List.mem_cons.2 (Or.inr hy)))
    rw [List.countP_cons, List.countP_cons, List.countP_cons]
    cases h1 : p1 x <;> cases h2 : p2 x <;>
      simp only [Bool.false_eq_true, Bool.false_or, Bool.true_or, ite_false, ite_true,
        Nat.add_zero]
    · exact ih'
    · omega
    · omega
    · exact (hd x (List.mem_cons.2 (Or.inl rfl)) ⟨h1, h2⟩).elim

/-- T5 计数 ≤ 窗口长。 -/
theorem tA_countP_le_len (w : List Nat) (p : Nat → Bool) : w.countP p ≤ w.length := by
  induction w with
  | nil => simp
  | cons x w ih =>
    rw [List.countP_cons, List.length_cons]
    cases hpx : p x <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> omega

/-! ### 1. 定理 A 七步（deep_01 §3 逐步；承载于判定层 Lane314 定义件之上） -/

/-- (A1)+(A2) 集合恒等（逐点 Bool 形）：L∖C₂ ≡ F₁₃∖(C₁∪C₂)。
x∈L ⟺ x∈F₁₃ ∧ x∉C₁（L 定义），两侧逐字相同。 -/
theorem stepA1_pointwise (n δ13 : Nat) (P C1 C2 : Nat → Bool) (x : Nat) :
    (Front583.Lane314.isL n δ13 P C1 x && !C2 x)
      = (Front583.Lane314.isF13 n δ13 P C1 x && !(C1 x || C2 x)) := by
  unfold Front583.Lane314.isL Front583.Lane314.isF13
  cases P x <;> cases C1 ((x + δ13) % n) <;> cases C1 x <;> cases C2 x <;> rfl

/-- (A3) 二分分解：L = (L∩C₂) ⊔ (L∖C₂)（不交并），故 g₁₃ = |L∩C₂| + |L∖C₂|。 -/
theorem stepA3_split (n δ13 : Nat) (P C1 C2 : Nat → Bool) :
    Front583.Lane314.g13 n δ13 P C1
      = (List.range n).countP (fun x => Front583.Lane314.isL n δ13 P C1 x && C2 x)
        + (List.range n).countP (fun x => Front583.Lane314.isL n δ13 P C1 x && !C2 x) := by
  have hpsplit : ∀ x : Nat, Front583.Lane314.isL n δ13 P C1 x
      = ((Front583.Lane314.isL n δ13 P C1 x && C2 x)
          || (Front583.Lane314.isL n δ13 P C1 x && !C2 x)) := by
    intro x
    cases h : Front583.Lane314.isL n δ13 P C1 x <;> cases C2 x <;> rfl
  have hd : ∀ x ∈ List.range n,
      ¬ ((Front583.Lane314.isL n δ13 P C1 x && C2 x) = true
        ∧ (Front583.Lane314.isL n δ13 P C1 x && !C2 x) = true) := by
    intro x _ hcon
    obtain ⟨h1, h2⟩ := hcon
    rw [Bool.and_eq_true] at h1 h2
    obtain ⟨_, hC2t⟩ := h1
    obtain ⟨_, hC2f⟩ := h2
    rw [Bool.not_eq_true'] at hC2f
    rw [hC2t] at hC2f
    exact Bool.noConfusion hC2f
  unfold Front583.Lane314.g13
  rw [tA_countP_congr _ _ _ (fun x _ => hpsplit x), tA_countP_or _ _ _ hd]

/-- (A4) 吸收项界：|L∩C₂| ≤ |C₂| = d₂（子集基数，T3 单调）。 -/
theorem stepA4_absorb (n δ13 d2 : Nat) (P C1 C2 : Nat → Bool)
    (hd2 : (List.range n).countP C2 = d2) :
    (List.range n).countP (fun x => Front583.Lane314.isL n δ13 P C1 x && C2 x) ≤ d2 := by
  have hmono : (List.range n).countP (fun x => Front583.Lane314.isL n δ13 P C1 x && C2 x)
      ≤ (List.range n).countP C2 :=
    tA_countP_mono _ _ _ (fun x _ hcon => by
      rw [Bool.and_eq_true] at hcon
      exact hcon.2)
  exact Nat.le_trans hmono (Nat.le_of_eq hd2)

/-- (A5) 付费项界：|L∖C₂| =（A1）val 第一项 ≤ val（三项皆基数非负）。 -/
theorem stepA5_pay (n δ13 δ23 t3 : Nat) (P C1 C2 : Nat → Bool) :
    (List.range n).countP (fun x => Front583.Lane314.isL n δ13 P C1 x && !C2 x)
      ≤ Front583.Lane314.val3 n δ13 δ23 t3 P C1 C2 := by
  have hcong : (List.range n).countP (fun x => Front583.Lane314.isL n δ13 P C1 x && !C2 x)
      = (List.range n).countP
          (fun x => Front583.Lane314.isF13 n δ13 P C1 x && !(C1 x || C2 x)) :=
    tA_countP_congr _ _ _ (fun x _ => stepA1_pointwise n δ13 P C1 C2 x)
  rw [hcong]
  unfold Front583.Lane314.val3
  omega

/-- (A6) 合并（注记 A-1 无前提形式，自含版）：g₁₃ ≤ d₂ + val。唯一前提 |C₂| = d₂。 -/
theorem stepA6_merge (n d2 δ13 δ23 t3 : Nat) (P C1 C2 : Nat → Bool)
    (hd2 : (List.range n).countP C2 = d2) :
    Front583.Lane314.g13 n δ13 P C1
      ≤ d2 + Front583.Lane314.val3 n δ13 δ23 t3 P C1 C2 := by
  have h3 := stepA3_split n δ13 P C1 C2
  have h4 := stepA4_absorb n δ13 d2 P C1 C2 hd2
  have h5 := stepA5_pay n δ13 δ23 t3 P C1 C2
  omega

/-- **定理 A 核心（299.A 完全体，自含重证；非装配件）**：val ≤ 1 ⟹ g₁₃ ≤ d₂+1。
A3 三拆 + A4 吸收 + A5 付费 + A6 合并；A1–A6 不用 so1（deep_03 发现 #1，断言更强）。 -/
theorem thmA2663_self (n d2 δ13 δ23 t3 : Nat) (P C1 C2 : Nat → Bool)
    (hd2 : (List.range n).countP C2 = d2)
    (hv : Front583.Lane314.val3 n δ13 δ23 t3 P C1 C2 ≤ 1) :
    Front583.Lane314.g13 n δ13 P C1 ≤ d2 + 1 :=
  Nat.le_trans (stepA6_merge n d2 δ13 δ23 t3 P C1 C2 hd2) (by omega)

/-! ### 2. (A7) 链式放大（前提 d₁≥1 ∧ d₃≥1 ∧ β≥1 显式化；首次 Lean 化） -/

/-- (A7) 链式放大：β = p−d₁−d₂−d₃ ≥ 1 且 d₁≥1、d₃≥1 ⟹ d₂+3 ≤ p（即 d₂+1 ≤ p−2）；
且 p = |P∩[0,N)| ≤ N。deep_01 §3 (A7) 的显式前提版。 -/
theorem stepA7_chain (I : Inst2663)
    (hd1 : 0 < I.d1) (hd3 : 0 < I.d3) (hbeta : 1 ≤ beta I) :
    I.d2 + 1 + 2 ≤ pcard I ∧ pcard I ≤ I.N := by
  have hpcard : pcard I ≤ I.N :=
    Nat.le_trans (tA_countP_le_len (List.range I.N) I.P)
      (Nat.le_of_eq (by rw [List.length_range]))
  unfold beta at hbeta
  omega

/-! ### 3. 定理 A 完全体（底座装配件的自含升级：wf 前提 + 七步全链） -/

/-- **定理 A 完全体（deep_01 §3 定理 A）**：良构实例 I（wf 内含 dᵢ≥1、β≥1——A7 前提
由 wf 逐项取出显式化）、合法对计数前提、val ≤ 1 ⟹ g₁₃ ≤ d₂+1 ≤ p−2 ≤ N−2 的
减法自由链形态 g₁₃ ≤ d₂+1 ∧ d₂+3 ≤ p ∧ p ≤ N。证明全链在本件：A1–A6（thmA2663_self）
+ A7（stepA7_chain），零指针装配。 -/
theorem thmA2663_full (I : Inst2663) (C1 C2 : Nat → Bool)
    (hwf : wf I) (hd2 : (List.range I.N).countP C2 = I.d2)
    (hv : val I C1 C2 ≤ 1) :
    g13 I C1 ≤ I.d2 + 1 ∧ I.d2 + 1 + 2 ≤ pcard I ∧ pcard I ≤ I.N := by
  obtain ⟨_, hdpos, _, hbeta, _⟩ := hwf
  have hv' : Front583.Lane314.val3 I.N (d13 I) (d23 I) I.t3 I.P C1 C2 ≤ 1 := hv
  refine ⟨thmA2663_self I.N I.d2 (d13 I) (d23 I) I.t3 I.P C1 C2 hd2 hv', ?_, ?_⟩
  · exact (stepA7_chain I hdpos.1 hdpos.2.2 hbeta).1
  · exact (stepA7_chain I hdpos.1 hdpos.2.2 hbeta).2

/-- A7 链的一致 N-函数尾式（deep_01 §3：g₁₃ ≤ d₂+1 ≤ p−2 ≤ N−2 的末环）。 -/
theorem thmA2663_chain_N (I : Inst2663) (C1 C2 : Nat → Bool)
    (hwf : wf I) (hd2 : (List.range I.N).countP C2 = I.d2)
    (hv : val I C1 C2 ≤ 1) :
    g13 I C1 ≤ I.d2 + 1 ∧ I.d2 + 1 + 2 ≤ pcard I ∧ pcard I ≤ I.N ∧ g13 I C1 ≤ I.N - 2 := by
  have h := thmA2663_full I C1 C2 hwf hd2 hv
  omega

/-- 与底座装配件 thmA2663 同陈述的自含重证（升级件：同型，证明换为本件七步全链）。 -/
theorem thmA2663_upgraded (I : Inst2663) (C1 C2 : Nat → Bool)
    (hd2 : (List.range I.N).countP C2 = I.d2) (hv : val I C1 C2 ≤ 1) :
    g13 I C1 ≤ I.d2 + 1 :=
  thmA2663_self I.N I.d2 (d13 I) (d23 I) I.t3 I.P C1 C2 hd2 hv

/-- 注记 A-1 自含版：g₁₃ ≤ d₂ + val（A6 落 F2663 别名层）。 -/
theorem g13_le_add_val_self (I : Inst2663) (C1 C2 : Nat → Bool)
    (hd2 : (List.range I.N).countP C2 = I.d2) :
    g13 I C1 ≤ I.d2 + val I C1 C2 :=
  stepA6_merge I.N I.d2 (d13 I) (d23 I) I.t3 I.P C1 C2 hd2

/-! ### 4. A-2/A-3 回归段（底座断言本件重断言，kernel 本次重检） -/

/-- A-2 良构回归（底座同式；命名件供全定理落地例引用）。 -/
theorem wfIA2 : wf IA2 := by
  unfold wf win dpos tdist capacity beta pcard IA2
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨by decide, by decide, by decide, ?_⟩
    intro x hx
    have hx' : x < 7 := of_decide_eq_true hx
    show x < 8
    omega
  · exact ⟨by decide, by decide, by decide⟩
  · decide
  · decide
  · decide

/-- A-2 合法对回归。 -/
example : LegalPair IA2 C1A2 C2A2 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx
    have hx' : 4 ≤ x ∧ x < 7 := of_decide_eq_true hx
    refine ⟨decide_eq_true hx'.2, ?_⟩
    have ht : IA2.t1 = 0 := rfl
    omega
  · rfl
  · intro x hx
    have hx' : x = 2 ∨ x = 3 := of_decide_eq_true hx
    rcases hx' with rfl | rfl
    · rfl
    · rfl
  · rfl

/-- A-2 核心数值回归：g₁₃=3=d₂+1 取等 ∧ val=1。 -/
example : g13 IA2 C1A2 = 3 ∧ val IA2 C1A2 C2A2 = 1 := ⟨by decide, by decide⟩

/-- A-3 良构回归（命名件供全定理落地例引用）。 -/
theorem wfIA3 : wf IA3 := by
  unfold wf win dpos tdist capacity beta pcard IA3
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨by decide, by decide, by decide, ?_⟩
    intro x hx
    have hx' : x ≠ 3 ∧ x < 6 := of_decide_eq_true hx
    show x < 6
    omega
  · exact ⟨by decide, by decide, by decide⟩
  · decide
  · decide
  · decide

/-- A-3 合法对回归。 -/
example : LegalPair IA3 C1A3 C2A3 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx
    have hx' : x = 0 ∨ x = 1 := of_decide_eq_true hx
    rcases hx' with rfl | rfl
    · simp only [IA3, P6]; exact ⟨by decide, by omega⟩
    · simp only [IA3, P6]; exact ⟨by decide, by omega⟩
  · rfl
  · intro x hx
    have hx' : x = 5 := of_decide_eq_true hx
    subst hx'
    rfl
  · rfl

/-- A-3 核心数值回归：g₁₃=1 ∧ val=1。 -/
example : g13 IA3 C1A3 = 1 ∧ val IA3 C1A3 C2A3 = 1 := ⟨by decide, by decide⟩

/-! ### 5. 中间步 example（≥2 要求；七步在两例上逐环落地） -/

/-- 中间步 (A3)×A-2：二分数值账 |L∩C₂|=2（饱和）、|L∖C₂|=1、g₁₃=3=2+1。 -/
example : (List.range 8).countP (fun x => L13 IA2 C1A2 x && C2A2 x) = 2
    ∧ (List.range 8).countP (fun x => L13 IA2 C1A2 x && !C2A2 x) = 1
    ∧ g13 IA2 C1A2 = 2 + 1 := by decide

/-- 中间步 (A3) 引理落地×A-2：stepA3_split 在实例上给出恒等式本身。 -/
example : g13 IA2 C1A2
    = (List.range 8).countP (fun x => L13 IA2 C1A2 x && C2A2 x)
      + (List.range 8).countP (fun x => L13 IA2 C1A2 x && !C2A2 x) :=
  stepA3_split 8 (d13 IA2) P8 C1A2 C2A2

/-- 中间步 (A4)(A5)×A-2：吸收项 2 ≤ d₂=2 恰饱和、付费项 1 ≤ val=1 恰取等。 -/
example : (List.range IA2.N).countP (fun x => L13 IA2 C1A2 x && C2A2 x) = IA2.d2
    ∧ (List.range IA2.N).countP (fun x => L13 IA2 C1A2 x && !C2A2 x)
      ≤ val IA2 C1A2 C2A2 := by
  have h4 := stepA4_absorb IA2.N (d13 IA2) IA2.d2 IA2.P C1A2 C2A2 (by rfl)
  have h5 := stepA5_pay IA2.N (d13 IA2) (d23 IA2) IA2.t3 IA2.P C1A2 C2A2
  have hc2 : (List.range IA2.N).countP (fun x => L13 IA2 C1A2 x && C2A2 x) = 2 := by decide
  have hval : val IA2 C1A2 C2A2 = 1 := by decide
  have hd2 : IA2.d2 = 2 := rfl
  unfold L13 at hc2 ⊢
  unfold val at hval ⊢
  omega

/-- 中间步 (A6)×A-3：自含合并引理落地，g₁₃=1 ≤ d₂+val=2。 -/
example : g13 IA3 C1A3 ≤ IA3.d2 + val IA3 C1A3 C2A3 :=
  g13_le_add_val_self IA3 C1A3 C2A3 rfl

/-- 中间步 (A7)×A-2：前提显式化后 d₂+3=5 ≤ p=7 ≤ N=8（A7 首次 Lean 化落地）。 -/
example : IA2.d2 + 1 + 2 ≤ pcard IA2 ∧ pcard IA2 ≤ IA2.N :=
  stepA7_chain IA2 (by decide) (by decide) (by decide)

/-- 中间步 (A7)×A-3：边界档 d₂+3=4 ≤ p=5 ≤ N=6。 -/
example : IA3.d2 + 1 + 2 ≤ pcard IA3 ∧ pcard IA3 ≤ IA3.N :=
  stepA7_chain IA3 (by decide) (by decide) (by decide)

/-! ### 6. 全定理落地（自含升级件在两例生效；含底座装配件同陈述回归） -/

/-- 全体×A-2：thmA2663_full 落地（wf/计数/val 三前提逐给）。 -/
example : g13 IA2 C1A2 ≤ IA2.d2 + 1 ∧ IA2.d2 + 1 + 2 ≤ pcard IA2 ∧ pcard IA2 ≤ IA2.N :=
  thmA2663_full IA2 C1A2 C2A2 wfIA2 rfl (by decide)

/-- 全体×A-3：thmA2663_full 落地（N−2 一致式）。 -/
example : g13 IA3 C1A3 ≤ IA3.d2 + 1 ∧ g13 IA3 C1A3 ≤ IA3.N - 2 := by
  have h := thmA2663_chain_N IA3 C1A3 C2A3 wfIA3 rfl (by decide)
  exact ⟨h.1, h.2.2.2⟩

/-- 底座装配件同陈述回归：thmA2663_upgraded 与 thmA2663 在 A-2 上同给 g₁₃ ≤ d₂+1。 -/
example : g13 IA2 C1A2 ≤ IA2.d2 + 1 := thmA2663_upgraded IA2 C1A2 C2A2 rfl (by decide)

end F2663

/-
  Struct2663.lean — 情形 2 结构定理（deep_L14 棒，2026-09-30）
  底账：front583/campaign/deep_L7_lean_case2.md §5① 开口（结构定理 r=1∧ℓ=1 ⟹
  g-不变核∪单点 未形式化，主定理被 β 单路绕开）+ deep_F3回炉终验.md §1.2/§2.2
  （(2a-iii) 前提域 C₁=C_m∪{s} 的纸面重推 PASS；625 对机器锚 canonical case-2：
  r=1∧游程长=1∧t₂,t₃∉C₁∧C₂=Q）。

  内容：
  - §S1 步进件：c2st_bg_succ（后向步迭代）、c2st_cong（模同余传递）、
    c2st_bwd_eq（(a+(N−g))%N=b ⟹ a=(b+g)%N）、c2st_fwd_eq（(a+g)%N=(b+g)%N ⟹ a=b）；
  - §S2 结构定理 case2_struct_r1：r=1（恰一头 s）∧ℓ=1（(s+2g)%N∉C₁）⟹
    C₁∖{(s+g)%N} 为 g-不变核（窗上前向+后向两向）＝「g-不变核 ∪ 单点」kernel 化
    ——deep_L7 §5① 开口闭合；
  - §S3 桥件：case2_struct_alpha_iff（α 判别式 C₁((t₁+g)%N) ⟺ 头=t₁，
    纸面 (2a-iii) α/β 与机器 hc 二分的对齐件）；
  - §S4 625 对机器锚抽样 ≥21 对 decidable 实例验证（canonical 协议从零枚举，
    逐格计数对 deep_F3回炉终验 §2.2 锚：(8,2):1/(10,2):2/(12,2):3/(12,3):11/
    (12,4):27/(15,3):16/(15,5):84=144 小域 m≥1 + m=0 219；抽样规则与清单见
    front583/campaign/deep_L14_lean_struct.md §3）。

  两路线关系（任务②结论：并存）：主定理 case2_val_ge_one（U2U32663.lean §16c）的
  r=1 支为 β 单路——hc 二分（C₁((t₁+g)%N) 判别）直接付费，不经结构定理，前提更弱
  （不假设 r=1 的头结构）、证明更短；结构定理是纸面 (2a-iii) 前提「C₁=C_m∪{s}」
  的 kernel 化，闭合纸面对齐开口，但主定理证明不消费它。两路线并存，关系见本头注、
  §S3 桥件与报告 §4。
-/
import Front583.U2U32663

namespace F2663

/-! ### S1. 步进件（deep_L14 结构定理的模步底座） -/

/-- 后向步迭代：bw(j+1) = bw(j)+（N−g）的 mod 形态（bw j x := (x + (N−g)*j) % N，
    即窗上 x−g 的代表元；全程零减法实现）。 -/
theorem c2st_bg_succ (N bg j x : Nat) :
    (x + bg * (j + 1)) % N = ((x + bg * j) % N + bg) % N := by
  rw [Nat.mul_succ, ← Nat.add_assoc, mod_add_absorb' (x + bg * j) bg N]

/-- 模同余传递：a + N*k = b ⟹ b % N = a % N。 -/
theorem c2st_cong (N a b k : Nat) (h : a + N * k = b) : b % N = a % N := by
  subst h
  rw [Nat.add_mul_mod_self_left]

/-- 后向元素等式：(a+(N−g))%N = b（a,b<N）⟹ a = (b+g)%N（商 ≤1 二分）。 -/
theorem c2st_bwd_eq (N g a b : Nat) (_hN : 0 < N) (hgN : g ≤ N)
    (hav : a < N) (_hbv : b < N) (h : (a + (N - g)) % N = b) :
    a = (b + g) % N := by
  have qle : (a + (N - g)) / N ≤ 1 := by
    have hlt : a + (N - g) < N * 2 := by omega
    exact Nat.le_of_lt_succ (Nat.div_lt_of_lt_mul hlt)
  have e : a + (N - g) = N * ((a + (N - g)) / N) + b := by
    have e0 := Nat.div_add_mod (a + (N - g)) N
    rw [h] at e0
    exact e0.symm
  rcases Nat.lt_or_ge ((a + (N - g)) / N) 1 with q0 | q1
  · have q0' : (a + (N - g)) / N = 0 := Nat.le_antisymm (Nat.le_of_lt_succ q0) (Nat.zero_le _)
    rw [q0', Nat.mul_zero] at e
    -- e : a + (N - g) = b ⟹ b + g = a + N
    have hcg : (b + g) % N = a % N := by
      refine c2st_cong N a (b + g) 1 ?_
      omega
    rw [hcg, Nat.mod_eq_of_lt hav]
  · have q1' : (a + (N - g)) / N = 1 := Nat.le_antisymm qle q1
    rw [q1', Nat.mul_one] at e
    -- e : a + (N - g) = N + b ⟹ a = b + g
    have hlt : b + g < N := by omega
    rw [Nat.mod_eq_of_lt hlt]
    omega

/-- 前向元素等式：(a+g)%N = (b+g)%N（a,b<N）⟹ a = b（商 ≤1 四分）。 -/
theorem c2st_fwd_eq (N g a b : Nat) (_hN : 0 < N) (hgN : g < N)
    (hav : a < N) (hbv : b < N) (h : (a + g) % N = (b + g) % N) : a = b := by
  have e1 : a + g = N * ((a + g) / N) + (b + g) % N := by
    have e0 := Nat.div_add_mod (a + g) N
    rw [h] at e0
    exact e0.symm
  have e2 : b + g = N * ((b + g) / N) + (b + g) % N :=
    (Nat.div_add_mod (b + g) N).symm
  have q1 : (a + g) / N ≤ 1 :=
    Nat.le_of_lt_succ (Nat.div_lt_of_lt_mul (show a + g < N * 2 by omega))
  have q2 : (b + g) / N ≤ 1 :=
    Nat.le_of_lt_succ (Nat.div_lt_of_lt_mul (show b + g < N * 2 by omega))
  rcases Nat.eq_zero_or_pos ((a + g) / N) with h0 | h1
  · rw [h0, Nat.mul_zero] at e1
    rcases Nat.eq_zero_or_pos ((b + g) / N) with h0' | h1'
    · rw [h0', Nat.mul_zero] at e2
      omega
    · have h1' : (b + g) / N = 1 := Nat.le_antisymm q2 h1'
      rw [h1', Nat.mul_one] at e2
      omega
  · have h1 : (a + g) / N = 1 := Nat.le_antisymm q1 h1
    rw [h1, Nat.mul_one] at e1
    rcases Nat.eq_zero_or_pos ((b + g) / N) with h0' | h1'
    · rw [h0', Nat.mul_zero] at e2
      omega
    · have h1' : (b + g) / N = 1 := Nat.le_antisymm q2 h1'
      rw [h1', Nat.mul_one] at e2
      omega

/-! ### S2. 结构定理（deep_L14 核心：r=1∧ℓ=1 ⟹ g-不变核∪单点） -/

/-- **情形 2 结构定理（deep_L14；deep_L7 §5① 开口闭合）**：
r=1（窗上恰一头 s：s∉C₁、(s+g)%N∈C₁）∧ ℓ=1（(s+2g)%N∉C₁，游程长 1）⟹
C₁∖{(s+g)%N} 是 g-不变核——窗上前向（core x ⟹ core (x+g)）与后向
（core (x+g) ⟹ core x）两向不变，即 **C₁ = g-不变核 ∪ 单点 {(s+g)%N}**。
证明结构：头唯一（c2_head_unique）⟹ 一步后向命题（每 C₁ 点的 −g 前像在 C₁
或为头 s）⟹ 游程归纳（core 点的后向游程全在 C₁：中途撞头 s 给出 (s+2g)%N∈C₁
与 ℓ=1 矛盾）⟹ 轨道长 L=N/gcd(g,N) 处 bw(L−1)x=(x+g)%N 承前向；后向直接
（非 C₁ 点的 +g 像在 C₁ ⟹ 该点为头 ⟹ =s ⟹ 与单点判别矛盾）。 -/
theorem case2_struct_r1 (N g s : Nat) (C1 : Nat → Bool)
    (hN : 0 < N) (hg : 0 < g) (hgN : g < N)
    (hr : (List.range N).countP (c2head N g C1) = 1)
    (hs : s < N) (hsh : c2head N g C1 s = true)
    (h2 : C1 ((s + 2 * g) % N) = false) :
    (∀ x, x < N → C1 x = true → x ≠ (s + g) % N →
        C1 ((x + g) % N) = true ∧ (x + g) % N ≠ (s + g) % N) ∧
      (∀ x, x < N → C1 ((x + g) % N) = true → (x + g) % N ≠ (s + g) % N →
        C1 x = true ∧ x ≠ (s + g) % N) := by
  -- 头事实：s∉C₁、(s+g)%N∈C₁
  unfold c2head at hsh
  rw [Bool.and_eq_true] at hsh
  obtain ⟨hC1s, hC1pt⟩ := hsh
  have hshT : c2head N g C1 s = true := by
    unfold c2head
    rw [hC1s, hC1pt]
    decide
  simp at hC1s
  -- 头唯一
  have huniq : ∀ y, y < N → c2head N g C1 y = true → y = s := by
    intro y hyw hyh
    by_cases hts : y = s
    · exact hts
    · exact (c2_head_unique N g C1 hr s hs hshT y hyw hyh
        (fun hxy => hts hxy.symm)).elim
  -- 一步后向（Claim A）：C₁ 点的 −g 前像在 C₁ 或为头 s
  have stepA : ∀ x, x < N → C1 x = true →
      C1 ((x + (N - g)) % N) = true ∨ (x + (N - g)) % N = s := by
    intro x hxw hcx
    have hb : (x + (N - g)) % N < N := Nat.mod_lt _ hN
    by_cases hcb : C1 ((x + (N - g)) % N) = true
    · exact Or.inl hcb
    · right
      have hcf : C1 ((x + (N - g)) % N) = false := by simpa using hcb
      have hsh2 : c2head N g C1 ((x + (N - g)) % N) = true := by
        unfold c2head
        rw [hcf]
        have hshift : (((x + (N - g)) % N + g) % N) = x := by
          have h3 : (((x + (N - g)) % N + g) % N) = (x + (N - g) + g) % N :=
            mod_add_absorb' (x + (N - g)) g N
          rw [h3]
          have hx2 : x + (N - g) + g = x + N := by omega
          rw [hx2, Front583.Lane314.mod_add_self, Nat.mod_eq_of_lt hxw]
        rw [hshift, hcx]
        simp
      exact huniq _ hb hsh2
  -- 游程归纳：core 点的后向游程全在 C₁（撞头即 ℓ≥2 矛盾）
  have walk : ∀ j x, x < N → C1 x = true → x ≠ (s + g) % N →
      ∀ i, i ≤ j → C1 ((x + (N - g) * i) % N) = true := by
    intro j
    induction j with
    | zero =>
      intro x hxw hcx _ i hi
      have hi0 : i = 0 := Nat.le_antisymm hi (Nat.zero_le _)
      rw [hi0, Nat.mul_zero, Nat.add_zero, Nat.mod_eq_of_lt hxw]
      exact hcx
    | succ j ih =>
      intro x hxw hcx hxpt i hi
      rcases Nat.eq_or_lt_of_le hi with heq | hlt
      · -- i = j+1
        rw [heq]
        have hwN : (x + (N - g) * j) % N < N := Nat.mod_lt _ hN
        have hCw := ih x hxw hcx hxpt j (Nat.le_refl j)
        rcases stepA ((x + (N - g) * j) % N) hwN hCw with h1 | hhit
        · rw [c2st_bg_succ N (N - g) j x]
          exact h1
        · exfalso
          have hwpt : (x + (N - g) * j) % N = (s + g) % N :=
            c2st_bwd_eq N g _ s hN (Nat.le_of_lt hgN) hwN hs hhit
          by_cases hj0 : j = 0
          · rw [hj0, Nat.mul_zero, Nat.add_zero, Nat.mod_eq_of_lt hxw] at hwpt
            exact hxpt hwpt
          · -- j ≥ 1：bw(j−1)x ∈ C₁ 且 bw(j−1)x ≡ bw(j)x + g ≡ s+2g ⟹ 与 ℓ=1 矛盾
            have hj1 : 1 ≤ j := Nat.pos_of_ne_zero hj0
            have hCprev := ih x hxw hcx hxpt (j - 1) (by omega)
            have e0 : ((x + (N - g) * (j - 1)) % N + (N - g)) % N
                = (x + (N - g) * j) % N := by
              have h0 := (c2st_bg_succ N (N - g) (j - 1) x).symm
              rw [show (j - 1) + 1 = j from by omega] at h0
              exact h0
            have hprev : (x + (N - g) * (j - 1)) % N = (s + 2 * g) % N := by
              have step1 : (x + (N - g) * (j - 1)) % N
                  = ((x + (N - g) * j) % N + g) % N :=
                c2st_bwd_eq N g _ _ hN (Nat.le_of_lt hgN) (Nat.mod_lt _ hN)
                  (Nat.mod_lt _ hN) e0
              rw [step1, hwpt, mod_add_absorb' (s + g) g N,
                show s + g + g = s + 2 * g from by omega]
            rw [hprev] at hCprev
            rw [hCprev] at h2
            exact absurd h2 (by decide)
      · exact ih x hxw hcx hxpt i (Nat.le_of_lt_succ hlt)
  refine ⟨?_, ?_⟩
  · -- 前向：core x ⟹ core (x+g)
    intro x hxw hcx hxpt
    refine ⟨?_, ?_⟩
    · -- 游程全 C₁ 至 N−1 步；bw(N−1)x = (x+g)%N（步数 j=N−1 ⟹ N∣(j+1)g 平凡成立）
      have hW := walk (N - 1) x hxw hcx hxpt (N - 1) (Nat.le_refl (N - 1))
      have hM2leM1 : g * (N - 1) ≤ N * (N - 1) := by
        have h9 := Nat.mul_le_mul_left (N - 1) (Nat.le_of_lt hgN)
        rw [Nat.mul_comm (N - 1) g, Nat.mul_comm (N - 1) N] at h9
        exact h9
      have hbg2 : (x + (N - g) * (N - 1)) % N = (x + g) % N := by
        have e1 : (N - g) * (N - 1) = N * (N - 1) - g * (N - 1) :=
          Nat.sub_mul _ _ _
        have e2 : g * (N - 1) + g = N * g := by
          rw [Nat.mul_sub g N 1, Nat.mul_one,
            Nat.sub_add_cancel (Nat.le_mul_of_pos_right g hN), Nat.mul_comm g N]
        have h1' : (x + (N - g) * (N - 1)) + N * g = (x + g) + N * (N - 1) := by
          omega
        have h2' : ((x + g) + N * (N - 1)) % N = (x + g) % N := by
          rw [Nat.add_mul_mod_self_left]
        have h3' : (x + (N - g) * (N - 1)) % N = ((x + g) + N * (N - 1)) % N :=
          (c2st_cong N (x + (N - g) * (N - 1)) ((x + g) + N * (N - 1)) g h1').symm
        rw [h3', h2']
      rw [hbg2] at hW
      exact hW
    · -- (x+g)%N ≠ (s+g)%N（否则 x=s∉C₁）
      intro heq
      have hxseq : x = s := c2st_fwd_eq N g x s hN hgN hxw hs heq
      rw [hxseq] at hcx
      simp [hC1s] at hcx
  · -- 后向：core (x+g) ⟹ core x
    intro x hxw hptg hnept
    have hcx : C1 x = true := by
      cases hx : C1 x with
      | true => rfl
      | false =>
        exfalso
        have hh : c2head N g C1 x = true := by
          unfold c2head
          rw [hx, hptg]
          simp
        have hxs := huniq x hxw hh
        rw [hxs] at hnept
        exact absurd rfl hnept
    refine ⟨hcx, ?_⟩
    intro heq
    have hxg : (x + g) % N = (s + 2 * g) % N := by
      rw [heq, mod_add_absorb' (s + g) g N,
        show s + g + g = s + 2 * g from by omega]
    rw [hxg] at hptg
    rw [hptg] at h2
    exact absurd h2 (by decide)

/-! ### S3. 桥件（纸面 (2a-iii) α/β ⟷ 机器 hc 二分的对齐） -/

/-- **α 判别式对齐桥（deep_L14）**：r=1（头唯一为 s）且 t₁∉C₁ 的情形 2 语境下，
机器判别式 hc := C₁((t₁+g)%N)（主定理 (2a) 支的二分式）成立 ⟺ 头=t₁——
即纸面 (2a-iii) 的「α ⟺ s=t₁+σ」（deep_F3回炉终验 §1.2：α 支付费位 t₂=s−δ₁₃，
判别式在结构前提下与 hc 等价）的 kernel 形态。 -/
theorem case2_struct_alpha_iff (N g t1 s : Nat) (C1 : Nat → Bool)
    (hN : 0 < N) (hr : (List.range N).countP (c2head N g C1) = 1)
    (ht1w : t1 < N) (hstw : s < N)
    (hC1t1 : C1 t1 = false)
    (hsh : c2head N g C1 s = true) :
    (C1 ((t1 + g) % N) = true ↔ t1 = s) := by
  constructor
  · intro hc
    have hh : c2head N g C1 t1 = true := by
      unfold c2head
      rw [hC1t1, hc]
      simp
    by_cases hts : t1 = s
    · exact hts
    · exact (c2_head_unique N g C1 hr s hstw hsh t1 ht1w hh
        (fun hxy => hts hxy.symm)).elim
  · intro hts
    have hsh' : c2head N g C1 t1 = true := by rw [hts]; exact hsh
    unfold c2head at hsh'
    rw [Bool.and_eq_true] at hsh'
    exact hsh'.2

/-! ### S4. 625 对机器锚抽样 decidable 实例验证（23 对；deep_L14）

抽样来源：/tmp/deepL14x/sample625.py 从零实现 canonical case-2 协议（FULL、k=2、
规范 T=(0,−g,−2g)、C₁=m 条完整 ⟨g⟩-轨道∪{(s+g)%N}、r=1、ℓ=1、t₂,t₃∉C₁、
C₂=Q 被迫、顶格 d₂=N−d₁−2≥1），**逐格计数与 deep_F3回炉终验 §2.2 锚逐格精确命中**：
(8,2):1/(10,2):2/(12,2):3/(12,3):11/(12,4):27/(15,3):16/(15,5):84/(18,2):6/
(18,6):225/(24,3):31 ⟹ m≥1 406=m≥1 锚 406；m=0 219（含 N=17:{1..4} 素数域四格，
L=17 ⟹ m≥1 结构性不可能，仅出 m=0）⟹ 合计 625=625。抽样规则：小域 m≥1 全取
(8,2)+(10,2)+(12,2) 共 6 对，再按格取前 k（(12,3):4、(12,4):4、(15,3):3、(15,5):4），
另取 m=0 首 2 对 ⟹ 23 对（≥20 纪律线）。每对实例 = kernel 定理 case2_struct_r1
应用 + 7 项前提（0<N、0<g、g<N、头计数=1、s<N、头谓词、ℓ=1）逐一 decide。 -/
/-- 结构定理结论谓词（实例验证的结论形态：core:=C₁∖{(s+g)%N} 的前向+后向不变）。 -/
def StructConcl (N g s : Nat) (C1 : Nat → Bool) : Prop :=
  (∀ x, x < N → C1 x = true → x ≠ (s + g) % N →
      C1 ((x + g) % N) = true ∧ (x + g) % N ≠ (s + g) % N) ∧
    (∀ x, x < N → C1 ((x + g) % N) = true → (x + g) % N ≠ (s + g) % N →
      C1 x = true ∧ x ≠ (s + g) % N)

/-- 样本 1/23：(N=8,g=2) m=1 s=0 pt=2 d₁=5 d₂=1（canonical 协议逐格锚在案）。 -/
example : StructConcl 8 2 0 (fun x => decide (x ∈ [1, 2, 3, 5, 7])) :=
  case2_struct_r1 8 2 0 (fun x => decide (x ∈ [1, 2, 3, 5, 7])) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- 样本 2/23：(N=10,g=2) m=1 s=0 pt=2 d₁=6 d₂=2（canonical 协议逐格锚在案）。 -/
example : StructConcl 10 2 0 (fun x => decide (x ∈ [1, 2, 3, 5, 7, 9])) :=
  case2_struct_r1 10 2 0 (fun x => decide (x ∈ [1, 2, 3, 5, 7, 9])) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- 样本 3/23：(N=10,g=2) m=1 s=2 pt=4 d₁=6 d₂=2（canonical 协议逐格锚在案）。 -/
example : StructConcl 10 2 2 (fun x => decide (x ∈ [1, 3, 4, 5, 7, 9])) :=
  case2_struct_r1 10 2 2 (fun x => decide (x ∈ [1, 3, 4, 5, 7, 9])) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- 样本 4/23：(N=12,g=2) m=1 s=0 pt=2 d₁=7 d₂=3（canonical 协议逐格锚在案）。 -/
example : StructConcl 12 2 0 (fun x => decide (x ∈ [1, 2, 3, 5, 7, 9, 11])) :=
  case2_struct_r1 12 2 0 (fun x => decide (x ∈ [1, 2, 3, 5, 7, 9, 11])) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- 样本 5/23：(N=12,g=2) m=1 s=2 pt=4 d₁=7 d₂=3（canonical 协议逐格锚在案）。 -/
example : StructConcl 12 2 2 (fun x => decide (x ∈ [1, 3, 4, 5, 7, 9, 11])) :=
  case2_struct_r1 12 2 2 (fun x => decide (x ∈ [1, 3, 4, 5, 7, 9, 11])) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- 样本 6/23：(N=12,g=2) m=1 s=4 pt=6 d₁=7 d₂=3（canonical 协议逐格锚在案）。 -/
example : StructConcl 12 2 4 (fun x => decide (x ∈ [1, 3, 5, 6, 7, 9, 11])) :=
  case2_struct_r1 12 2 4 (fun x => decide (x ∈ [1, 3, 5, 6, 7, 9, 11])) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- 样本 7/23：(N=12,g=3) m=1 s=0 pt=3 d₁=5 d₂=5（canonical 协议逐格锚在案）。 -/
example : StructConcl 12 3 0 (fun x => decide (x ∈ [1, 3, 4, 7, 10])) :=
  case2_struct_r1 12 3 0 (fun x => decide (x ∈ [1, 3, 4, 7, 10])) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- 样本 8/23：(N=12,g=3) m=1 s=2 pt=5 d₁=5 d₂=5（canonical 协议逐格锚在案）。 -/
example : StructConcl 12 3 2 (fun x => decide (x ∈ [1, 4, 5, 7, 10])) :=
  case2_struct_r1 12 3 2 (fun x => decide (x ∈ [1, 4, 5, 7, 10])) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- 样本 9/23：(N=12,g=3) m=1 s=5 pt=8 d₁=5 d₂=5（canonical 协议逐格锚在案）。 -/
example : StructConcl 12 3 5 (fun x => decide (x ∈ [1, 4, 7, 8, 10])) :=
  case2_struct_r1 12 3 5 (fun x => decide (x ∈ [1, 4, 7, 8, 10])) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- 样本 10/23：(N=12,g=3) m=1 s=8 pt=11 d₁=5 d₂=5（canonical 协议逐格锚在案）。 -/
example : StructConcl 12 3 8 (fun x => decide (x ∈ [1, 4, 7, 10, 11])) :=
  case2_struct_r1 12 3 8 (fun x => decide (x ∈ [1, 4, 7, 10, 11])) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- 样本 11/23：(N=12,g=4) m=1 s=2 pt=6 d₁=4 d₂=6（canonical 协议逐格锚在案）。 -/
example : StructConcl 12 4 2 (fun x => decide (x ∈ [1, 5, 6, 9])) :=
  case2_struct_r1 12 4 2 (fun x => decide (x ∈ [1, 5, 6, 9])) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- 样本 12/23：(N=12,g=4) m=1 s=3 pt=7 d₁=4 d₂=6（canonical 协议逐格锚在案）。 -/
example : StructConcl 12 4 3 (fun x => decide (x ∈ [1, 5, 7, 9])) :=
  case2_struct_r1 12 4 3 (fun x => decide (x ∈ [1, 5, 7, 9])) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- 样本 13/23：(N=12,g=4) m=1 s=6 pt=10 d₁=4 d₂=6（canonical 协议逐格锚在案）。 -/
example : StructConcl 12 4 6 (fun x => decide (x ∈ [1, 5, 9, 10])) :=
  case2_struct_r1 12 4 6 (fun x => decide (x ∈ [1, 5, 9, 10])) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- 样本 14/23：(N=12,g=4) m=1 s=7 pt=11 d₁=4 d₂=6（canonical 协议逐格锚在案）。 -/
example : StructConcl 12 4 7 (fun x => decide (x ∈ [1, 5, 9, 11])) :=
  case2_struct_r1 12 4 7 (fun x => decide (x ∈ [1, 5, 9, 11])) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- 样本 15/23：(N=15,g=3) m=1 s=0 pt=3 d₁=6 d₂=7（canonical 协议逐格锚在案）。 -/
example : StructConcl 15 3 0 (fun x => decide (x ∈ [1, 3, 4, 7, 10, 13])) :=
  case2_struct_r1 15 3 0 (fun x => decide (x ∈ [1, 3, 4, 7, 10, 13])) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- 样本 16/23：(N=15,g=3) m=1 s=2 pt=5 d₁=6 d₂=7（canonical 协议逐格锚在案）。 -/
example : StructConcl 15 3 2 (fun x => decide (x ∈ [1, 4, 5, 7, 10, 13])) :=
  case2_struct_r1 15 3 2 (fun x => decide (x ∈ [1, 4, 5, 7, 10, 13])) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- 样本 17/23：(N=15,g=3) m=1 s=3 pt=6 d₁=6 d₂=7（canonical 协议逐格锚在案）。 -/
example : StructConcl 15 3 3 (fun x => decide (x ∈ [1, 4, 6, 7, 10, 13])) :=
  case2_struct_r1 15 3 3 (fun x => decide (x ∈ [1, 4, 6, 7, 10, 13])) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- 样本 18/23：(N=15,g=5) m=1 s=2 pt=7 d₁=4 d₂=9（canonical 协议逐格锚在案）。 -/
example : StructConcl 15 5 2 (fun x => decide (x ∈ [1, 6, 7, 11])) :=
  case2_struct_r1 15 5 2 (fun x => decide (x ∈ [1, 6, 7, 11])) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- 样本 19/23：(N=15,g=5) m=1 s=3 pt=8 d₁=4 d₂=9（canonical 协议逐格锚在案）。 -/
example : StructConcl 15 5 3 (fun x => decide (x ∈ [1, 6, 8, 11])) :=
  case2_struct_r1 15 5 3 (fun x => decide (x ∈ [1, 6, 8, 11])) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- 样本 20/23：(N=15,g=5) m=1 s=4 pt=9 d₁=4 d₂=9（canonical 协议逐格锚在案）。 -/
example : StructConcl 15 5 4 (fun x => decide (x ∈ [1, 6, 9, 11])) :=
  case2_struct_r1 15 5 4 (fun x => decide (x ∈ [1, 6, 9, 11])) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- 样本 21/23：(N=15,g=5) m=1 s=7 pt=12 d₁=4 d₂=9（canonical 协议逐格锚在案）。 -/
example : StructConcl 15 5 7 (fun x => decide (x ∈ [1, 6, 11, 12])) :=
  case2_struct_r1 15 5 7 (fun x => decide (x ∈ [1, 6, 11, 12])) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- 样本 22/23：(N=8,g=1) m=0 s=0 pt=1 d₁=1 d₂=5（canonical 协议逐格锚在案）。 -/
example : StructConcl 8 1 0 (fun x => decide (x ∈ [1])) :=
  case2_struct_r1 8 1 0 (fun x => decide (x ∈ [1])) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- 样本 23/23：(N=12,g=2) m=0 s=0 pt=2 d₁=1 d₂=9（canonical 协议逐格锚在案）。 -/
example : StructConcl 12 2 0 (fun x => decide (x ∈ [2])) :=
  case2_struct_r1 12 2 0 (fun x => decide (x ∈ [2])) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- 联动件：样本 1/23 即 deep_F3 回炉终验最小坐标（U2U32663.I8c/C1m8，α 支：
T=(0,6,4)、d=(5,1,1)、C₁={1,2,3,5,7}=⟨2⟩-整轨道 {1,3,5,7}∪{2}、头 s=0、单点 pt=2）——
结构定理在主定理实例坐标上直接落地（两路线并存的机器锚点）。 -/
example : StructConcl 8 2 0 C1m8 :=
  case2_struct_r1 8 2 0 C1m8 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

end F2663

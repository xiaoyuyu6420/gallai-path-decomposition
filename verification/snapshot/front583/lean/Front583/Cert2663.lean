/-
  Cert2663.lean — 266.3(so1) 承重机器账证书化（Lean 五步之第五步【机器账证书化】首攻，deep_L8 棒）
  账源：front583/campaign/deep_01_holechain_bound.md §8 E1（N=6: 588 实例/5,724 合法对/2,613
  witness；N=8: 30,760/701,360/285,372；§6 E2 定理 D 三域 588/30,760/634,960）、
  deep_L20a M1/L20b R2/L21b W1-W2（锚值与直方图 {0:190,1:398}/{0:20308,1:10452} 逐位）。
  域口径（deep_L8 净域实验钉死，双实现对拍逐位命中三域）：组合典范 T（每无序三元组按
  (t₃,t₁,t₂) 键字典序取角色代表）× 全 P 掩码 × d=(d₁,d₂,d₃) 各≥1 × β≥1 × 容量准入 × so1。
  方案 A（Lean 内直算）：全域账 ledger6 以 kernel 可计算定义承载，native_decide 验证；
  方案 B（证书文件）：净域 /tmp/deepL8x/cert6.txt 逐 witness 证书 + md5 双录，Lean 端
  witValid 校验谓词对抽样+计数核对（#eval 级，零枚举）。
  keys 桥一般化（L7 开口②）：hmod2g 前提由 d13 定义层/so1 见证提取一般导出，实例级
  decide 仅剩「k=2 是见证」一次判定。
  诚实落款：直算经 native_decide（公理 Lean.ofReduceBool，非未证断言件）；kernel decide 在
  200k/4M heartbeats 下 whnf 超时（探针留痕 /tmp/deepL8x/probe3decide.lean）；判定层
  语义（val/Qof/mset/pcard/beta/d12/d13）全部承 F2663（2663Core/U2U32663），零重定义。
-/
import Front583.U2U32663

namespace F2663.Cert

/-! ### 1. 组合典范序（域口径的 Lean 承载） -/

/-- 三元组字典序 ≤（Bool 层）。 -/
def lex3LE (x y : Nat × Nat × Nat) : Bool :=
  x.1 < y.1 || (x.1 == y.1 && (x.2.1 < y.2.1 || (x.2.1 == y.2.1 && x.2.2 ≤ y.2.2)))

/-- 角色典范键：(t₃, t₁, t₂)。 -/
def ckey (t : Nat × Nat × Nat) : Nat × Nat × Nat := (t.2.2, t.1, t.2.1)

/-- 组合典范 T：两两不同，且键 (t₃,t₁,t₂) 在 6 个角色排列的键中字典序最小。 -/
def isCanonT (a b c : Nat) : Bool :=
  a != b && a != c && b != c &&
  lex3LE (ckey (a, b, c)) (ckey (a, c, b)) &&
  lex3LE (ckey (a, b, c)) (ckey (b, a, c)) &&
  lex3LE (ckey (a, b, c)) (ckey (b, c, a)) &&
  lex3LE (ckey (a, b, c)) (ckey (c, a, b)) &&
  lex3LE (ckey (a, b, c)) (ckey (c, b, a))

/-- 典范 T 列表（Z_N 上全部无序三元组的角色代表）。 -/
def domT (N : Nat) : List (Nat × Nat × Nat) :=
  ((List.range N).flatMap fun a => (List.range N).flatMap fun b =>
    (List.range N).map fun c => (a, b, c)).filter (fun t => isCanonT t.1 t.2.1 t.2.2)

/-! ### 2. 域谓词（F2663.wf ∪ so1 的 Bool 化；判定层零漂移） -/

/-- so1 的 Bool 化（F2663.so1 同式：δ₁₂≠0 ∧ ∃k∈[2, N/gcd(δ₁₂,N))，k·δ₁₂≡δ₁₃）。 -/
def so1B (I : Inst2663) : Bool :=
  d12 I != 0 && (List.range (I.N / Nat.gcd (d12 I) I.N)).any
    (fun k => 2 ≤ k && (k * d12 I) % I.N == d13 I)

/-- 实例域谓词：win + dᵢ≥1 + 两两不同 + β≥1 + 容量准入 + so1。 -/
def instOK (I : Inst2663) : Bool :=
  I.t1 < I.N && I.t2 < I.N && I.t3 < I.N &&
  0 < I.d1 && 0 < I.d2 && 0 < I.d3 &&
  I.t1 != I.t2 && I.t1 != I.t3 && I.t2 != I.t3 &&
  1 ≤ beta I && I.d1 ≤ pcard I - (if I.P I.t1 then 1 else 0) &&
  so1B I

/-- 域实例条目：((t₁,t₂,t₃), mP, d₁, (d₂, d₃))；P 以掩码承载。 -/
abbrev DomE := (Nat × Nat × Nat) × Nat × Nat × Nat × Nat

/-- 域实例 → 判定层实例（P := mset N mP，F2663.mset 承载）。 -/
def mkI (N : Nat) (e : DomE) : Inst2663 :=
  { N := N, P := mset N e.2.1, t1 := e.1.1, t2 := e.1.2.1, t3 := e.1.2.2,
    d1 := e.2.2.1, d2 := e.2.2.2.1, d3 := e.2.2.2.2 }

/-- 全域实例列表：典范 T × P 掩码 × d 三元组，域谓词过滤。 -/
def domList (N : Nat) : List DomE :=
  (domT N).flatMap fun t =>
    (List.range (2 ^ N)).flatMap fun m =>
      (List.range N).flatMap fun d1 =>
        (List.range N).flatMap fun d2 =>
          (List.range N).filterMap fun d3 =>
            let e : DomE := (t, m, d1, (d2, d3))
            if instOK (mkI N e) then some e else none

/-! ### 3. 合法对枚举与全域账 -/

/-- C₁ 合法性：⊆P∖{t₁} ∧ |C₁|=d₁（LegalPair 前两件的掩码层同式）。 -/
def c1ok (N : Nat) (I : Inst2663) (mC1 : Nat) : Bool :=
  (List.range N).all (fun x => !(mset N mC1 x) || (I.P x && x != I.t1)) &&
  (List.range N).countP (mset N mC1) == I.d1

/-- C₂ 合法性：⊆Q(C₁) ∧ |C₂|=d₂（LegalPair 后两件；Q := F2663.Qof）。 -/
def c2ok (N : Nat) (I : Inst2663) (mC1 mC2 : Nat) : Bool :=
  (List.range N).all (fun x => !(mset N mC2 x) || Qof I (mset N mC1) x) &&
  (List.range N).countP (mset N mC2) == I.d2

/-- 单实例账：(合法对数, val≤1 witness 数, minval)。 -/
def instLedger (N : Nat) (e : DomE) : Nat × Nat × Nat :=
  let I := mkI N e
  let ps : List (Nat × Nat) :=
    (List.range (2 ^ N)).flatMap fun mc1 =>
      if c1ok N I mc1 then
        (List.range (2 ^ N)).filterMap fun mc2 =>
          if c2ok N I mc1 mc2 then some (mc1, mc2) else none
      else []
  let vals := ps.map (fun p => val I (mset N p.1) (mset N p.2))
  (vals.length, vals.countP (fun v => v ≤ 1), vals.foldl min N)

/-- N=6 全域账五元组：(合法对 5,724, witness 2,613, minval=0 档 190, minval=1 档 398, 实例 588)。 -/
def ledger6 : Nat × Nat × Nat × Nat × Nat :=
  let ls := (domList 6).map (instLedger 6)
  (ls.map (·.1) |>.sum, ls.map (·.2.1) |>.sum,
   ls.countP (fun l => l.2.2 == 0), ls.countP (fun l => l.2.2 == 1), ls.length)

/-- N=8 域实例计数账。 -/
def domCount8 : Nat := (domList 8).length

/-! ### 4. 账定理（native_decide 直算；与 deep_01 E1 / L21b W1-W2 锚逐位互钉） -/

/-- **N=6 全域账**（deep_01 §8 E1、L21b W1 锚：5,724 合法对/2,613 witness/{0:190,1:398}/588 实例）。 -/
theorem ledger6_ok : ledger6 = (5724, 2613, 190, 398, 588) := by native_decide

/-- **N=6 域实例计数**（deep_01 §8 E1 锚 588）。 -/
theorem domList6_len : (domList 6).length = 588 := by native_decide

/-- **N=8 域实例计数**（deep_01 §8 E1 / L21b W2 锚 30,760；定理 D 三域之二）。 -/
theorem domCount8_ok : domCount8 = 30760 := by native_decide

/-- **N=8 典范 T 数**（域分解副账：C(8,3)=56）。 -/
theorem domT8_len : (domT 8).length = 56 := by native_decide

/-- **N=6 典范 T 数**（域分解副账：C(6,3)=20）。 -/
theorem domT6_len : (domT 6).length = 20 := by native_decide

/-! ### 5. keys 桥一般化（L7 开口②：hmod2g 从实例级 decide 升一般引理） -/

/-- **定义层对接**：δ₁₃ 恒等于 (t₁+N−t₃)%N——so1-k=2 见证的等式 (2·δ₁₂)%N=δ₁₃ 即 keys 桥
前提 hmod2g 的实例无关形态（d13 定义展开，零 decide）。 -/
theorem hmod2g_of_d13_eq (I : Inst2663) (h2 : (2 * d12 I) % I.N = d13 I) :
    (2 * d12 I) % I.N = (I.t1 + I.N - I.t3) % I.N := h2

/-- **so1 见证提取**（一般形态）：区间 [2, N/gcd(δ₁₂,N)) 上见证唯一为 2 时，so1 给出
δ₁₃ ≡ 2δ₁₂ (mod N)——实例级仅需一次 k=2 见证 decide，不再对 keys 三件逐个裸判。 -/
theorem d13_eq_2d12_of_so1 (I : Inst2663) (hso1 : so1 I)
    (hu : ∀ k, 2 ≤ k → k < I.N / Nat.gcd (d12 I) I.N → (k * d12 I) % I.N = d13 I → k = 2) :
    (2 * d12 I) % I.N = d13 I := by
  rcases hso1 with ⟨-, k, hk1, hk2, hkv⟩
  have hke : k = 2 := hu k hk1 hk2 hkv
  subst hke
  exact hkv

/-- **keys 桥实例化**（case2_keys_bridge 的一般对接形态）：keys 桥前提直接由 δ 关系
(2g)%N = δ₁₃（其中 d₁₂=δ₁₂ 的值 g）承载，不再要求裸 (t₁+N−t₃)%N 形态的 decide。 -/
theorem keys_bridge_inst (I : Inst2663) (g : Nat) (hN : 0 < I.N) (hgN : g < I.N)
    (htw : I.t1 < I.N) (ht2 : I.t2 < I.N) (ht3 : I.t3 < I.N)
    (ht2g : (I.t2 + g) % I.N = I.t1) (hgd : d12 I = g)
    (hmod2gI : (2 * g) % I.N = d13 I) (hdist13 : I.t1 ≠ I.t3) :
    (I.t3 + g) % I.N = I.t2 ∧ (2 * g) % I.N ≠ 0 := by
  refine case2_keys_bridge I.N g I.t1 I.t2 I.t3 hN hgN htw ht2 ht3 ht2g ?_ hdist13
  rw [← hgd]
  exact hmod2g_of_d13_eq I (by rw [hgd]; exact hmod2gI)

/-! ### 6. 实例级验证：I8c 的 keys 经一般引理重导（与 U2U32663.lean 裸 keys decide 等价） -/

/-- I8c 的 so1 见证唯一为 k=2：d₁₂=2、N/gcd=4、k∈{2,3}，(3·2)%8=6≠4。 -/
example : so1 I8c := by
  unfold so1
  refine ⟨by decide, ⟨2, by decide, by decide, by decide⟩⟩

/-- I8c 见证唯一性（k=2）：区间 [2,4) 中 k=3 不满足（(3·2)%8=6≠4=δ₁₃）。 -/
example : ∀ k, 2 ≤ k → k < 8 / Nat.gcd (d12 I8c) 8 → (k * d12 I8c) % 8 = d13 I8c → k = 2 := by
  intro k hk1 hk2 hkv
  have h2 : d12 I8c = 2 := rfl
  have h4 : d13 I8c = 4 := rfl
  rw [h2, h4] at hkv
  have hg4 : 8 / Nat.gcd (d12 I8c) 8 = 4 := by decide
  have hk : k = 2 ∨ k = 3 := by omega
  rcases hk with rfl | h3
  · rfl
  · subst h3
    exact absurd hkv (by decide)

/-- I8c 的 keys 二件经一般引理 keys_bridge_inst 重导（δ 关系一次 decide 承载）。 -/
example : (I8c.t3 + 2) % 8 = I8c.t2 ∧ (2 * 2) % 8 ≠ 0 := by
  have h := keys_bridge_inst I8c 2 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) rfl (by decide) (by decide)
  exact h

/-- I12c 的 so1 见证**结构唯一**：N/gcd(d₁₂,N)=12/gcd(8,12)=3 ⟹ 候选区间 [2,3) 仅含 k=2，
一般引理 d13_eq_2d12_of_so1 的唯一性前提由 omega 结构给出（零 decide）。 -/
example : so1 I12c := by
  unfold so1
  refine ⟨by decide, ⟨2, by decide, by decide, by decide⟩⟩

example : (2 * d12 I12c) % 12 = d13 I12c :=
  d13_eq_2d12_of_so1 I12c (by
    unfold so1
    exact ⟨by decide, ⟨2, by decide, by decide, by decide⟩⟩)
    (fun k _ hk2 _ => by
      have h8 : d12 I12c = 8 := rfl
      have hgn : I12c.N = 12 := rfl
      rw [h8, hgn] at hk2
      have hg2 : Nat.gcd 8 12 = 4 := by decide
      rw [hg2] at hk2
      have h34 : (12 : Nat) / 4 = 3 := rfl
      omega)

/-- I12c 的 keys 二件经一般引理重导（与 U2U32663.lean 裸 keys decide 等价）。 -/
example : (I12c.t3 + 8) % 12 = I12c.t2 ∧ (2 * 8) % 12 ≠ 0 := by
  have h := keys_bridge_inst I12c 8 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) rfl (by decide) (by decide)
  exact h

/-! ### 7. 证书校验器（方案 B 前置件；数据件 Cert6Data.lean 承载 2,613 条全表） -/

/-- witness 证书条目：(t₁,t₂,t₃,mP,d₁,d₂,d₃,mC₁,mC₂)。 -/
structure Wit6 where
  t1 : Nat
  t2 : Nat
  t3 : Nat
  mP : Nat
  d1 : Nat
  d2 : Nat
  d3 : Nat
  mC1 : Nat
  mC2 : Nat
deriving BEq

/-- 逐对相异检查（无 mathlib 环境的自含 Nodup Bool 层）。 -/
def nodupCheck : List Wit6 → Bool
  | [] => true
  | a :: t => !t.contains a && nodupCheck t

/-- 证书条目 → 判定层实例。 -/
def witI (w : Wit6) : Inst2663 :=
  { N := 6, P := mset 6 w.mP, t1 := w.t1, t2 := w.t2, t3 := w.t3,
    d1 := w.d1, d2 := w.d2, d3 := w.d3 }

/-- 证书条目校验：域谓词 ∧ C₁ 合法 ∧ C₂ 合法 ∧ val≤1（Lean 端只做检查不做枚举）。 -/
def witValid (w : Wit6) : Bool :=
  let I := witI w
  instOK I && c1ok 6 I w.mC1 && c2ok 6 I w.mC1 w.mC2 &&
  val I (mset 6 w.mC1) (mset 6 w.mC2) ≤ 1

end F2663.Cert

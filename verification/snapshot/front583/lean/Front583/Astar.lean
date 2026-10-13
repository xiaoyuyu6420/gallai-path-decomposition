import Front583.Fan

/-!
# front583 / lane_60 + lane_66b + lane_68：A\* 修复版定理族

语义对照 paper/main.tex §3（thm:Astar 修复版 = lane_31_astar_fix 报告 T31.1；
thm:sep = T31.2）。陈述口径逐字对照：

- (A1) EV(G) 三角无关；
- (A2) 每个高点 v（E-度 ≥ 4）有奇 E-度，且其每个 EV-邻居 w 满足 E-度 w ≤ 3；
- (A4) 存在高点 u 使得每个偶度点 x ∉ {u} ∪ N_EV(u) 满足
  E-度(x) − |N_EV(x) ∩ N_EV(u)| ≤ 3；
- 结论：pn(G) ≤ ⌊n/2⌋。

**lane_68（2026-09-17）Fan 引擎进展**：`reinsert_star`（paper Thm 3.1 Step 3–4
回插引擎）升级为**真证**——缺口收缩为两条逐字对应 Fan 2005 Lem 3.4/3.6
（BS21 Lem 6/7）的接口占位 `fan6_use`/`fan7_use`。真证部分：
`star_not_adj`（(A1) 星顶点两两不相邻）、`deadCount_gStar_le`（吸收引理：
死邻居 ⊆ N_EV(v)∖{u}，个数 ≤ eDeg v − 1 ≤ 2，纯真证无 sorry）、
`lEngine`（L-步序列归纳，预算不变量 |T| + 2 ≤ D(u)）、`gStar_full`
（图回满转移）、组合逻辑与全部计数。`fan_class` 保持占位（Fan 2005 主定理
机器，lane_81 已分解，见下）。lane_68 交接时点本文件共 3 处 sorry：
`fan_class`、`fan6_use`、`fan7_use`，每个都是单一外部结果的一对一占位。
其余全部真证：删星图 `delStar` 基建、度偏移三引理（P1a/P1b/P1c）、
奇偶传播（f1/f2）、EV 单调与 (A1) 遗传（f6）、远偶点刻画（f4）、E-度偏移
（f5）、(A4) 迁移（G̃ 全低 E-度）、宿主端点条件（Step 2）、(A2)/(A3) 遗传、
边数严格下降、预算算术 `budget_last`、强归纳骨架。

**lane_81（2026-09-18）fan_class 分解**：陈述不变；`fan_class` 的缺口从
"整条 Fan 2005 主定理"收缩为两个**一对一机器验证核**：
`fan_class_terminal`（一切 E-度 = 0，EV 无边，Pyber 型无边特例）与
`fan_class_case02`（一切 E-度 ∈ {0,2} 且有 2，EV 非孤立部分 = 不交圈，
Fan 的双圈边删除案例）。归纳组织与**奇 E-度步**（E-度 ∈ {1,3}：整星删除
+ 类遗传 `eDeg_delStar_le3`（新真证）+ `reinsert_star` 回插）全部真证。
机器验证底账：lab/fan81/，n ≤ 6 全空间（26,402 类成员）0 违反；
终态 8,945 例、case02 897 例（且全部存在 Fan 归约式保类双删边）0 违反；
n = 7 全空间（2^21 图，1,491,410 成员；终态 373,409、case02 19,281，
归约 19,281/19,281）0 违反，见 lab/fan81/run_n7_shard*.log。

**lane_82（2026-09-18）最终 mile 攻坚（fan7 机制 + 基例，四 sorry 不变）**：
新增真证三件（`#print axioms` 均无 sorryAx）：`gStar_nil_adj`（gStar 空表
逐点等同 delStar，纯语法改写）、`fan7_step_dead_zero`（全活不变量下 fan6
朝 u 吸收的 passing 过滤器 = 0：与 `deadCount_gStar_le` 的上界互补的精确
清零）、`fan7_use_le_two`（fan7_use 的 k = eDeg G u ≤ 2 完整基例：k=0 取
A=[]；k∈{1,2} 取 A=[v] 用一次 fan6_use——未来 fan7 归纳的底例）。
机制结论（lab/fan82/exp_fan7_mech.py，n ≤ 5 全空间 36,620 实例）：顺序
fan6 吸收的可达上界 = m + min(s,1)（m = D'≥2 星顶点数，s = D'=1 星顶点数；
killed 单端点星顶点堵塞后续步），n=5 存在 105 个 deficit 实例
（seq_opt = 1 < ⌈4/2⌉ = 2，全部 k=4 s=4 形态）而 fan7 结论仍真
（true_opt = 2，赢法 A 100% 呈"每 D'-块恰一星顶点"形态）——**fan7 的
完整证明必需非顺序的全局重排移动**（过 u 合并两块），顺序 fan6 不可证
fan7。四条 sorry（fan6_nf / fan7_use / fan_class_terminal /
fan_class_case02）全部保持，逐一的精确卡点与攻墙路线见
campaign/lane_82_lean_final.md。
**lane_68c（2026-09-18）fan6 接线与最小充分形式**：本文件 import `Fan.lean`
（lane_68b 遗产修复编译后正式入链），两文件重复的 del1 块合并为 Fan.lean
一份；`fan6_use` 从裸 sorry 升级为**组装件** = `fan6_nf`（唯一重排核
sorry，Fan.lean）+ `fan6_case1`（纯真证）+ 轮廓转移（真证）。
A\* Lean 链 sorry 总数不变（4：`fan6_nf`、`fan7_use`、`fan_class_terminal`、
`fan_class_case02`），但 fan6 的缺口面从"整条 Fan 2005 Lem 3.4"收缩为单一
重排核 `fan6_nf`（其陈述经 lane_68b 穷举验证 n ≤ 5 全空间 241,040 例
0 违反、n = 6 后台进行中）。
**最小充分形式分析（消费点；lane_109 §3.3 勘误、lane_111 落盘）**：
`lEngine` 消费 fan6_use 结论的第 1/2/4 子句（IsDecomp、条数不变、b 端 −1）；
**a 端 +1 子句实际被 `fan7_use_le_two`（fan7_use 组装路线，k∈{1,2} 基例的
一次 fan6_use 吸收）消费**——旧文"a 端 +1 与逐点不变子句未消费"失实；
逐点不变子句仅在 lEngine 单点未消费，且旧 fan6_use 组装曾消费 fan6_nf 的
完整逐点轮廓——本分析只对 lEngine 单点成立，不能解读为 fan6_use 记账面
可缩窄。`reinsert_star` 对 `fan7_use` 全子句消费——fan7 陈述无可再缩。
**负结果（lab/fan68c/probe_detour.py）**：曾试探把 fan6_nf 进一步缩为
"Case-2 单步绕行纠正结构必存在"，被 n = 5 穷举否证（241,040 合格实例中
1,710 例失败，如掩码 223 加边 (0,3)），fan6_nf 的级联重排核不可再缩。
**lane_87b（2026-09-19）fan7 分块改接路线收口**：lane_87 机器钉死
（lab/fan87/exp_fan7_route.py，n=4/5 全空间 + n=6 k≥3 剪枝共 2,369,096
实例：R1 无脏星 ⟹ 纯改接匹配达 ⌈k/2⌉、R2 改接缺口 ⟹ 必脏、R3 改接+四
移动贪心全达标）指导下的 Lean 化。新增（matchHalve 系列 + selOf +
fan7_use_clean，全部零 sorry）：**匹配减半引理** `matchHalve`——每星有
端点路径 ⟹ 存在匹配 M（路径互异、星互异、逐对合法）使 |S| ≤ 2|M|
（对路径表归纳：每步配对一路径并剔除其全部至多 2 个星端点）；
`selOf`/`attachOK_of_match`/`matchStars_le_image` 把匹配转成 σ-选取并
验证 lane_86 的 `AttachOK` 接口；`fan7_use_clean`：hend + 全清洁 ⟹
fan7_use 结论完整成立（经 lane_86 底件组装）。`fan7_use` 从单一占位
收缩为两支组装：全清洁支真证；脏星支为 `fan7_use_dirty_moves`
（唯一残余 sorry：W/R 脏星移动 + 头合并 + 首边翻转的级联重排，lane_87
R3 机器验证 0 失败，Lean 化留给后续 lane）。定理本体因依赖本节件移至
`fan7_use_goodForm` 之后，陈述一字未改。

**lane_111（2026-09-19）W4' 止血（编排者裁决，lane_108/109 反例后果）**：
`fan6_nf`（Fan.lean）的 Lean 陈述被机器反例证伪（n = 5 掩码 221，
lane_108 发现、lane_109 三方独立复核）。本 lane 执行 W4'：`fan6_use`
摘除 fan6_nf + fan6_case1 组装、恢复**直接占位 sorry**（陈述与类型签名
一字不动）；fan6_nf 封存为已证假研究件（勿清偿，修复走 W3）。全链
Lean 背书从"依赖已知假定理"恢复为"依赖未证占位"——诚实层级修复，
数学内容零进展；fan6_use/fan7_use/astar 等陈述真实性仍只由机器底账
支撑（双向扫描，见 campaign/lane_109_audit.md §2.2）。sorry 总数
4 → 5（fan6_use 占位新增；fan6_nf 封存保留）。同 lane 修正 lane_68c
"最小充分形式"失实注释（a 端 +1 实被 fan7_use_le_two 消费）并补
Fan.lean 假设面机检件 `gtest221_hab0`。

**lane_120（2026-09-20）W3 第二棒：`fan6_use` 首次部分真证（直用分支）**：
证明体按情形分支重组。**直用分支（真证，`#print axioms` 无 sorryAx）**：
若 D 中已存在 b-端且避开 a 的路 P，则 `fan6_case1`（纯真证）直接给出全部
五子句——此分支不需要任何假设面。机器占比（n = 5 全空间，双向，
`lab120_split`/`lab120_split2` 双实现逐位一致）：直用分支覆盖 430,400 /
482,080 qualifying 实例（89.3%）；剩余域 = 死角域（无避开路 ∧ dead(a)=0 ∧
D(b)=1，44,940）∪ C5 域（无避开路 ∧ dead(a)≥1 ∨ D(b)≥2，6,740），两域
三实现口径 0 违反背书但 Lean 证明未达（死角引理 = 单路改道/编织，纸面
进展与精确障碍见 campaign/lane_120_w3b.md），维持 sorry。sorry 总账 5
不变（fan6_use 的 sorry 从全域收缩为剩余域）。陈述与类型签名一字未动。

**lane_154（2026-09-21）W3 降档棒：`fan6_use` 五子句 → 四子句（C2 直组
完全真证）**：删第 5 子句（其余逐点不动）——组装锁死引理（lane_119 §1）
证明其不可由 C2+case1 组装，消费面（paper 5 应用点 + :329 内嵌 + 本文件
`lEngine`/`fan7_use_le_two`）零依赖第 5 子句。证明体 = Fan.lean
`fan6_use_weak`（C2 直组完全真证）逐字实例；原剩余域 sorry 换位为
`fan6_use_c2`（C2 存在性，机器 0 违反，未证）。sorry 总账 5→5（fan6_use
消除、C2 换位），fan6_use 本体完全真证；陈述 md5 已变（见 lane_154 报告）。
-/

namespace Front583

/-! ## EV 子图结构 -/

/-- EV-邻接：x ≠ y 相邻且两端均偶度（paper §2 的 N_EV 与 EV(G)）。 -/
@[reducible]
def EVAdj {n : Nat} (G : Graph n) (x y : Fin n) : Prop :=
  x ≠ y ∧ G.adjB x y = true ∧ deg G x % 2 = 0 ∧ deg G y % 2 = 0

/-- E-度：v 在 EV(G) 内的邻居个数（paper §2 的 d_EV(v)）。 -/
def eDeg {n : Nat} (G : Graph n) (v : Fin n) : Nat :=
  ((finList n).filter (fun w => decide (EVAdj G v w))).length

/-- 高点：E-度 ≥ 4（隐含偶度；paper §3 "call such a vertex high"）。 -/
def IsHigh {n : Nat} (G : Graph n) (v : Fin n) : Prop := 4 ≤ eDeg G v

/-- 偶度点。 -/
def EvenDeg {n : Nat} (G : Graph n) (v : Fin n) : Prop := deg G v % 2 = 0

/-- (A1)：EV(G) 三角无关。 -/
def A1 {n : Nat} (G : Graph n) : Prop :=
  ∀ x y z : Fin n, EVAdj G x y → EVAdj G y z → EVAdj G x z → False

/-- (A2)：高点有奇 E-度，且其 EV-邻居 E-度 ≤ 3。 -/
def A2 {n : Nat} (G : Graph n) : Prop :=
  ∀ v : Fin n, IsHigh G v → eDeg G v % 2 = 1 ∧ ∀ w : Fin n, EVAdj G v w → eDeg G w ≤ 3

/-- (A3)：不同高点的 EV-邻域无公共点（thm:sep 的分离条件）。 -/
def A3 {n : Nat} (G : Graph n) : Prop :=
  ∀ u x w : Fin n, IsHigh G u → IsHigh G x → u ≠ x → EVAdj G u w → EVAdj G x w → False

/-- N_EV(x) ∩ N_EV(u) 的计数（对齐条件 A4 的扣除项）。 -/
def evCommon {n : Nat} (G : Graph n) (x u : Fin n) : Nat :=
  ((finList n).filter (fun w => decide (EVAdj G x w ∧ EVAdj G u w))).length

/-- (A4)：存在高点 u，一切偶度点 x ∉ {u} ∪ N_EV(u) 满足
    E-度(x) − |N_EV(x) ∩ N_EV(u)| ≤ 3。 -/
def A4 {n : Nat} (G : Graph n) : Prop :=
  ∃ u : Fin n, IsHigh G u ∧ ∀ x : Fin n, EvenDeg G x → x ≠ u →
    ¬ EVAdj G u x → eDeg G x - evCommon G x u ≤ 3

/-- 连通（自包含版）：任何两点由路径连接。 -/
def Connected {n : Nat} (G : Graph n) : Prop :=
  ∀ x y : Fin n, x = y ∨ ∃ l : List (Fin n),
    2 ≤ l.length ∧ Distinct l ∧ Chain (GAdj G) l ∧ l.head? = some x ∧ lastOf l = some y

/-! ## 基础计数工具（lane_66b；自包含，不依赖 CompleteOdd.lean） -/

/-- filter 谓词逐点相等 ⟹ 长度相等（自包含副本，避免跨文件依赖）。 -/
theorem filterLensCongr {V : Type} (p q : V → Bool) (h : ∀ x, p x = q x) :
    ∀ l : List V, (l.filter p).length = (l.filter q).length
  | [] => rfl
  | a :: t => by
      have hrec := filterLensCongr p q h t
      by_cases hpa : p a = true
      · have hqa : q a = true := h a ▸ hpa
        rw [List.filter_cons, if_pos hpa, List.filter_cons, if_pos hqa,
          List.length_cons, List.length_cons, hrec]
      · have hqa : ¬ (q a = true) := fun hc => hpa (h a ▸ hc)
        rw [List.filter_cons, if_neg hpa, List.filter_cons, if_neg hqa]
        exact hrec

/-- filter 分区：按 q 把 filter p 的元素二划分。 -/
theorem filterLensSplit {V : Type} (p q : V → Bool) : ∀ (l : List V),
    (l.filter p).length
      = (l.filter (fun x => p x && q x)).length
        + (l.filter (fun x => p x && !q x)).length
  | [] => rfl
  | a :: t => by
      have hrec := filterLensSplit p q t
      by_cases hp : p a = true
      · by_cases hq : q a = true
        · have h2 : (p a && q a) = true := by simp [hp, hq]
          have h3 : ¬((p a && !q a) = true) := by simp [hp, hq]
          rw [List.filter_cons, List.filter_cons, List.filter_cons,
            if_pos hp, if_pos h2, if_neg h3]
          simp only [List.length_cons]
          omega
        · have h2 : ¬((p a && q a) = true) := by simp [hp, hq]
          have h3 : (p a && !q a) = true := by simp [hp, hq]
          rw [List.filter_cons, List.filter_cons, List.filter_cons,
            if_pos hp, if_neg h2, if_pos h3]
          simp only [List.length_cons]
          omega
      · have h0 : p a = false := by
          cases hb : p a with
          | false => rfl
          | true => exact absurd hb hp
        have h2 : ¬((p a && q a) = true) := by simp [h0]
        have h3 : ¬((p a && !q a) = true) := by simp [h0]
        rw [List.filter_cons, List.filter_cons, List.filter_cons,
          if_neg hp, if_neg h2, if_neg h3]
        exact hrec

/-- 互异列表中"等于 a"的过滤至多挑出 1 个元素。 -/
theorem distinctFilterEqLen {V : Type} [DecidableEq V] : ∀ (l : List V) (a : V),
    Distinct l → (l.filter (fun x => decide (x = a))).length ≤ 1
  | [], _, _ => by simp
  | b :: t, a, hd => by
      obtain ⟨hnb, hdt⟩ := hd
      rw [List.filter_cons]
      cases hba : decide (b = a) with
      | false =>
        show (List.filter (fun x => decide (x = a)) t).length ≤ 1
        exact distinctFilterEqLen t a hdt
      | true =>
        show (b :: List.filter (fun x => decide (x = a)) t).length ≤ 1
        have ha : b = a := decide_eq_true_iff.1 hba
        have htnil : (t.filter (fun x => decide (x = a))).length = 0 := by
          refine filter_nil_len _ t (fun x hx => ?_)
          have hxa : x ≠ a := by
            intro hc
            exact hnb (ha ▸ hc ▸ hx)
          simp [hxa]
        rw [List.length_cons, htnil]
        exact Nat.le_refl 1

/-- LB1(ii) 计数形式：奇度点在任意分解中以 v 为端点的路径数 > 0。 -/
theorem vEndCount_pos_of_odd {n : Nat} (G : Graph n) (D : List (List (Fin n)))
    (hD : IsDecomp G D) (v : Fin n) (hv : deg G v % 2 = 1) : 0 < vEndCount D v := by
  have hsum := sumVInc_eq_deg G v D hD
  have hpar := sumVInc_parity v D (decomp_paths G D hD)
  rcases Nat.eq_zero_or_pos (vEndCount D v) with h0 | h0
  · rw [h0, Nat.zero_mod] at hpar
    rw [hsum] at hpar
    omega
  · exact h0

/-- 有 EV-邻居 ⟹ 偶度。 -/
theorem evenDeg_of_eDeg_pos {n : Nat} (G : Graph n) (v : Fin n) (h : 0 < eDeg G v) :
    EvenDeg G v := by
  unfold eDeg at h
  have hne : (finList n).filter (fun w => decide (EVAdj G v w)) ≠ [] := by
    intro h0
    rw [h0] at h
    simp at h
  obtain ⟨w, hw⟩ := List.exists_mem_of_ne_nil _ hne
  have hd : decide (EVAdj G v w) = true := (List.mem_filter.1 hw).2
  exact (decide_eq_true_iff.1 hd).2.2.1

/-- E-度 > 0 ⟹ 存在 EV-邻居。 -/
theorem exists_EVAdj_of_pos {n : Nat} (G : Graph n) (v : Fin n) (h : 0 < eDeg G v) :
    ∃ w : Fin n, EVAdj G v w := by
  unfold eDeg at h
  have hne : (finList n).filter (fun w => decide (EVAdj G v w)) ≠ [] := by
    intro h0
    rw [h0] at h
    simp at h
  obtain ⟨w, hw⟩ := List.exists_mem_of_ne_nil _ hne
  exact ⟨w, decide_eq_true_iff.1 (List.mem_filter.1 hw).2⟩

/-! ## 删星图：G̃ = delStar G u（删去 u 的全部 E-星边） -/

/-- delStar 的邻接：G 的邻接去掉 u–N_EV(u) 星边。 -/
def delAdj {n : Nat} (G : Graph n) (u x y : Fin n) : Bool :=
  G.adjB x y && !decide ((x = u ∧ EVAdj G u y) ∨ (y = u ∧ EVAdj G u x))

theorem delAdj_true_iff {n : Nat} (G : Graph n) (u x y : Fin n) :
    delAdj G u x y = true ↔
      G.adjB x y = true ∧ ¬((x = u ∧ EVAdj G u y) ∨ (y = u ∧ EVAdj G u x)) := by
  unfold delAdj
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.1 h
    refine ⟨h1, ?_⟩
    intro hc
    have hsf : decide ((x = u ∧ EVAdj G u y) ∨ (y = u ∧ EVAdj G u x)) = false := by
      cases hdec : decide ((x = u ∧ EVAdj G u y) ∨ (y = u ∧ EVAdj G u x)) with
      | false => rfl
      | true => rw [hdec] at h2; exact Bool.noConfusion h2
    exact (decide_eq_false_iff_not |>.1 hsf) hc
  · intro ⟨h1, h2⟩
    refine Bool.and_eq_true_iff.2 ⟨h1, ?_⟩
    rw [decide_eq_false_iff_not.2 h2]
    rfl

theorem delAdj_symm {n : Nat} (G : Graph n) (u x y : Fin n) (h : delAdj G u x y = true) :
    delAdj G u y x = true := by
  obtain ⟨h1, h2⟩ := (delAdj_true_iff G u x y).1 h
  refine (delAdj_true_iff G u y x).2 ⟨G.symm x y h1, ?_⟩
  intro hc
  apply h2
  rcases hc with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · exact Or.inr ⟨e1, e2⟩
  · exact Or.inl ⟨e1, e2⟩

theorem delAdj_loop {n : Nat} (G : Graph n) (u x : Fin n) : delAdj G u x x = false := by
  unfold delAdj
  rw [G.loopless x]
  rfl

/-- 删星图 G̃ = G − {uv : v ∈ N_EV(u)}（paper Thm 3.1 的 G − F）。 -/
def delStar {n : Nat} (G : Graph n) (u : Fin n) : Graph n :=
  ⟨delAdj G u, delAdj_symm G u, delAdj_loop G u⟩

theorem delStar_adj_iff {n : Nat} (G : Graph n) (u x y : Fin n) :
    (delStar G u).adjB x y = true ↔
      G.adjB x y = true ∧ ¬((x = u ∧ EVAdj G u y) ∨ (y = u ∧ EVAdj G u x)) :=
  delAdj_true_iff G u x y

/-! ## 度偏移三引理（paper Step 1 的度数记账） -/

/-- (P1a) 远点（x ≠ u 且非 EV-邻居）度数不变。 -/
theorem deg_delStar_of_far {n : Nat} (G : Graph n) (u x : Fin n)
    (hx1 : x ≠ u) (hx2 : ¬ EVAdj G u x) :
    deg (delStar G u) x = deg G x := by
  show ((finList n).filter (delAdj G u x)).length
      = ((finList n).filter (G.adjB x)).length
  have hdec : ∀ w : Fin n,
      decide ((x = u ∧ EVAdj G u w) ∨ (w = u ∧ EVAdj G u x)) = false := by
    intro w
    refine decide_eq_false_iff_not.2 ?_
    rintro (⟨he, _⟩ | ⟨_, hv⟩)
    · exact hx1 he
    · exact hx2 hv
  refine filterLensCongr _ _ (fun w => ?_) (finList n)
  unfold delAdj
  rw [hdec w, Bool.not_false, Bool.and_true]

/-- (P1b) 星心：deg G̃(u) + d_EV(u) = deg G(u)。 -/
theorem deg_delStar_u {n : Nat} (G : Graph n) (u : Fin n) :
    deg (delStar G u) u + eDeg G u = deg G u := by
  have hsplit := filterLensSplit (G.adjB u) (fun w => decide (EVAdj G u w)) (finList n)
  have hcongr1 : ((finList n).filter
      (fun w => G.adjB u w && decide (EVAdj G u w))).length = eDeg G u := by
    refine filterLensCongr (fun w => G.adjB u w && decide (EVAdj G u w))
      (fun w => decide (EVAdj G u w)) (fun w => ?_) (finList n)
    by_cases h : G.adjB u w = true
    · have step1 : (G.adjB u w && decide (EVAdj G u w))
          = (true && decide (EVAdj G u w)) :=
        congrArg (fun b => b && decide (EVAdj G u w)) h
      rw [step1, Bool.true_and]
    · have h0 : G.adjB u w = false := by
        cases hb : G.adjB u w with
        | false => rfl
        | true => exact absurd hb h
      have hna : ¬ EVAdj G u w := fun hc => h hc.2.1
      have step1 : (G.adjB u w && decide (EVAdj G u w))
          = (false && decide (EVAdj G u w)) :=
        congrArg (fun b => b && decide (EVAdj G u w)) h0
      rw [step1, Bool.false_and, decide_eq_false_iff_not.2 hna]
  have hkey : ∀ w : Fin n,
      decide ((u = u ∧ EVAdj G u w) ∨ (w = u ∧ EVAdj G u u)) = decide (EVAdj G u w) := by
    intro w
    by_cases h : EVAdj G u w
    · rw [decide_eq_true_iff.2 (Or.inl ⟨rfl, h⟩), decide_eq_true_iff.2 h]
    · have hf : ¬((u = u ∧ EVAdj G u w) ∨ (w = u ∧ EVAdj G u u)) := by
        rintro (⟨_, hc⟩ | ⟨_, hc⟩)
        · exact h hc
        · exact absurd hc.1 (fun h1 => h1 rfl)
      rw [decide_eq_false_iff_not.2 hf, decide_eq_false_iff_not.2 h]
  have hcongr2 : ((finList n).filter
      (fun w => G.adjB u w && !(decide (EVAdj G u w)))).length
      = deg (delStar G u) u := by
    refine filterLensCongr (fun w => G.adjB u w && !(decide (EVAdj G u w)))
      (delAdj G u u) (fun w => ?_) (finList n)
    unfold delAdj
    rw [hkey w]
  have hL : ((finList n).filter (G.adjB u)).length = deg G u := rfl
  rw [hL, hcongr1, hcongr2] at hsplit
  omega

/-- (P1c) 星顶点：deg G̃(v) + 1 = deg G(v)。 -/
theorem deg_delStar_of_star {n : Nat} (G : Graph n) (u v : Fin n) (h : EVAdj G u v) :
    deg (delStar G u) v + 1 = deg G v := by
  have huv : u ≠ v := h.1
  have hadjv : G.adjB v u = true := G.symm u v h.2.1
  have hpt : ∀ w : Fin n, (G.adjB v w && decide (w = u)) = decide (w = u) := by
    intro w
    by_cases hw : w = u
    · subst hw
      rw [decide_eq_true_iff.2 rfl, hadjv, Bool.and_true]
    · rw [decide_eq_false_iff_not.2 hw, Bool.and_false]
  have hone : ((finList n).filter (fun w => decide (w = u))).length = 1 := by
    have hge : 0 < ((finList n).filter (fun w => decide (w = u))).length := by
      have hmem : u ∈ (finList n).filter (fun w => decide (w = u)) :=
        List.mem_filter.2 ⟨mem_finList n u, decide_eq_true_iff.2 rfl⟩
      have hne : ((finList n).filter (fun w => decide (w = u))) ≠ [] :=
        List.ne_nil_of_mem hmem
      cases hF : ((finList n).filter (fun w => decide (w = u))) with
      | nil => exact absurd hF hne
      | cons a l => simp
    have hle := distinctFilterEqLen (finList n) u (distinct_finList n)
    omega
  have hkey : ∀ w : Fin n,
      decide ((v = u ∧ EVAdj G u w) ∨ (w = u ∧ EVAdj G u v)) = decide (w = u) := by
    intro w
    by_cases hw : w = u
    · have hr : ((v = u ∧ EVAdj G u w) ∨ (w = u ∧ EVAdj G u v)) := Or.inr ⟨hw, h⟩
      subst hw
      rw [decide_eq_true_iff.2 rfl]
      exact decide_eq_true_iff.2 hr
    · have hf : ¬((v = u ∧ EVAdj G u w) ∨ (w = u ∧ EVAdj G u v)) := by
        rintro (⟨he, _⟩ | ⟨he, _⟩)
        · exact huv he.symm
        · exact hw he
      rw [decide_eq_false_iff_not.2 hf, decide_eq_false_iff_not.2 hw]
  have hcongr1 : ((finList n).filter
      (fun w => G.adjB v w && decide (w = u))).length = 1 := by
    refine Eq.trans (filterLensCongr (fun w => G.adjB v w && decide (w = u))
      (fun w => decide (w = u)) hpt (finList n)) hone
  have hcongr2 : ((finList n).filter
      (fun w => G.adjB v w && !(decide (w = u)))).length = deg (delStar G u) v := by
    refine filterLensCongr (fun w => G.adjB v w && !(decide (w = u)))
      (delAdj G u v) (fun w => ?_) (finList n)
    unfold delAdj
    rw [hkey w]
  have hsplit := filterLensSplit (G.adjB v) (fun w => decide (w = u)) (finList n)
  have hL : ((finList n).filter (G.adjB v)).length = deg G v := rfl
  rw [hL, hcongr1, hcongr2] at hsplit
  omega

/-! ## 奇偶传播与结构刻画（paper Step 1 的 (f1)–(f4)） -/

/-- 星心与星顶点在 G̃ 中均为奇度（(f1)(f2)）。 -/
theorem odd_delStar_u {n : Nat} (G : Graph n) (u : Fin n)
    (huOddE : eDeg G u % 2 = 1) :
    deg (delStar G u) u % 2 = 1 ∧
      ∀ v : Fin n, EVAdj G u v → deg (delStar G u) v % 2 = 1 := by
  constructor
  · have h1 := deg_delStar_u G u
    have h2 : deg G u % 2 = 0 :=
      evenDeg_of_eDeg_pos G u (by
        have hne : eDeg G u ≠ 0 := by
          intro h0
          rw [h0] at huOddE
          omega
        exact Nat.pos_of_ne_zero hne)
    have hmod := Nat.mod_two_eq_zero_or_one (deg (delStar G u) u)
    rcases hmod with h | h
    · omega
    · exact h
  · intro v hv
    have h1 := deg_delStar_of_star G u v hv
    have h2 : deg G v % 2 = 0 := hv.2.2.2
    have hmod := Nat.mod_two_eq_zero_or_one (deg (delStar G u) v)
    rcases hmod with h | h
    · omega
    · exact h

/-- (f4) G̃ 中的偶度点必是 G 的远偶点：x ∉ {u} ∪ N_EV(u) 且在 G 中偶度。 -/
theorem evenFar_of_delStar {n : Nat} (G : Graph n) (u x : Fin n)
    (huOddE : eDeg G u % 2 = 1) (h : EvenDeg (delStar G u) x) :
    x ≠ u ∧ ¬ EVAdj G u x ∧ EvenDeg G x := by
  obtain ⟨hu1, hu2⟩ := odd_delStar_u G u huOddE
  unfold EvenDeg at h
  by_cases hx1 : x = u
  · subst hx1
    exact absurd h (by omega)
  by_cases hx2 : EVAdj G u x
  · have h1 := deg_delStar_of_star G u x hx2
    have h2 : deg G x % 2 = 0 := hx2.2.2.2
    have hmod := Nat.mod_two_eq_zero_or_one (deg (delStar G u) x)
    rcases hmod with h0 | h0
    · exact absurd h (by omega)
    · exact absurd h0 (by omega)
  · refine ⟨hx1, hx2, ?_⟩
    show deg G x % 2 = 0
    have hfar := deg_delStar_of_far G u x hx1 hx2
    rw [← hfar]
    exact h

/-- EV 单调：EVAdj G̃ ⟹ EVAdj G（(f6) 的基础）。 -/
theorem EVAdj_delStar_mono {n : Nat} (G : Graph n) (u x y : Fin n)
    (huOddE : eDeg G u % 2 = 1) (h : EVAdj (delStar G u) x y) :
    EVAdj G x y := by
  obtain ⟨hxy, hadj, hx, hy⟩ := h
  refine ⟨hxy, ?_, ?_, ?_⟩
  · exact ((delAdj_true_iff G u x y).1
      (show delAdj G u x y = true from hadj)).1
  · exact (evenFar_of_delStar G u x huOddE hx).2.2
  · exact (evenFar_of_delStar G u y huOddE hy).2.2

/-- (A1) 遗传：EV(G̃) 是 EV(G) 的诱导子图，三角无关自动继承（(f6)）。 -/
theorem A1_delStar {n : Nat} (G : Graph n) (u : Fin n)
    (huOddE : eDeg G u % 2 = 1) (h1 : A1 G) : A1 (delStar G u) := by
  intro x y z hxy hyz hxz
  exact h1 x y z (EVAdj_delStar_mono G u x y huOddE hxy)
    (EVAdj_delStar_mono G u y z huOddE hyz) (EVAdj_delStar_mono G u x z huOddE hxz)

/-- 星心在 G̃ 中无 EV-边（E-度 = 0）。 -/
theorem eDeg_delStar_u {n : Nat} (G : Graph n) (u : Fin n)
    (huOddE : eDeg G u % 2 = 1) : eDeg (delStar G u) u = 0 := by
  have hu1 : deg (delStar G u) u % 2 = 1 := (odd_delStar_u G u huOddE).1
  show ((finList n).filter (fun w => decide (EVAdj (delStar G u) u w))).length = 0
  refine filter_nil_len (fun w => decide (EVAdj (delStar G u) u w)) (finList n)
    (fun w _ => ?_)
  cases hd : decide (EVAdj (delStar G u) u w) with
  | false => rfl
  | true =>
    have hE : EVAdj (delStar G u) u w := decide_eq_true_iff.1 hd
    have hpar : deg (delStar G u) u % 2 = 0 := by
      rcases hE with ⟨_, _, hpar, _⟩
      exact hpar
    omega

/-! ## E-度偏移与 (A4) 迁移（paper Step 1 的 (f5)） -/

/-- (P4) 远偶点的 E-度偏移：eDeg G̃(x) + |N_EV(x) ∩ N_EV(u)| = eDeg G(x)。 -/
theorem eDeg_delStar_of_far {n : Nat} (G : Graph n) (u x : Fin n)
    (huOddE : eDeg G u % 2 = 1) (hx1 : x ≠ u) (hx2 : ¬ EVAdj G u x)
    (hxe : EvenDeg G x) :
    eDeg (delStar G u) x + evCommon G x u = eDeg G x := by
  -- hcon：G 的 EV-邻居中避开 {u} ∪ N_EV(u) 者是 G̃ 的 EV-邻居
  have hcon : ∀ w : Fin n, EVAdj G x w →
      (decide (w = u) || decide (EVAdj G u w)) = false →
      EVAdj (delStar G u) x w := by
    intro w hw2 hBf
    have hwu : w ≠ u := by
      intro he
      rw [he] at hBf
      rw [decide_eq_true_iff.2 rfl, Bool.true_or] at hBf
      exact Bool.noConfusion hBf
    have hnw : ¬ EVAdj G u w := by
      intro hc
      cases hd : decide (EVAdj G u w) with
      | false => exact (decide_eq_false_iff_not |>.1 hd) hc
      | true =>
        rw [hd, Bool.or_true] at hBf
        exact Bool.noConfusion hBf
    rcases hw2 with ⟨hw21, hw22, hw23, hw24⟩
    refine ⟨hw21, delAdj_true_iff G u x w |>.2 ⟨hw22, ?_⟩, ?_, ?_⟩
    · rintro (⟨he, _⟩ | ⟨he, _⟩)
      · exact hx1 he
      · exact hwu he
    · have h1 := deg_delStar_of_far G u x hx1 hx2
      rw [h1]
      exact hw23
    · have h1 := deg_delStar_of_far G u w hwu hnw
      rw [h1]
      exact hw24
  -- 逐点刻画：G̃ 的 EV-邻居 = G 的 EV-邻居中避开 {u} ∪ N_EV(u) 者
  have hpoint : ∀ w : Fin n,
      decide (EVAdj (delStar G u) x w)
        = (decide (EVAdj G x w) && !(decide (w = u) || decide (EVAdj G u w))) := by
    intro w
    by_cases hw1 : EVAdj (delStar G u) x w
    · have hmono := EVAdj_delStar_mono G u x w huOddE hw1
      have hfar := evenFar_of_delStar G u w huOddE hw1.2.2.2
      rw [decide_eq_true_iff.2 hw1, decide_eq_true_iff.2 hmono,
        decide_eq_false_iff_not.2 hfar.1, decide_eq_false_iff_not.2 hfar.2.1]
      decide
    · by_cases hw2 : EVAdj G x w
      · rw [decide_eq_false_iff_not.2 hw1, decide_eq_true_iff.2 hw2]
        by_cases hwu : w = u
        · rw [decide_eq_true_iff.2 hwu, Bool.true_or, Bool.not_true, Bool.and_false]
        · by_cases hgw : EVAdj G u w
          · rw [decide_eq_false_iff_not.2 hwu, decide_eq_true_iff.2 hgw,
              Bool.false_or, Bool.not_true, Bool.and_false]
          · exact absurd (hcon w hw2 (by
              show (decide (w = u) || decide (EVAdj G u w)) = false
              rw [decide_eq_false_iff_not.2 hwu, decide_eq_false_iff_not.2 hgw]
              decide)) hw1
      · rw [decide_eq_false_iff_not.2 hw1, decide_eq_false_iff_not.2 hw2,
          Bool.false_and]
  -- 分区计数
  have hsplit := filterLensSplit (fun w => decide (EVAdj G x w))
    (fun w => (decide (w = u) || decide (EVAdj G u w))) (finList n)
  have hcommon : ((finList n).filter
      (fun w => decide (EVAdj G x w) &&
        (decide (w = u) || decide (EVAdj G u w)))).length = evCommon G x u := by
    unfold evCommon
    refine filterLensCongr _ _ (fun w => ?_) (finList n)
    by_cases hw2 : EVAdj G x w
    · by_cases hwu : w = u
      · exfalso
        have huEven : deg G u % 2 = 0 :=
          evenDeg_of_eDeg_pos G u (by
            have hne : eDeg G u ≠ 0 := by
              intro h0; rw [h0] at huOddE; omega
            exact Nat.pos_of_ne_zero hne)
        have hadjxu : G.adjB x u = true := by
          rw [← hwu]
          exact hw2.2.1
        refine hx2 ⟨fun hc => hw2.1 (hc.symm.trans hwu.symm),
          G.symm x u hadjxu, huEven, hxe⟩
      · rw [decide_eq_false_iff_not.2 hwu, Bool.false_or]
        by_cases hgw : EVAdj G u w
        · rw [decide_eq_true_iff.2 hgw, decide_eq_true_iff.2 hw2,
            decide_eq_true_iff.2 ⟨hw2, hgw⟩]
          decide
        · have hR : ¬ ((EVAdj G x w) ∧ (EVAdj G u w)) := fun hc => hgw hc.2
          rw [decide_eq_false_iff_not.2 hgw, Bool.and_false,
            decide_eq_false_iff_not.2 hR]
    · have hR : ¬ ((EVAdj G x w) ∧ (EVAdj G u w)) := fun hc => hw2 hc.1
      rw [decide_eq_false_iff_not.2 hw2, decide_eq_false_iff_not.2 hR,
        Bool.false_and]
  have htilde : eDeg (delStar G u) x
      = ((finList n).filter
        (fun w => decide (EVAdj G x w) &&
          !(decide (w = u) || decide (EVAdj G u w)))).length := by
    exact filterLensCongr (fun w => decide (EVAdj (delStar G u) x w))
      (fun w => decide (EVAdj G x w) && !(decide (w = u) || decide (EVAdj G u w)))
      hpoint (finList n)
  rw [htilde]
  show ((finList n).filter
      (fun w => decide (EVAdj G x w) &&
        !(decide (w = u) || decide (EVAdj G u w)))).length + evCommon G x u
    = ((finList n).filter (fun w => decide (EVAdj G x w))).length
  omega

/-- (A4) 迁移：对齐高点的删星图全低 E-度（paper Step 1 末）。 -/
theorem eDeg_delStar_le {n : Nat} (G : Graph n) (u : Fin n)
    (huHigh : IsHigh G u) (h2 : A2 G)
    (hA4 : ∀ x : Fin n, EvenDeg G x → x ≠ u → ¬ EVAdj G u x →
      eDeg G x - evCommon G x u ≤ 3) :
    ∀ x : Fin n, eDeg (delStar G u) x ≤ 3 := by
  have huOddE : eDeg G u % 2 = 1 := (h2 u huHigh).1
  intro x
  by_cases hx1 : x = u
  · rw [hx1, eDeg_delStar_u G u huOddE]
    exact Nat.zero_le 3
  by_cases hx2 : EVAdj G u x
  · have hodd : deg (delStar G u) x % 2 = 1 := (odd_delStar_u G u huOddE).2 x hx2
    have h0 : eDeg (delStar G u) x = 0 := by
      show ((finList n).filter (fun w => decide (EVAdj (delStar G u) x w))).length = 0
      refine filter_nil_len (fun w => decide (EVAdj (delStar G u) x w)) (finList n)
        (fun w _ => ?_)
      cases hd : decide (EVAdj (delStar G u) x w) with
      | false => rfl
      | true =>
        have hE : EVAdj (delStar G u) x w := decide_eq_true_iff.1 hd
        have hpar : deg (delStar G u) x % 2 = 0 := by
          rcases hE with ⟨_, _, hpar, _⟩
          exact hpar
        omega
    rw [h0]
    exact Nat.zero_le 3
  · by_cases hxe : EvenDeg G x
    · have hP4 := eDeg_delStar_of_far G u x huOddE hx1 hx2 hxe
      have hA4x := hA4 x hxe hx1 hx2
      omega
    · -- x 奇度 ⟹ 在 G̃ 中仍奇度 ⟹ 无 EV-边 ⟹ E-度 0
      have hxe1 : deg G x % 2 = 1 := by
        have h2m := Nat.mod_two_eq_zero_or_one (deg G x)
        unfold EvenDeg at hxe
        omega
      have h0 : eDeg (delStar G u) x = 0 := by
        show ((finList n).filter (fun w => decide (EVAdj (delStar G u) x w))).length = 0
        refine filter_nil_len (fun w => decide (EVAdj (delStar G u) x w)) (finList n)
          (fun w _ => ?_)
        cases hd : decide (EVAdj (delStar G u) x w) with
        | false => rfl
        | true =>
          have hE : EVAdj (delStar G u) x w := decide_eq_true_iff.1 hd
          have hpar : deg (delStar G u) x % 2 = 0 := by
            rcases hE with ⟨_, _, hpar, _⟩
            exact hpar
          have hfar := deg_delStar_of_far G u x hx1 hx2
          omega
      rw [h0]
      exact Nat.zero_le 3

/-! ## lane_81：fan_class 分解的遗传基建 -/

/-- 星顶点在 G̃ 中 E-度 = 0（星顶点奇于 G̃ ⟹ 无 EV-边）。 -/
theorem eDeg_delStar_of_star_eq_zero {n : Nat} (G : Graph n) (u v : Fin n)
    (huOddE : eDeg G u % 2 = 1) (hv : EVAdj G u v) :
    eDeg (delStar G u) v = 0 := by
  have hodd : deg (delStar G u) v % 2 = 1 := (odd_delStar_u G u huOddE).2 v hv
  show ((finList n).filter (fun w => decide (EVAdj (delStar G u) v w))).length = 0
  refine filter_nil_len (fun w => decide (EVAdj (delStar G u) v w)) (finList n)
    (fun w _ => ?_)
  cases hd : decide (EVAdj (delStar G u) v w) with
  | false => rfl
  | true =>
    have hE : EVAdj (delStar G u) v w := decide_eq_true_iff.1 hd
    have hpar : deg (delStar G u) v % 2 = 0 := by
      rcases hE with ⟨_, _, hpar, _⟩
      exact hpar
    omega

/-- 远奇点在 G̃ 中 E-度 = 0（度数不动保持奇）。 -/
theorem eDeg_delStar_of_odd_eq_zero {n : Nat} (G : Graph n) (u x : Fin n)
    (hx1 : x ≠ u) (hx2 : ¬ EVAdj G u x) (hodd : deg G x % 2 = 1) :
    eDeg (delStar G u) x = 0 := by
  have h0 : eDeg (delStar G u) x = 0 := by
    show ((finList n).filter (fun w => decide (EVAdj (delStar G u) x w))).length = 0
    refine filter_nil_len (fun w => decide (EVAdj (delStar G u) x w)) (finList n)
      (fun w _ => ?_)
    cases hd : decide (EVAdj (delStar G u) x w) with
    | false => rfl
    | true =>
      have hE : EVAdj (delStar G u) x w := decide_eq_true_iff.1 hd
      have hpar : deg (delStar G u) x % 2 = 0 := by
        rcases hE with ⟨_, _, hpar, _⟩
        exact hpar
      have hfar := deg_delStar_of_far G u x hx1 hx2
      omega
  exact h0

/-- **类遗传（fan_class 归纳的删星步，lane_81 真证）**：u 有奇 E-度、G 一切
    E-度 ≤ 3 ⟹ G̃ = delStar G u 一切 E-度 ≤ 3。
    证明：u 与星顶点奇于 G̃（E-度 0）；远偶点 x 的 E-度经 (P4) 只降不升
    （eDeg G̃(x) + evCommon = eDeg G(x) ≤ 3）；远奇点度不动（E-度 0）。
    与 (A4) 版 `eDeg_delStar_le` 互不依赖：本引理只需 hlow，不需 A2/A4。 -/
theorem eDeg_delStar_le3 {n : Nat} (G : Graph n) (u : Fin n)
    (huOddE : eDeg G u % 2 = 1) (hlow : ∀ v : Fin n, eDeg G v ≤ 3) :
    ∀ x : Fin n, eDeg (delStar G u) x ≤ 3 := by
  intro x
  by_cases hx1 : x = u
  · rw [hx1, eDeg_delStar_u G u huOddE]
    exact Nat.zero_le 3
  by_cases hx2 : EVAdj G u x
  · rw [eDeg_delStar_of_star_eq_zero G u x huOddE hx2]
    exact Nat.zero_le 3
  · by_cases hxe : EvenDeg G x
    · have hP4 := eDeg_delStar_of_far G u x huOddE hx1 hx2 hxe
      have hxlow := hlow x
      omega
    · have hxe1 : deg G x % 2 = 1 := by
        have h2m := Nat.mod_two_eq_zero_or_one (deg G x)
        unfold EvenDeg at hxe
        omega
      rw [eDeg_delStar_of_odd_eq_zero G u x hx1 hx2 hxe1]
      exact Nat.zero_le 3

/-! ## lane_68：Fan 回插引擎的图基建（gStar / del1） -/

/-- u 的星顶点表（eDeg 的底层过滤列表，互异）。 -/
def starList {n : Nat} (G : Graph n) (u : Fin n) : List (Fin n) :=
  (finList n).filter (fun w => decide (EVAdj G u w))

theorem starList_length {n : Nat} (G : Graph n) (u : Fin n) :
    (starList G u).length = eDeg G u := rfl

theorem starList_spec {n : Nat} (G : Graph n) (u v : Fin n) :
    v ∈ starList G u ↔ EVAdj G u v :=
  List.mem_filter.trans
    ⟨fun h => decide_eq_true_iff.1 h.2, fun h => ⟨mem_finList n v, decide_eq_true_iff.2 h⟩⟩

theorem starList_distinct {n : Nat} (G : Graph n) (u : Fin n) :
    Distinct (starList G u) :=
  distinct_filter _ (finList n) (distinct_finList n)

/-- delStar 的 u-侧邻接刻画（delAdj 在 x = u 处的化简）。 -/
theorem delAdj_u_iff {n : Nat} (G : Graph n) (u y : Fin n) :
    delAdj G u u y = true ↔ G.adjB u y = true ∧ ¬ EVAdj G u y := by
  rw [delAdj_true_iff]
  have hself : ¬ EVAdj G u u := fun h => h.1 rfl
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun hEV => h2 ?_⟩
    exact Or.inl ⟨rfl, hEV⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    rintro (⟨_, hEV⟩ | ⟨he, hEV⟩)
    · exact h2 hEV
    · exact absurd hEV hself

/-- gStar 的邻接：delStar 的邻接加回 u–L 星边（L ⊆ N_EV(u) 时是合法图）。 -/
def gStarAdj {n : Nat} (G : Graph n) (u : Fin n) (L : List (Fin n)) (x y : Fin n) : Bool :=
  delAdj G u x y || (decide (x = u) && decide (y ∈ L)) || (decide (y = u) && decide (x ∈ L))

theorem gStarAdj_true_iff {n : Nat} (G : Graph n) (u : Fin n) (L : List (Fin n)) (x y : Fin n) :
    gStarAdj G u L x y = true ↔
      delAdj G u x y = true ∨ (x = u ∧ y ∈ L) ∨ (y = u ∧ x ∈ L) := by
  simp only [gStarAdj, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_iff]
  constructor
  · rintro ((h | ⟨e1, e2⟩) | ⟨e1, e2⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨e1, e2⟩)
    · exact Or.inr (Or.inr ⟨e1, e2⟩)
  · rintro (h | (⟨e1, e2⟩ | ⟨e1, e2⟩))
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr ⟨e1, e2⟩)
    · exact Or.inr ⟨e1, e2⟩

theorem gStarAdj_symm {n : Nat} (G : Graph n) (u : Fin n) (L : List (Fin n)) (x y : Fin n)
    (h : gStarAdj G u L x y = true) : gStarAdj G u L y x = true := by
  rw [gStarAdj_true_iff] at h
  rw [gStarAdj_true_iff]
  rcases h with h | ⟨e1, e2⟩ | ⟨e1, e2⟩
  · exact Or.inl (delAdj_symm G u x y h)
  · exact Or.inr (Or.inr ⟨e1, e2⟩)
  · exact Or.inr (Or.inl ⟨e1, e2⟩)

theorem gStarAdj_loop {n : Nat} (G : Graph n) (u : Fin n) (L : List (Fin n))
    (hUL : ∀ v ∈ L, EVAdj G u v) (x : Fin n) : gStarAdj G u L x x = false := by
  unfold gStarAdj
  have hdu : delAdj G u x x = false := delAdj_loop G u x
  by_cases hxu : x = u
  · rw [hxu] at hdu ⊢
    have hnl : u ∉ L := fun hm => (hUL u hm).1 rfl
    simp only [hdu, Bool.false_or, decide_eq_true_iff.2 rfl, decide_eq_false_iff_not.2 hnl,
      Bool.and_false, Bool.false_or]
  · simp only [hdu, Bool.false_or, decide_eq_false_iff_not.2 hxu, Bool.false_and,
      Bool.false_or]

/-- 中间图：delStar G u 加回 u–L 星边（回插引擎的当前图；L = [] 时即 delStar G u）。 -/
def gStar {n : Nat} (G : Graph n) (u : Fin n) (L : List (Fin n))
    (hUL : ∀ v ∈ L, EVAdj G u v) : Graph n :=
  ⟨gStarAdj G u L, gStarAdj_symm G u L, gStarAdj_loop G u L hUL⟩

theorem gStar_adjB {n : Nat} (G : Graph n) (u : Fin n) (L : List (Fin n))
    (hUL : ∀ v ∈ L, EVAdj G u v) :
    (gStar G u L hUL).adjB = gStarAdj G u L := rfl

theorem gStar_loopless {n : Nat} (G : Graph n) (u : Fin n) (L : List (Fin n))
    (hUL : ∀ v ∈ L, EVAdj G u v) (x : Fin n) : (gStar G u L hUL).adjB x x = false :=
  gStarAdj_loop G u L hUL x

theorem gStar_adj_true {n : Nat} (G : Graph n) (u : Fin n) (L : List (Fin n))
    (hUL : ∀ v ∈ L, EVAdj G u v) (x y : Fin n) :
    (gStar G u L hUL).adjB x y = true ↔
      delAdj G u x y = true ∨ (x = u ∧ y ∈ L) ∨ (y = u ∧ x ∈ L) :=
  gStarAdj_true_iff G u L x y

theorem gStar_adj_far {n : Nat} (G : Graph n) (u : Fin n) (L : List (Fin n))
    (hUL : ∀ v ∈ L, EVAdj G u v) {x y : Fin n} (hx : x ≠ u) (hy : y ≠ u) :
    (gStar G u L hUL).adjB x y = true ↔ G.adjB x y = true := by
  constructor
  · intro h
    rw [gStar_adj_true] at h
    rcases h with h | ⟨he, _⟩ | ⟨he, _⟩
    · exact (delAdj_true_iff G u x y).1 h |>.1
    · exact absurd he hx
    · exact absurd he hy
  · intro h
    rw [gStar_adj_true]
    refine Or.inl ((delAdj_true_iff G u x y).2 ⟨h, ?_⟩)
    rintro (⟨he, _⟩ | ⟨he, _⟩)
    · exact hx he
    · exact hy he

theorem gStar_adj_u {n : Nat} (G : Graph n) (u : Fin n) (L : List (Fin n))
    (hUL : ∀ v ∈ L, EVAdj G u v) (y : Fin n) :
    (gStar G u L hUL).adjB u y = true ↔ y ∈ L ∨ (G.adjB u y = true ∧ ¬ EVAdj G u y) := by
  rw [gStar_adj_true, delAdj_u_iff]
  constructor
  · rintro (h | ⟨he, hm⟩ | ⟨he, hm⟩)
    · exact Or.inr ⟨h.1, h.2⟩
    · exact Or.inl hm
    · exact absurd hm (fun hc => (hUL u hc).1 rfl)
  · rintro (hm | ⟨hadj, hnev⟩)
    · exact Or.inr (Or.inl ⟨rfl, hm⟩)
    · exact Or.inl ⟨hadj, hnev⟩

theorem gStar_adj_u' {n : Nat} (G : Graph n) (u : Fin n) (L : List (Fin n))
    (hUL : ∀ v ∈ L, EVAdj G u v) (x : Fin n) :
    (gStar G u L hUL).adjB x u = true ↔ x ∈ L ∨ (G.adjB x u = true ∧ ¬ EVAdj G u x) := by
  constructor
  · intro h
    have h' := (gStar G u L hUL).symm x u h
    rw [gStar_adj_u G u L hUL x] at h'
    rcases h' with hm | ⟨hadj, hnev⟩
    · exact Or.inl hm
    · exact Or.inr ⟨G.symm u x hadj, hnev⟩
  · rintro (hm | ⟨hadj, hnev⟩)
    · exact (gStar G u L hUL).symm u x ((gStar_adj_u G u L hUL x).2 (Or.inl hm))
    · exact (gStar G u L hUL).symm u x
        ((gStar_adj_u G u L hUL x).2 (Or.inr ⟨G.symm x u hadj, hnev⟩))

theorem gStar_adj_mem {n : Nat} (G : Graph n) (u : Fin n) (L : List (Fin n))
    (hUL : ∀ v ∈ L, EVAdj G u v) {v : Fin n} (hv : v ∈ L) :
    (gStar G u L hUL).adjB u v = true ∧ (gStar G u L hUL).adjB v u = true := by
  refine ⟨(gStar_adj_true G u L hUL u v).2 (Or.inr (Or.inl ⟨rfl, hv⟩)),
    (gStar_adj_true G u L hUL v u).2 (Or.inr (Or.inr ⟨rfl, hv⟩))⟩

theorem gStar_adj_notmem {n : Nat} (G : Graph n) (u : Fin n) (L : List (Fin n))
    (hUL : ∀ v ∈ L, EVAdj G u v) {v : Fin n} (hv : EVAdj G u v) (hvL : v ∉ L) :
    (gStar G u L hUL).adjB u v = false ∧ (gStar G u L hUL).adjB v u = false := by
  constructor
  · refine Bool.eq_false_iff.2 (fun h => ?_)
    rw [gStar_adj_u G u L hUL v] at h
    rcases h with hm | ⟨_, hnev⟩
    · exact hvL hm
    · exact hnev hv
  · refine Bool.eq_false_iff.2 (fun h => ?_)
    rw [gStar_adj_u' G u L hUL v] at h
    rcases h with hm | ⟨_, hnev⟩
    · exact hvL hm
    · exact hnev hv

/- 单边删除图 `del1`（lane_68c 起）：定义与基本引理统一由 `Front583.Fan`
    提供（lane_68b 迁入版，与 Astar 原内联副本逐字相同，本文件原副本删除）。
    可用件：`del1`、`del1Adj`、`del1_adj_iff`、`del1Adj_eq_of_ne`、`del1_swap`、
    `deadCount6`（fan6 passing 条件的命名形式）。 -/


/-- 邻接逐点相等的两个图上，分解性互相转移。 -/
theorem decomp_congr {n : Nat} {H₁ H₂ : Graph n} (hEq : ∀ x y, H₁.adjB x y = H₂.adjB x y)
    {D : List (List (Fin n))} (hD : IsDecomp H₁ D) : IsDecomp H₂ D := by
  have hAdj : GAdj H₁ = GAdj H₂ := by
    funext x y
    show (H₁.adjB x y = true) = (H₂.adjB x y = true)
    rw [hEq x y]
  obtain ⟨h1, h2⟩ := hD
  rw [hAdj] at h1
  exact ⟨h1, h2⟩

theorem bool_eq_of_true_iff {b₁ b₂ : Bool} (h : (b₁ = true ↔ b₂ = true)) : b₁ = b₂ := by
  cases h1 : b₁ with
  | false =>
    cases h2 : b₂ with
    | false => rfl
    | true => exact absurd (h.2 h2) (by rw [h1]; exact fun hc => Bool.noConfusion hc)
  | true =>
    cases h2 : b₂ with
    | false => exact absurd (h.1 h1) (by rw [h2]; exact fun hc => Bool.noConfusion hc)
    | true => rfl

/-- 关键步：gStar (L ++ [v]) 删去 uv 恰为 gStar L（逐点邻接）。 -/
theorem del1_gStar_step {n : Nat} (G : Graph n) (u v : Fin n) (hv : EVAdj G u v)
    (L : List (Fin n)) (hUL : ∀ w ∈ L, EVAdj G u w)
    (hUL1 : ∀ w ∈ L ++ [v], EVAdj G u w) (hvL : v ∉ L) (x y : Fin n) :
    (gStar G u L hUL).adjB x y = (del1 (gStar G u (L ++ [v]) hUL1) u v).adjB x y := by
  have hmL : ∀ w : Fin n, w ≠ v → (w ∈ L ++ [v] ↔ w ∈ L) := by
    intro w hwv
    constructor
    · intro hm
      rcases List.mem_append.1 hm with h1 | h2
      · exact h1
      · exact absurd (List.mem_singleton.1 h2) hwv
    · intro hm
      exact List.mem_append.2 (Or.inl hm)
  by_cases hxu : x = u
  · rw [hxu]
    by_cases hyv : y = v
    · rw [hyv]
      have h1 : (gStar G u L hUL).adjB u v = false := (gStar_adj_notmem G u L hUL hv hvL).1
      rw [h1]
      exact (Bool.eq_false_iff.2 (fun hc => by
        obtain ⟨_, hnot⟩ := del1_adj_iff _ _ _ _ _ |>.1 hc
        exact hnot (Or.inl ⟨rfl, rfl⟩))).symm
    · refine bool_eq_of_true_iff ⟨fun hc => ?_, fun hc => ?_⟩
      · rw [gStar_adj_u G u L hUL y] at hc
        rw [del1Adj_eq_of_ne (gStar G u (L ++ [v]) hUL1) u v u y
          (fun hcp => hyv hcp.2) (fun hcp => hv.1 hcp.1)]
        rw [gStar_adj_u G u (L ++ [v]) hUL1 y]
        rcases hc with hm | ⟨hadj, hnev⟩
        · exact Or.inl ((hmL y hyv).2 hm)
        · exact Or.inr ⟨hadj, hnev⟩
      · rw [del1Adj_eq_of_ne (gStar G u (L ++ [v]) hUL1) u v u y
          (fun hcp => hyv hcp.2) (fun hcp => hv.1 hcp.1)] at hc
        rw [gStar_adj_u G u (L ++ [v]) hUL1 y] at hc
        rw [gStar_adj_u G u L hUL y]
        rcases hc with hm | ⟨hadj, hnev⟩
        · exact Or.inl ((hmL y hyv).1 hm)
        · exact Or.inr ⟨hadj, hnev⟩
  · by_cases hyu : y = u
    · rw [hyu]
      by_cases hxv : x = v
      · rw [hxv]
        have h1 : (gStar G u L hUL).adjB v u = false := (gStar_adj_notmem G u L hUL hv hvL).2
        rw [h1]
        exact (Bool.eq_false_iff.2 (fun hc => by
          obtain ⟨_, hnot⟩ := del1_adj_iff _ _ _ _ _ |>.1 hc
          exact hnot (Or.inr ⟨rfl, rfl⟩))).symm
      · refine bool_eq_of_true_iff ⟨fun hc => ?_, fun hc => ?_⟩
        · rw [gStar_adj_u' G u L hUL x] at hc
          rw [del1Adj_eq_of_ne (gStar G u (L ++ [v]) hUL1) u v x u
            (fun hcp => hxu hcp.1) (fun hcp => hxv hcp.1)]
          rw [gStar_adj_u' G u (L ++ [v]) hUL1 x]
          rcases hc with hm | ⟨hadj, hnev⟩
          · exact Or.inl ((hmL x hxv).2 hm)
          · exact Or.inr ⟨hadj, hnev⟩
        · rw [del1Adj_eq_of_ne (gStar G u (L ++ [v]) hUL1) u v x u
            (fun hcp => hxu hcp.1) (fun hcp => hxv hcp.1)] at hc
          rw [gStar_adj_u' G u (L ++ [v]) hUL1 x] at hc
          rw [gStar_adj_u' G u L hUL x]
          rcases hc with hm | ⟨hadj, hnev⟩
          · exact Or.inl ((hmL x hxv).1 hm)
          · exact Or.inr ⟨hadj, hnev⟩
    · refine bool_eq_of_true_iff ⟨fun hc => ?_, fun hc => ?_⟩
      · have hadj : G.adjB x y = true := gStar_adj_far G u L hUL hxu hyu |>.1 hc
        have hrem1 : ¬ (x = u ∧ y = v) := fun hcp => hxu hcp.1
        have hrem2 : ¬ (x = v ∧ y = u) := fun hcp => hyu hcp.2
        rw [del1Adj_eq_of_ne (gStar G u (L ++ [v]) hUL1) u v x y hrem1 hrem2,
          gStar_adj_far G u (L ++ [v]) hUL1 hxu hyu]
        exact hadj
      · obtain ⟨hadj, _⟩ := del1_adj_iff _ _ _ _ _ |>.1 hc
        rw [gStar_adj_true] at hadj
        rcases hadj with hd | ⟨he, _⟩ | ⟨he, _⟩
        · exact gStar_adj_far G u L hUL hxu hyu |>.2
            ((delAdj_true_iff G u x y).1 hd |>.1)
        · exact absurd he hxu
        · exact absurd he hyu

/-- gStar 中远点的度数不变（P1a 的 gStar 版）。 -/
theorem deg_gStar_far {n : Nat} (G : Graph n) (u : Fin n) (L : List (Fin n))
    (hUL : ∀ v ∈ L, EVAdj G u v) (x : Fin n) (hx1 : x ≠ u) (hx2 : ¬ EVAdj G u x) :
    deg (gStar G u L hUL) x = deg G x := by
  show ((finList n).filter (gStarAdj G u L x)).length
      = ((finList n).filter (G.adjB x)).length
  refine filterLensCongr _ _ (fun y => ?_) (finList n)
  by_cases hy : y = u
  · rw [hy]
    have hxl : ¬ (x ∈ L) := by
      intro hm
      exact hx2 (hUL x hm)
    unfold gStarAdj
    rw [decide_eq_false_iff_not.2 hx1, Bool.false_and, Bool.or_false,
      decide_eq_true_iff.2 rfl, Bool.true_and,
      decide_eq_false_iff_not.2 hxl, Bool.or_false]
    unfold delAdj
    have hns : ¬ ((x = u ∧ EVAdj G u u) ∨ (u = u ∧ EVAdj G u x)) := by
      rintro (⟨he, _⟩ | ⟨_, hE⟩)
      · exact hx1 he
      · exact hx2 hE
    rw [decide_eq_false_iff_not.2 hns, Bool.not_false, Bool.and_true]
  · unfold gStarAdj
    rw [decide_eq_false_iff_not.2 hx1, Bool.false_and, decide_eq_false_iff_not.2 hy,
      Bool.false_and, Bool.or_false, Bool.or_false]
    unfold delAdj
    have hns : ¬ ((x = u ∧ EVAdj G u y) ∨ (y = u ∧ EVAdj G u x)) := by
      rintro (⟨he, _⟩ | ⟨he, _⟩)
      · exact hx1 he
      · exact hy he
    rw [decide_eq_false_iff_not.2 hns, Bool.not_false, Bool.and_true]

/-- (A1) 的星顶点两两不相邻推论：回插记账中星顶点永不成为彼此的死候选。 -/
theorem star_not_adj {n : Nat} (G : Graph n) (hA1 : A1 G) (u v w : Fin n)
    (hv : EVAdj G u v) (hw : EVAdj G u w) (hvw : v ≠ w) (hadj : G.adjB v w = true) : False :=
  hA1 u v w hv ⟨hvw, hadj, hv.2.2.2, hw.2.2.2⟩ hw

/-- filter 长度单调（子集注入）。 -/
theorem filter_len_mono {V : Type} (p q : V → Bool) (hpq : ∀ x, p x = true → q x = true) :
    ∀ l : List V, (l.filter p).length ≤ (l.filter q).length
  | [] => by simp
  | a :: t => by
      have hrec := filter_len_mono p q hpq t
      by_cases hp : p a = true
      · have hq : q a = true := hpq a hp
        rw [List.filter_cons, if_pos hp, List.filter_cons, if_pos hq]
        simp only [List.length_cons]
        omega
      · rw [List.filter_cons, if_neg hp, List.filter_cons]
        cases hq : q a with
        | false =>
          show (List.filter p t).length ≤ (List.filter q t).length
          exact hrec
        | true =>
          show (List.filter p t).length ≤ (a :: List.filter q t).length
          simp only [List.length_cons]
          omega

/-! ## lane_68：Fan 吸收引理与回插引擎 -/

/-- **关键吸收引理（lane_31 §3 回插记账的 (A1)-输入；lane_68 真证）**：
    在 gStar G u L（L ⊆ N_EV(u)）中，星顶点 v 的"死"邻居（无端点路径的邻居）
    必落在 N_EV(v) ∖ {u} 内，故个数 ≤ eDeg(v) − 1。
    证明：死 ⟹ 偶度于 gStar（LB1(iii) 逆否）；gStar 中邻 v 的偶点分类：
    u（被预算排除：D(u) > 0）、其它星顶点（(A1) 星顶点两两不相邻）、
    远偶点（度不变 ⟹ 偶于 G ⟹ ∈ N_EV(v)）。 -/
theorem deadCount_gStar_le {n : Nat} (G : Graph n) (u v : Fin n)
    (hA1 : A1 G) (hlow : ∀ w, EVAdj G u w → eDeg G w ≤ 3)
    (L : List (Fin n)) (hUL : ∀ w ∈ L, EVAdj G u w)
    (huv : EVAdj G u v) (hvL : v ∉ L)
    (D : List (List (Fin n))) (hD : IsDecomp (gStar G u L hUL) D)
    (hu : 0 < vEndCount D u) :
    ((finList n).filter
        (fun w => decide ((gStar G u L hUL).adjB v w = true ∧ vEndCount D w = 0))).length
      + 1 ≤ eDeg G v := by
  have hpoint : ∀ w : Fin n,
      (gStar G u L hUL).adjB v w = true → vEndCount D w = 0 → EVAdj G v w := by
    intro w hadj hdead
    have hwu : w ≠ u := by
      intro he
      rw [he] at hdead
      exact absurd hdead (Nat.ne_of_gt hu)
    have hvw : v ≠ w := by
      intro he
      rw [he] at hadj
      exact Bool.noConfusion ((gStar_loopless G u L hUL w).symm.trans hadj)
    have hadjG : G.adjB v w = true :=
      gStar_adj_far G u L hUL (Ne.symm huv.1) hwu |>.1 hadj
    have hweven : deg (gStar G u L hUL) w % 2 = 0 := by
      rcases Nat.mod_two_eq_zero_or_one (deg (gStar G u L hUL) w) with h | h
      · exact h
      · exact absurd hdead (Nat.ne_of_gt
          (vEndCount_pos_of_odd (gStar G u L hUL) D hD w h))
    by_cases hstar : EVAdj G u w
    · exact absurd hadjG (star_not_adj G hA1 u v w huv hstar hvw)
    · have hfar := deg_gStar_far G u L hUL w hwu hstar
      exact ⟨hvw, hadjG, huv.2.2.2, by omega⟩
  -- u 在 G 中偶度（有 EV-邻居 v）
  have hvuE : deg G u % 2 = 0 := evenDeg_of_eDeg_pos G u (by
    rw [show eDeg G u = (starList G u).length from rfl]
    have hmem : v ∈ starList G u := (starList_spec G u v).2 huv
    cases hF : starList G u with
    | nil => rw [hF] at hmem; exact absurd hmem (by simp)
    | cons a l => simp)
  have hvu : EVAdj G v u := ⟨fun he => huv.1 he.symm, G.symm u v huv.2.1, huv.2.2.2, hvuE⟩
  have hdeg : eDeg G v = ((finList n).filter (fun w => decide (EVAdj G v w))).length := rfl
  -- eDeg 分区：w = u 块恰一元素（u ∈ N_EV(v)），非 u 块 ≥ 死邻居数
  have hsplit := filterLensSplit (fun w => decide (EVAdj G v w)) (fun w => decide (w = u))
    (finList n)
  have hcongr1 : ((finList n).filter
      (fun w => decide (EVAdj G v w) && decide (w = u))).length
      = ((finList n).filter (fun w => decide (w = u))).length := by
    refine filterLensCongr _ _ (fun w => ?_) (finList n)
    by_cases hwu : w = u
    · rw [hwu]
      rw [decide_eq_true_iff.2 hvu, Bool.true_and]
    · rw [decide_eq_false_iff_not.2 hwu, Bool.and_false]
  have hge1 : 0 < ((finList n).filter (fun w => decide (w = u))).length := by
    have huin : u ∈ (finList n).filter (fun w => decide (w = u)) :=
      List.mem_filter.2 ⟨mem_finList n u, decide_eq_true_iff.2 rfl⟩
    cases hF : (finList n).filter (fun w => decide (w = u)) with
    | nil => rw [hF] at huin; exact absurd huin (by simp)
    | cons a t => simp
  have hpq : ∀ w : Fin n,
      decide ((gStar G u L hUL).adjB v w = true ∧ vEndCount D w = 0) = true →
      (decide (EVAdj G v w) && !(decide (w = u))) = true := by
    intro w h
    obtain ⟨hadj, hdead⟩ := decide_eq_true_iff.1 h
    have hE := hpoint w hadj hdead
    have hne : w ≠ u := by
      intro he
      rw [he] at hdead
      exact absurd hdead (Nat.ne_of_gt hu)
    rw [decide_eq_true_iff.2 hE, decide_eq_false_iff_not.2 hne, Bool.not_false, Bool.and_true]
  have hmono := filter_len_mono
    (fun w => decide ((gStar G u L hUL).adjB v w = true ∧ vEndCount D w = 0))
    (fun w => decide (EVAdj G v w) && !(decide (w = u))) hpq (finList n)
  rw [hcongr1] at hsplit
  omega

/-- **fan6 接口（lane_154：C2 直组四子句完全真证）**：paper lem:fan6 =
    Fan 2005 Lemma 3.4 = BS21 Lemma 6（"addible edge"）逐字转录到本工程的
    列表表示。语义：uv ∈ E(H)，D 分解 H − uv，若 D(b) 大于 a 在 H − uv 中
    死邻居个数，则 H 有分解 D′：条数不变，端点记账 a +1 / b −1。
    历史：lane_68b/c 曾把本定理组装为 `fan6_nf`（重排核）+ `fan6_case1`
    （延长）两步；lane_108 机器反例（掩码 221）+ lane_109 三方复核证明
    fan6_nf 陈述为假（其逐点轮廓子句不可满足地过强），该组装链作废。
    lane_111（W4'）：摘除组装，恢复直接占位 sorry。
    lane_120（W3 第二棒）：证明体按情形分支重组（直用分支真证 + 剩余域
    占位 sorry）。
    **lane_154（W3 降档棒）**：陈述删第 5 子句（其余逐点不动）降为四子句
    ——组装锁死引理（lane_119 §1）证明第 5 子句不可由 C2+case1 组装，且
    无任何消费者使用（paper 5 应用点 + :329 内嵌 + 本文件 `lEngine`/
    `fan7_use_le_two`，lane_120 消费面核对 + lane_154 独立复核）。证明 =
    `fan6_use_weak`（Fan.lean，C2 直组完全真证）的逐字实例；原五子句
    剩余域缺口换位为 C2 存在性 `fan6_use_c2`（Fan.lean，机器 0 违反，
    未证）。sorry 总账 5→5（fan6_use 的 sorry 消除，C2 换位入 Fan.lean；
    字面 5→4 需 C2 证出或不占账，见 campaign/lane_154_c2downgrade.md）。
    消费面（lane_109 §3.3 勘误）：`lEngine` 用第 1/2/4 子句（IsDecomp、
    条数不变、b 端 −1）；**a 端 +1 被 `fan7_use_le_two`（fan7_use 组装
    路线）消费**。 -/
theorem fan6_use {n : Nat} (H : Graph n) (a b : Fin n) (hab : H.adjB a b = true)
    (D : List (List (Fin n))) (hD : IsDecomp (del1 H a b) D)
    (hpass : ((finList n).filter
        (fun w => decide ((del1 H a b).adjB a w = true ∧ vEndCount D w = 0))).length
      < vEndCount D b) :
    ∃ D' : List (List (Fin n)), IsDecomp H D' ∧ D'.length = D.length ∧
      vEndCount D' a = vEndCount D a + 1 ∧ vEndCount D' b + 1 = vEndCount D b := by
  exact fan6_use_weak H a b hab D hD hpass

/- **fan7 接口位置说明（lane_87b）**：`fan7_use` 的组装依赖 lane_86 的
    `fan7_reattach`/`AttachOK` 与 lane_87b 的匹配计数（matchHalve），需置于
    其定义之后——定理本体已移至 `fan7_use_goodForm` 之后的 lane_87b 节，
    陈述一字未改，消费方 `reinsert_star` 不受影响。原 lane_68 占位 sorry
    收缩为脏星支 `fan7_use_dirty_moves`。 -/

/-! ## lane_82：fan7 步进机制与基例（真证，无新 sorry）

机器侧机制结论（lab/fan82/exp_fan7_mech.py，n ≤ 5 全空间）的 Lean 对应物：

1. `fan7_step_dead_zero`：若当前中间图 gStar G u L 中 u 的全部邻居都活
   （端点计数 > 0），则对星边 u–v 做 fan6 朝 u 吸收（H := gStar (L++[v])，
   a := u，b := v）时 passing 过滤器为空——"全活不变量下每步 fan6 免费"。
   注意与 `deadCount_gStar_le` 的差别：那条给上界（≤ eDeg v − 1），
   本条在全活假设下给精确的 0。
2. `fan7_use_le_two`：fan7_use 在 k = eDeg G u ≤ 2 时的完整基例。
   k = 0 取 A = []；k ∈ {1, 2} 取 A = [v]（任取一个星顶点）并用一次 `fan6_use`
   吸收（passing 由 `fan7_step_dead_zero` + hend 给出；从 delStar 新鲜态出发
   首次吸收的死邻居数恒为 0 < D(v)）。这是未来任何 fan7 归纳证明的底例，
   也是"fan7 的顺序 fan6 机制在前几步免费、卡点在单端点星顶点变死堵塞
   后续步"这一机制的 Lean 级验证（机器侧：lab/fan82 deficit 实验定量确认
   顺序吸收可达上界 = m + min(s,1)，s > m+1 时达不到 ⌈k/2⌉）。 -/

/-- gStar 的空表情形逐点等同于 delStar（lane_82；纯语法层面改写，避免
    gStarAdj 对变元的可判定性归约卡点）。 -/
theorem gStar_nil_adj {n : Nat} (G : Graph n) (u x y : Fin n)
    (hUL0 : ∀ w ∈ ([] : List (Fin n)), EVAdj G u w) :
    (delStar G u).adjB x y = (gStar G u ([] : List (Fin n)) hUL0).adjB x y := by
  show delAdj G u x y = gStarAdj G u ([] : List (Fin n)) x y
  have e1 : (decide (x = u) && decide (y ∈ ([] : List (Fin n)))) = false := by
    cases hd : decide (y ∈ ([] : List (Fin n))) with
    | false => simp
    | true => exact absurd (decide_eq_true_iff.1 hd) List.not_mem_nil
  have e2 : (decide (y = u) && decide (x ∈ ([] : List (Fin n)))) = false := by
    cases hd : decide (x ∈ ([] : List (Fin n))) with
    | false => simp
    | true => exact absurd (decide_eq_true_iff.1 hd) List.not_mem_nil
  simp only [gStarAdj, e1, e2, Bool.false_and, Bool.or_false]

/-- **fan7 步进死邻居清零（lane_82 真证）**：D 分解 gStar G u L，u 在 gStar L 中
    的全部邻居在 D 中活 ⟹ 对 H := gStar G u (L++[v]) 的星边 u–v 做 fan6 朝 u
    吸收时，passing 过滤器（a := u 的死邻居数）为空。 -/
theorem fan7_step_dead_zero {n : Nat} (G : Graph n) (u v : Fin n)
    (L : List (Fin n)) (hUL : ∀ w ∈ L, EVAdj G u w) (hvL : v ∉ L) (hv : EVAdj G u v)
    (hUL1 : ∀ w ∈ L ++ [v], EVAdj G u w)
    (D : List (List (Fin n))) (hD : IsDecomp (gStar G u L hUL) D)
    (halive : ∀ w : Fin n, (gStar G u L hUL).adjB u w = true → 0 < vEndCount D w) :
    ((finList n).filter
        (fun w => decide ((del1 (gStar G u (L ++ [v]) hUL1) u v).adjB u w = true
          ∧ vEndCount D w = 0))).length = 0 := by
  refine filter_nil_len (fun w => decide ((del1 (gStar G u (L ++ [v]) hUL1) u v).adjB u w = true
      ∧ vEndCount D w = 0)) (finList n) (fun w _ => ?_)
  cases hd : (decide ((del1 (gStar G u (L ++ [v]) hUL1) u v).adjB u w = true
      ∧ vEndCount D w = 0)) with
  | false => rfl
  | true =>
    obtain ⟨hadj, hdead⟩ := decide_eq_true_iff.1 hd
    have hw' : (gStar G u L hUL).adjB u w = true := by
      rw [del1_gStar_step G u v hv L hUL hUL1 hvL u w]
      exact hadj
    have halive' := halive w hw'
    omega

/-- **fan7 基例（lane_82 真证）**：k = eDeg G u ≤ 2 时 fan7_use 结论成立。
    k = 0 取 A = []（gStar [] 逐点等同于 delStar，见 gStar_nil_adj）；
    k ∈ {1,2} 取 A = [v]（任取一个星顶点）并用一次 `fan6_use` 朝 u 吸收——
    passing 过滤器由 `fan7_step_dead_zero` 清零（gStar [] 的 u-邻居 = G 的
    非 EV 邻居，全部由 hend 保证活）。k = 2 时 ⌈k/2⌉ = 1：一次吸收即达标。 -/
theorem fan7_use_le_two {n : Nat} (G : Graph n) (u : Fin n)
    (D' : List (List (Fin n))) (hD' : IsDecomp (delStar G u) D')
    (hend : ∀ w : Fin n, G.adjB w u = true → 0 < vEndCount D' w)
    (hk : eDeg G u ≤ 2) :
    ∃ (A : List (Fin n)) (hAsub : ∀ v ∈ A, EVAdj G u v),
      Distinct A ∧ (eDeg G u + 1) / 2 ≤ A.length ∧
      ∃ D₁ : List (List (Fin n)),
        IsDecomp (gStar G u A hAsub) D₁ ∧ D₁.length = D'.length ∧
        vEndCount D₁ u = vEndCount D' u + A.length := by
  rcases Nat.eq_zero_or_pos (eDeg G u) with h0 | h0pos
  · -- k = 0：A = []
    refine ⟨[], ?_, by trivial, ?_, D', ?_, rfl, ?_⟩
    · intro w hw
      exact absurd hw List.not_mem_nil
    · rw [h0]; simp
    · refine decomp_congr (fun x y => ?_) hD'
      show delAdj G u x y = gStarAdj G u ([] : List (Fin n)) x y
      simp [gStarAdj]
    · simp
  · -- k ∈ {1,2}：A = [v]，一次 fan6 吸收
    obtain ⟨v, hv⟩ := exists_EVAdj_of_pos G u (by omega)
    have hvu : G.adjB v u = true := G.symm u v hv.2.1
    have hvpos : 0 < vEndCount D' v := hend v hvu
    have hUL0 : ∀ w ∈ ([] : List (Fin n)), EVAdj G u w :=
      fun w hw => absurd hw List.not_mem_nil
    have hUL1 : ∀ w ∈ ([] : List (Fin n)) ++ [v], EVAdj G u w := by
      intro w hw
      rcases List.mem_append.1 hw with h1' | h2'
      · exact absurd h1' List.not_mem_nil
      · have hwv : w = v := List.mem_singleton.1 h2'
        exact hwv ▸ hv
    have hvL : v ∉ ([] : List (Fin n)) := fun hmem => absurd hmem List.not_mem_nil
    have hEq : ∀ x y : Fin n, (gStar G u ([] : List (Fin n)) hUL0).adjB x y
        = (del1 (gStar G u (([] : List (Fin n)) ++ [v]) hUL1) u v).adjB x y :=
      fun x y => del1_gStar_step G u v hv ([] : List (Fin n)) hUL0 hUL1 hvL x y
    have hD : IsDecomp (del1 (gStar G u (([] : List (Fin n)) ++ [v]) hUL1) u v) D' :=
      decomp_congr (fun x y => (gStar_nil_adj G u x y hUL0).trans (hEq x y)) hD'
    have hzero : ((finList n).filter
        (fun w => decide ((del1 (gStar G u (([] : List (Fin n)) ++ [v]) hUL1) u v).adjB u w
          = true ∧ vEndCount D' w = 0))).length = 0 := by
      refine fan7_step_dead_zero G u v ([] : List (Fin n)) hUL0 hvL hv hUL1 D' ?_ ?_
      · exact decomp_congr (fun x y => gStar_nil_adj G u x y hUL0) hD'
      · intro w hw'
        rw [gStar_adj_u G u ([] : List (Fin n)) hUL0 w] at hw'
        rcases hw' with hm | ⟨hadjG, _⟩
        · exact absurd hm List.not_mem_nil
        · exact hend w (G.symm u w hadjG)
    have hpass : ((finList n).filter
        (fun w => decide ((del1 (gStar G u (([] : List (Fin n)) ++ [v]) hUL1) u v).adjB u w
          = true ∧ vEndCount D' w = 0))).length < vEndCount D' v := by
      rw [hzero]; exact hvpos
    have hmem : v ∈ ([] : List (Fin n)) ++ [v] :=
      List.mem_append.2 (Or.inr (List.mem_singleton.2 rfl))
    have hab : (gStar G u (([] : List (Fin n)) ++ [v]) hUL1).adjB u v = true :=
      (gStar_adj_mem G u (([] : List (Fin n)) ++ [v]) hUL1 hmem).1
    obtain ⟨D₁, hD₁, hlen₁, hu₁, _⟩ :=
      fan6_use (gStar G u (([] : List (Fin n)) ++ [v]) hUL1) u v hab D' hD hpass
    refine ⟨[v], ?_, ?_, ?_, D₁, hD₁, hlen₁, ?_⟩
    · intro w hw
      rcases List.mem_cons.1 hw with h1' | h2'
      · exact h1'.symm ▸ hv
      · exact absurd h2' List.not_mem_nil
    · exact ⟨fun hmem => absurd hmem List.not_mem_nil, by trivial⟩
    · have h3 : eDeg G u + 1 ≤ 3 := by omega
      have hd2 : (eDeg G u + 1) / 2 ≤ 3 / 2 := Nat.div_le_div_right h3
      have h32 : (3 : Nat) / 2 = 1 := rfl
      have hlv : [v].length = 1 := rfl
      omega
    · rw [hu₁]; simp

theorem distinct_append_single {V : Type} : ∀ (l : List V) (a : V),
    Distinct l → a ∉ l → Distinct (l ++ [a])
  | [], a, _, _ => ⟨by simp, True.intro⟩
  | b :: t, a, hd, ha => by
      obtain ⟨hb, hdt⟩ := hd
      show Distinct ((b :: t) ++ [a])
      rw [List.cons_append]
      refine ⟨fun hm => ?_,
        distinct_append_single t a hdt (fun hm => ha (List.mem_cons.2 (Or.inr hm)))⟩
      rcases List.mem_append.1 hm with h1 | h2
      · exact hb h1
      · rcases List.mem_singleton.1 h2 with hc
        exact ha (List.mem_cons.2 (Or.inl hc.symm))

/-- **L-引擎（lane_68 真证）**：剩余星边 T 逐条朝各自星顶点回插。
    对 T 归纳：只要当前分解满足 D(u) ≥ |T| + 2，则 T 的星边可全部朝其
    星顶点回插（fan6 朝 v），条数不变，末态 D(u) ≥ 2。
    每步预算：D(u) ≥ |T| + 2 ≥ 3 > 2 ≥ 死邻居上界（deadCount_gStar_le，
    hlow 的 (A2b) 输入 + (A1) 的星顶点两两不相邻）。
    对应 paper Thm 3.1 Step 4 / lane_31 T31.2 回插段的 L = F ∖ A 循环。 -/
theorem lEngine {n : Nat} (G : Graph n) (u : Fin n)
    (hA1 : A1 G) (hlow : ∀ v : Fin n, EVAdj G u v → eDeg G v ≤ 3) :
    ∀ (T : List (Fin n)), (∀ v ∈ T, EVAdj G u v) → Distinct T →
      ∀ (L₀ : List (Fin n)) (hUL₀ : ∀ v ∈ L₀, EVAdj G u v), Distinct L₀ →
      (∀ v ∈ T, v ∉ L₀) → (hULT : ∀ v ∈ L₀ ++ T, EVAdj G u v) →
      ∀ (D : List (List (Fin n))), IsDecomp (gStar G u L₀ hUL₀) D →
      T.length + 2 ≤ vEndCount D u →
      ∃ D' : List (List (Fin n)),
        IsDecomp (gStar G u (L₀ ++ T) hULT) D' ∧
        D'.length = D.length ∧ 2 ≤ vEndCount D' u := by
  intro T
  induction T with
  | nil =>
      intro _ _ L₀ hUL₀ _ _ hULT D hD hbud
      refine ⟨D, ?_, rfl, hbud⟩
      refine decomp_congr (fun x y => ?_) hD
      show gStarAdj G u L₀ x y = gStarAdj G u (L₀ ++ []) x y
      rw [List.append_nil]
  | cons v T' ih =>
      intro hTsub hTdis L₀ hUL₀ hL₀dis hTL hULT D hD hbud
      have hvT : v ∉ T' := hTdis.1
      have hT'dis : Distinct T' := hTdis.2
      have hvsub : EVAdj G u v := hTsub v (List.mem_cons.2 (Or.inl rfl))
      have hT'sub : ∀ x ∈ T', EVAdj G u x := fun x hx =>
        hTsub x (List.mem_cons.2 (Or.inr hx))
      have hvL : v ∉ L₀ := hTL v (List.mem_cons.2 (Or.inl rfl))
      have hTL' : ∀ x ∈ T', x ∉ L₀ ++ [v] := by
        intro x hx
        have hxL₀ : x ∉ L₀ := hTL x (List.mem_cons.2 (Or.inr hx))
        intro hm
        rcases List.mem_append.1 hm with h1 | h2
        · exact hxL₀ h1
        · have hxe : x = v := List.mem_singleton.1 h2
          exact hvT (hxe ▸ hx)
      have hUL₁ : ∀ x ∈ L₀ ++ [v], EVAdj G u x := by
        intro x hx
        rcases List.mem_append.1 hx with h1 | h2
        · exact hUL₀ x h1
        · have hxe : x = v := List.mem_singleton.1 h2
          rw [hxe]
          exact hvsub
      have hL₁dis : Distinct (L₀ ++ [v]) := distinct_append_single L₀ v hL₀dis hvL
      have hAssoc : (L₀ ++ [v]) ++ T' = L₀ ++ (v :: T') := by
        rw [List.append_assoc]
        rfl
      have hULT' : ∀ w ∈ (L₀ ++ [v]) ++ T', EVAdj G u w := by
        rw [hAssoc]
        exact hULT
      -- 当前图 H₁ = gStar (L₀ ++ [v])，其删 uv 恰为 gStar L₀
      have hEq : ∀ x y : Fin n,
          (gStar G u L₀ hUL₀).adjB x y
            = (del1 (gStar G u (L₀ ++ [v]) hUL₁) u v).adjB x y :=
        fun x y => del1_gStar_step G u v hvsub L₀ hUL₀ hUL₁ hvL x y
      have hD'0 : IsDecomp (del1 (gStar G u (L₀ ++ [v]) hUL₁) v u) D := by
        refine decomp_congr (fun x y => ?_) hD
        rw [del1_swap (gStar G u (L₀ ++ [v]) hUL₁) v u x y]
        exact hEq x y
      have hl : (v :: T').length = T'.length + 1 := rfl
      have hbud3 : 3 ≤ vEndCount D u := by omega
      have hlowv : eDeg G v ≤ 3 := hlow v hvsub
      have hdead := deadCount_gStar_le G u v hA1 hlow L₀ hUL₀ hvsub hvL D hD
        (by omega)
      have hpass : ((finList n).filter
          (fun w => decide ((del1 (gStar G u (L₀ ++ [v]) hUL₁) v u).adjB v w = true
            ∧ vEndCount D w = 0))).length
        < vEndCount D u := by
        rw [filterLensCongr
          (fun w => decide ((del1 (gStar G u (L₀ ++ [v]) hUL₁) v u).adjB v w = true
            ∧ vEndCount D w = 0))
          (fun w => decide ((gStar G u L₀ hUL₀).adjB v w = true ∧ vEndCount D w = 0))
          (fun w => by
            rw [del1_swap (gStar G u (L₀ ++ [v]) hUL₁) v u, hEq v w]) (finList n)]
        omega
      have hMem : v ∈ L₀ ++ [v] := List.mem_append.2 (Or.inr (List.mem_singleton.2 rfl))
      have hab : (gStar G u (L₀ ++ [v]) hUL₁).adjB v u = true :=
        (gStar_adj_mem G u (L₀ ++ [v]) hUL₁ hMem).2
      obtain ⟨D₁, hD₁, hlen₁, _, hub₁⟩ :=
        fan6_use (gStar G u (L₀ ++ [v]) hUL₁) v u hab D hD'0 hpass
      have hbud' : T'.length + 2 ≤ vEndCount D₁ u := by omega
      obtain ⟨D', hD'1, hlen'1, hu'1⟩ :=
        ih hT'sub hT'dis (L₀ ++ [v]) hUL₁ hL₁dis hTL' hULT' D₁ hD₁ hbud'
      refine ⟨D', ?_, hlen'1.trans hlen₁, hu'1⟩
      refine decomp_congr (fun x y => by
        show gStarAdj G u ((L₀ ++ [v]) ++ T') x y = gStarAdj G u (L₀ ++ (v :: T')) x y
        rw [hAssoc]) hD'1

theorem gStar_full {n : Nat} (G : Graph n) (u : Fin n) (M : List (Fin n))
    (hM : ∀ v ∈ M, EVAdj G u v) (hv : ∀ v : Fin n, EVAdj G u v → v ∈ M) :
    ∀ x y : Fin n, (gStar G u M hM).adjB x y = G.adjB x y := by
  intro x y
  by_cases hadj : G.adjB x y = true
  · rw [hadj]
    by_cases hxu : x = u
    · rw [hxu] at hadj ⊢
      rw [gStar_adj_u G u M hM y]
      by_cases hyE : EVAdj G u y
      · exact Or.inl (hv y hyE)
      · exact Or.inr ⟨hadj, hyE⟩
    · by_cases hyu : y = u
      · rw [hyu] at hadj ⊢
        rw [gStar_adj_u' G u M hM x]
        by_cases hxE : EVAdj G u x
        · exact Or.inl (hv x hxE)
        · exact Or.inr ⟨hadj, hxE⟩
      · rw [gStar_adj_true]
        refine Or.inl ((delAdj_true_iff G u x y).2 ⟨hadj, ?_⟩)
        rintro (⟨he, _⟩ | ⟨he, _⟩)
        · exact hxu he
        · exact hyu he
  · rw [Bool.eq_false_iff.2 hadj]
    refine Bool.eq_false_iff.2 (fun hc => hadj ?_)
    rw [gStar_adj_true] at hc
    rcases hc with h | ⟨he, hm⟩ | ⟨he, hm⟩
    · exact (delAdj_true_iff G u x y).1 h |>.1
    · rw [he]
      exact (hM y hm).2.1
    · rw [he]
      exact G.symm u x (hM x hm).2.1

/-! ## lane_86：分块改接 u 端（σ-形式构造 + 计数 + 结构化 fan7）

lane_82 定界的赢法形态（每 D′-块恰一星顶点）的形式化。σ-改接 = 对 D′ 的
每块 P 选取 Option (星顶点 v × 接头标志 b)：b = true 把 u 接到块头
（u :: P，消耗星边 u–v），b = false 接到块尾（P ++ [u]），none 不动。
lane_86 机器底账（lab/fan86/，n ≤ 5 全空间 36,620 实例 + 结构化族）：
σ-构造（匹配口径）在 n=4 覆盖 58/156、n=5 覆盖 14,934/36,620 = 40.8%；
σ-缺口实例上 true_opt 全部仍 ≥ ⌈k/2⌉（C1 0 违反），赢法是"过 u 块拆半 +
星边封桥端 + 缝合合并"的级联重排（lab/fan86/struct_check.py 的
family_t2_f2 实例给出了显式赢法），不属于逐块局部移动——这就是 fan7_use
一般情形剩余缺口的精确形状。本节把**可证部分**全部形式化：
`fan7_reattach`（σ-形式构造引理：IsPathDecomp 保持 + 端点账本）与
`fan7_use_goodForm`（每星顶点都被选中时 fan7_use 结论成立，|A| = k）。 -/

/-- 单块改接：s = some (v, true) 接头，s = some (v, false) 接尾，none 不动。 -/
def attachOne {n : Nat} (u : Fin n) (s : Option (Fin n × Bool)) (P : List (Fin n)) :
    List (Fin n) :=
  match s with
  | some (_, true) => u :: P
  | some (_, false) => P ++ [u]
  | none => P

/-- σ-选取的星顶点像表。 -/
def attachImage {n : Nat} (sel : List (Fin n) → Option (Fin n × Bool))
    (D : List (List (Fin n))) : List (Fin n) :=
  D.filterMap (fun P => (sel P).map Prod.fst)

/-- 全部分解的改接。 -/
def attachAll {n : Nat} (u : Fin n) (sel : List (Fin n) → Option (Fin n × Bool))
    (D : List (List (Fin n))) : List (List (Fin n)) :=
  D.map (fun P => attachOne u (sel P) P)

/-- σ-改接假设包：选中的是星顶点、接头位置（头/尾）、块不含 u、
    不同块选不同星顶点。 -/
structure AttachOK {n : Nat} (G : Graph n) (u : Fin n) (D : List (List (Fin n)))
    (sel : List (Fin n) → Option (Fin n × Bool)) : Prop where
  sel_star : ∀ (P : List (Fin n)) (v : Fin n) (b : Bool),
    sel P = some (v, b) → EVAdj G u v
  sel_head : ∀ (P : List (Fin n)) (v : Fin n),
    sel P = some (v, true) → P.head? = some v ∧ u ∉ P
  sel_tail : ∀ (P : List (Fin n)) (v : Fin n),
    sel P = some (v, false) → lastOf P = some v ∧ u ∉ P
  sel_inj : ∀ P Q : List (Fin n), P ∈ D → Q ∈ D → P ≠ Q →
    sel P = some (v, b) → sel Q = some (w, c) → v ≠ w

/-- AttachOK 对块表的尾部限制。 -/
theorem attachOK_tail {n : Nat} (G : Graph n) (u : Fin n) (P : List (Fin n))
    (D : List (List (Fin n))) (sel : List (Fin n) → Option (Fin n × Bool))
    (hOK : AttachOK G u (P :: D) sel) : AttachOK G u D sel := by
  obtain ⟨h1, h2, h3, h4⟩ := hOK
  exact ⟨h1, h2, h3, fun Q R hQ hR hne hs ht => h4 Q R (List.mem_cons_of_mem _ hQ)
    (List.mem_cons_of_mem _ hR) hne hs ht⟩

/-- EIn 的对称性。 -/
theorem l86EIn_swap {V : Type} : ∀ (P : List V) (x y : V), EIn P x y → EIn P y x
  | [], _, _, h => h.elim
  | [_], _, _, h => h.elim
  | u :: v :: r, x, y, h => by
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | h3
      · exact Or.inr (Or.inl ⟨h1, h2⟩)
      · exact Or.inl ⟨h1, h2⟩
      · exact Or.inr (Or.inr (l86EIn_swap (v :: r) x y h3))

/-- EIn 蕴含两端点都在列表中。 -/
theorem l86EIn_mem_of {V : Type} [DecidableEq V] :
    ∀ (P : List V) (x y : V), EIn P x y → x ∈ P ∧ y ∈ P
  | [], _, _, h => h.elim
  | [_], _, _, h => h.elim
  | u :: v :: r, x, y, h => by
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | h3
      · exact ⟨List.mem_cons.2 (Or.inl h1.symm),
          List.mem_cons_of_mem u (List.mem_cons.2 (Or.inl h2.symm))⟩
      · exact ⟨List.mem_cons_of_mem u (List.mem_cons.2 (Or.inl h2.symm)),
          List.mem_cons.2 (Or.inl h1.symm)⟩
      · obtain ⟨h4, h5⟩ := l86EIn_mem_of (v :: r) x y h3
        exact ⟨List.mem_cons_of_mem _ h4, List.mem_cons_of_mem _ h5⟩

/-- 长度 ≥ 2 的列表有一对相邻元素。 -/
theorem l86exists_EIn_of_len2 {V : Type} : ∀ (P : List V), 2 ≤ P.length →
    ∃ x y : V, EIn P x y
  | [], h => by simp at h
  | [_], h => by simp at h
  | u :: v :: r, _ => ⟨u, v, Or.inl ⟨rfl, rfl⟩⟩

/-- 星边对不出现在 delStar G u 的任何路径中（星边已被删，delAdj 为 false）。 -/
theorem starPair_not_EIn {n : Nat} (G : Graph n) (u v : Fin n) (hv : EVAdj G u v)
    (P : List (Fin n)) (hP : IsPath (GAdj (delStar G u)) P) :
    ¬ EIn P u v := by
  intro he
  have hadj := EIn_adj (delStar G u) P hP u v he
  have hfalse : (delStar G u).adjB u v = false := by
    show delAdj G u u v = false
    unfold delAdj
    rw [decide_eq_true_iff.2 (Or.inl ⟨rfl, hv⟩), Bool.not_true, Bool.and_false]
  rw [hfalse] at hadj
  exact Bool.noConfusion hadj

/-- 路径中有一条避开 u 的边（u 不在路径中时）。 -/
theorem l86exists_EIn_avoid {V : Type} [DecidableEq V] (a : V) :
    ∀ (P : List V), 2 ≤ P.length → a ∉ P → ∃ x y : V, EIn P x y ∧ x ≠ a ∧ y ≠ a := by
  intro P h2 ha
  obtain ⟨x, y, hxy⟩ := l86exists_EIn_of_len2 P h2
  obtain ⟨h4, h5⟩ := l86EIn_mem_of P x y hxy
  exact ⟨x, y, hxy, fun hc => ha (hc ▸ h4), fun hc => ha (hc ▸ h5)⟩

/-- 尾部追加单点的右消去。 -/
theorem l86append_single_cancel {V : Type} [DecidableEq V] :
    ∀ (P Q : List V) (a : V), P ++ [a] = Q ++ [a] → P = Q
  | [], [], _, _ => rfl
  | [], b :: t, a, h => by
      injection h with _ h5
      cases t with
      | nil => exact absurd h5 (by simp)
      | cons c t' => exact absurd h5 (by simp [List.cons_append])
  | a0 :: s, [], a, h => by
      injection h with _ h5
      cases s with
      | nil => exact absurd h5 (by simp)
      | cons c t' => exact absurd h5 (by simp [List.cons_append])
  | a0 :: s, b :: t, a, h => by
      injection h with h4 h5
      rw [h4, l86append_single_cancel s t a h5]

/-- 逐点单射的 map 保持互异。 -/
theorem l86distinct_map_inj' {V W : Type} [DecidableEq V] [DecidableEq W] (f : V → W) :
    ∀ (l : List V), Distinct l → (∀ x y, x ∈ l → y ∈ l → x ≠ y → f x ≠ f y) →
      Distinct (l.map f)
  | [], _, _ => by trivial
  | a :: t, hd, hinj => by
      obtain ⟨hnb, hdt⟩ := hd
      show Distinct (List.map f (a :: t))
      rw [List.map_cons]
      refine ⟨fun hm => ?_, l86distinct_map_inj' f t hdt (fun x y hx hy hne => hinj x y
        (List.mem_cons_of_mem _ hx) (List.mem_cons_of_mem _ hy) hne)⟩
      rcases List.mem_map.1 hm with ⟨b, hb, hfb⟩
      have hba : b = a := Decidable.byContradiction (fun hc =>
        (hinj b a (List.mem_cons_of_mem _ hb)
          (List.mem_cons.2 (Or.inl rfl)) hc) hfb)
      exact hnb (hba ▸ hb)

/-- delStar-链在 gStar 中仍是链（边只增不减）。 -/
theorem l86chain_delStar_gStar {n : Nat} (G : Graph n) (u : Fin n) (P : List (Fin n))
    (hc : Chain (GAdj (delStar G u)) P)
    (L : List (Fin n)) (hUL : ∀ w ∈ L, EVAdj G u w) :
    Chain (GAdj (gStar G u L hUL)) P :=
  chain_mono (GAdj (delStar G u)) (GAdj (gStar G u L hUL)) P hc
    (fun x y hxy => (gStar_adj_true G u L hUL x y).2 (Or.inl hxy))

/-- 接头：u :: P 在 gStar 中是路径（head P = 星顶点 v，u ∉ P）。 -/
theorem l86attachOne_cons_path {n : Nat} (G : Graph n) (u v : Fin n) (hv : EVAdj G u v)
    (P : List (Fin n)) (hPv : P.head? = some v) (hPu : u ∉ P)
    (hpath : IsPath (GAdj (delStar G u)) P)
    {L : List (Fin n)} (hUL : ∀ w ∈ L, EVAdj G u w) (hvL : v ∈ L) :
    IsPath (GAdj (gStar G u L hUL)) (u :: P) := by
  obtain ⟨h2, hdis, hchain⟩ := hpath
  have hPne : P ≠ [] := by
    intro h0
    rw [h0] at hPv
    simp at hPv
  cases P with
  | nil => exact absurd rfl hPne
  | cons r0 r1 =>
    have h0 : r0 = v := by simpa using hPv
    refine ⟨by simp, ⟨hPu, hdis⟩, ?_⟩
    have hc0 : GAdj (gStar G u L hUL) u r0 := by
      rw [h0]
      exact (gStar_adj_mem G u L hUL hvL).1
    exact ⟨hc0, l86chain_delStar_gStar G u (r0 :: r1) hchain L hUL⟩

/-- 接尾：P ++ [u] 在 gStar 中是路径（lastOf P = 星顶点 v，u ∉ P）。 -/
theorem l86attachOne_append_path {n : Nat} (G : Graph n) (u v : Fin n) (hv : EVAdj G u v)
    (P : List (Fin n)) (hPlv : lastOf P = some v) (hPu : u ∉ P)
    (hpath : IsPath (GAdj (delStar G u)) P)
    {L : List (Fin n)} (hUL : ∀ w ∈ L, EVAdj G u w) (hvL : v ∈ L) :
    IsPath (GAdj (gStar G u L hUL)) (P ++ [u]) := by
  obtain ⟨h2, hdis, hchain⟩ := hpath
  have hPne : P ≠ [] := by
    intro h0
    rw [h0] at hPlv
    simp [lastOf] at hPlv
  cases P with
  | nil => exact absurd rfl hPne
  | cons r0 r1 =>
    refine ⟨by simp, distinct_append_single (r0 :: r1) u hdis hPu, ?_⟩
    refine chain_append_single (GAdj (gStar G u L hUL)) (r0 :: r1) u
      (l86chain_delStar_gStar G u (r0 :: r1) hchain L hUL) (fun w hw => ?_)
    have hw' : lastOf (r0 :: r1) = some w := hw
    rw [hPlv] at hw'
    have hwv : w = v := (Option.some.inj hw').symm
    rw [hwv]
    exact (gStar_adj_mem G u L hUL hvL).2

/-- attachOne 保持块内已用的边。 -/
theorem l86attachOne_EIn_mono {n : Nat} (u : Fin n) (s : Option (Fin n × Bool)) :
    ∀ (P : List (Fin n)) (x y : Fin n), EIn P x y → EIn (attachOne u s P) x y := by
  intro P x y h
  cases s with
  | none => exact h
  | some p =>
    cases p with
    | mk v b =>
      cases b with
      | true => exact EIn_cons_prefix P x y h
      | false => exact EIn_append_suffix P x y h

/-- 接头新增的星边：EIn (u :: P) u v。 -/
theorem l86attachOne_starEdge_head {n : Nat} (u v : Fin n) (P : List (Fin n))
    (hPv : P.head? = some v) : EIn (u :: P) u v := by
  cases P with
  | nil => simp at hPv
  | cons r0 r1 =>
    have h0 : r0 = v := by simpa using hPv
    show (u = u ∧ r0 = v) ∨ (u = v ∧ r0 = u) ∨ EIn (r0 :: r1) u v
    exact Or.inl ⟨rfl, h0⟩

/-- 接尾新增的星边：EIn (P ++ [u]) u v。 -/
theorem l86attachOne_starEdge_tail {n : Nat} (u v : Fin n) (P : List (Fin n))
    (hPlv : lastOf P = some v) : EIn (P ++ [u]) u v :=
  l86EIn_swap (P ++ [u]) v u (EIn_append_last P u v hPlv)

/-- 账本位：改接后 u 的端点位 = 原位 + 是否改接。 -/
theorem l86vEndBit_attachOne_u {n : Nat} (u : Fin n) (s : Option (Fin n × Bool))
    (P : List (Fin n))
    (hsu : ∀ v : Fin n, ∀ b : Bool, s = some (v, b) → u ∉ P)
    (hsne : s ≠ none → P ≠ []) :
    vEndBit u (attachOne u s P) = vEndBit u P + (if s = none then 0 else 1) := by
  cases s with
  | none => rfl
  | some p =>
    cases p with
    | mk v b =>
      have hne : (some (v, b) : Option (Fin n × Bool)) ≠ none := by simp
      have hPne : P ≠ [] := hsne hne
      have hup : u ∉ P := hsu v b rfl
      rw [if_neg hne]
      cases b with
      | true =>
        show vEndBit u (u :: P) = vEndBit u P + 1
        rw [vEndBit_cons_self, vEndBit_not_mem P hup]
      | false =>
        show vEndBit u (P ++ [u]) = vEndBit u P + 1
        rw [vEndBit_append_self u P hPne, vEndBit_not_mem P hup]

/-- 逐对单射：不同块改接后仍不同（关键：星边对不出现在 delStar-路径中）。 -/
theorem l86attachOne_inj {n : Nat} (G : Graph n) (u : Fin n)
    (D : List (List (Fin n))) (hD : IsDecomp (delStar G u) D)
    (sel : List (Fin n) → Option (Fin n × Bool)) (hOK : AttachOK G u D sel) :
    ∀ P Q : List (Fin n), P ∈ D → Q ∈ D → P ≠ Q →
      attachOne u (sel P) P ≠ attachOne u (sel Q) Q := by
  intro P Q hP hQ hPQ heq
  obtain ⟨⟨hpaths, hcover, hdisj⟩, hdist⟩ := hD
  obtain ⟨h1, h2, h3, h4⟩ := hOK
  have hp2 : 2 ≤ P.length := (hpaths P hP).1
  have hq2 : 2 ≤ Q.length := (hpaths Q hQ).1
  cases hsp : sel P with
  | none =>
    cases hsq : sel Q with
    | none =>
      rw [hsp, hsq] at heq
      simp only [attachOne] at heq
      exact hPQ heq
    | some sq =>
      obtain ⟨w, c⟩ := sq
      cases c with
      | true =>
        rw [hsp, hsq] at heq
        simp only [attachOne] at heq
        obtain ⟨x, y, hxy⟩ := l86exists_EIn_of_len2 Q hq2
        have hPxy : EIn P x y := by rw [heq]; exact EIn_cons_prefix Q x y hxy
        exact hdisj P hP Q hQ hPQ x y ⟨hPxy, hxy⟩
      | false =>
        rw [hsp, hsq] at heq
        simp only [attachOne] at heq
        obtain ⟨x, y, hxy⟩ := l86exists_EIn_of_len2 Q hq2
        have hPxy : EIn P x y := by rw [heq]; exact EIn_append_suffix Q x y hxy
        exact hdisj P hP Q hQ hPQ x y ⟨hPxy, hxy⟩
  | some sp =>
    obtain ⟨v, b⟩ := sp
    have hPu : u ∉ P := by
      cases b with
      | true => exact (h2 P v hsp).2
      | false => exact (h3 P v hsp).2
    cases hsq : sel Q with
    | none =>
      rw [hsp, hsq] at heq
      simp only [attachOne] at heq
      obtain ⟨x, y, hxy⟩ := l86exists_EIn_of_len2 P hp2
      have hQxy : EIn Q x y := by
        rw [← heq]
        exact l86attachOne_EIn_mono u (some (v, b)) P x y hxy
      exact hdisj P hP Q hQ hPQ x y ⟨hxy, hQxy⟩
    | some sq =>
      obtain ⟨w, c⟩ := sq
      have hQu : u ∉ Q := by
        cases c with
        | true => exact (h2 Q w hsq).2
        | false => exact (h3 Q w hsq).2
      rw [hsp, hsq] at heq
      cases b with
      | true =>
        cases c with
        | true =>
          simp only [attachOne] at heq
          exact hPQ (List.cons.inj heq).2
        | false =>
          simp only [attachOne] at heq
          obtain ⟨x, y, hxy, hxu, hyu⟩ := l86exists_EIn_avoid u P hp2 hPu
          have h1' : EIn (u :: P) x y := EIn_cons_prefix P x y hxy
          rw [heq] at h1'
          rcases EIn_append_inv Q x y h1' with hE | ⟨e1, e2⟩ | ⟨e1, e2⟩
          · exact hdisj P hP Q hQ hPQ x y ⟨hxy, hE⟩
          · exact hxu e1
          · exact hyu e1
      | false =>
        cases c with
        | true =>
          simp only [attachOne] at heq
          obtain ⟨x, y, hxy, hxu, hyu⟩ := l86exists_EIn_avoid u Q hq2 hQu
          have h1' : EIn (u :: Q) x y := EIn_cons_prefix Q x y hxy
          rw [← heq] at h1'
          rcases EIn_append_inv P x y h1' with hE | ⟨e1, e2⟩ | ⟨e1, e2⟩
          · exact hdisj P hP Q hQ hPQ x y ⟨hE, hxy⟩
          · exact hxu e1
          · exact hyu e1
        | false =>
          simp only [attachOne] at heq
          exact hPQ (l86append_single_cancel P Q u heq)


/-- filterMap 成员刻画（自包含版）。 -/
theorem l86mem_filterMap {V W : Type} [DecidableEq V] (f : V → Option W) :
    ∀ (l : List V) (b : W), b ∈ List.filterMap f l ↔ ∃ a ∈ l, f a = some b
  | [], b => by simp
  | a :: t, b => by
      rw [List.filterMap_cons]
      cases hf : f a with
      | none =>
        simp only []
        constructor
        · intro h
          obtain ⟨c, hc, hcb⟩ := (l86mem_filterMap f t b).1 h
          exact ⟨c, List.mem_cons.2 (Or.inr hc), hcb⟩
        · rintro ⟨c, hc, hcb⟩
          rcases List.mem_cons.1 hc with h0 | h0
          · rw [h0, hf] at hcb
            exact absurd hcb (by simp)
          · exact (l86mem_filterMap f t b).2 ⟨c, h0, hcb⟩
      | some d =>
        simp only []
        constructor
        · intro h
          rcases List.mem_cons.1 h with h0 | h0
          · exact ⟨a, List.mem_cons.2 (Or.inl rfl), by rw [hf, h0]⟩
          · obtain ⟨c, hc, hcb⟩ := (l86mem_filterMap f t b).1 h0
            exact ⟨c, List.mem_cons.2 (Or.inr hc), hcb⟩
        · rintro ⟨c, hc, hcb⟩
          rcases List.mem_cons.1 hc with h0 | h0
          · have hbd : b = d := by
              rw [h0] at hcb
              rw [hf] at hcb
              exact (Option.some.inj hcb).symm
            exact List.mem_cons.2 (Or.inl hbd)
          · exact List.mem_cons_of_mem _ ((l86mem_filterMap f t b).2 ⟨c, h0, hcb⟩)

/-- Option.map Prod.fst = some v ⟺ 选中 v。 -/
theorem l86optionMap_fst_eq {n : Nat} (sel : List (Fin n) → Option (Fin n × Bool))
    (P : List (Fin n)) (v : Fin n) :
    (sel P).map Prod.fst = some v ↔ ∃ b : Bool, sel P = some (v, b) := by
  cases hs : sel P with
  | none => simp
  | some p =>
    obtain ⟨w, b⟩ := p
    simp only [hs, Option.map_some, Option.some.injEq, Prod.mk.injEq]
    constructor
    · intro h
      exact ⟨b, h, rfl⟩
    · rintro ⟨b', h1, h2⟩
      exact h1

theorem l86mem_attachImage {n : Nat} (sel : List (Fin n) → Option (Fin n × Bool)) :
    ∀ (D : List (List (Fin n))) (v : Fin n), v ∈ attachImage sel D ↔
      ∃ (P : List (Fin n)), P ∈ D ∧ ∃ b : Bool, sel P = some (v, b) := by
  intro D v
  induction D with
  | nil => simp [attachImage]
  | cons P t ih =>
    -- lane_87b 修复：原稿 `rw [attachImage, l86mem_filterMap]` 后匿名构造器
    -- 形状不匹配（lane_86 在途态遗留）。改用 Iff.rfl 过渡 + 逐分支构造。
    have h1 : v ∈ attachImage sel (P :: t) ↔
        v ∈ List.filterMap (fun Q => (sel Q).map Prod.fst) (P :: t) := Iff.rfl
    rw [h1, l86mem_filterMap]
    constructor
    · rintro ⟨Q, hQ, hQv⟩
      rcases List.mem_cons.1 hQ with h0 | h0
      · obtain ⟨b, hb⟩ := (l86optionMap_fst_eq sel Q v).1 hQv
        refine ⟨P, List.mem_cons.2 (Or.inl rfl), b, ?_⟩
        rw [← h0]
        exact hb
      · obtain ⟨Q2, hQ2, b, hb⟩ := ih.1
          ((l86mem_filterMap (fun Q => (sel Q).map Prod.fst) t v).2 ⟨Q, h0, hQv⟩)
        exact ⟨Q2, List.mem_cons.2 (Or.inr hQ2), b, hb⟩
    · rintro ⟨Q, hQ, hQv⟩
      rcases List.mem_cons.1 hQ with h0 | h0
      · exact ⟨Q, List.mem_cons.2 (Or.inl h0), (l86optionMap_fst_eq sel Q v).2 hQv⟩
      · exact ⟨Q, List.mem_cons.2 (Or.inr h0),
          (l86optionMap_fst_eq sel Q v).2 hQv⟩

/-- attachAll 的每块都是 gStar-路径。 -/
theorem l86attachAll_paths {n : Nat} (G : Graph n) (u : Fin n) (D : List (List (Fin n)))
    (hD : IsDecomp (delStar G u) D)
    (sel : List (Fin n) → Option (Fin n × Bool)) (hOK : AttachOK G u D sel)
    (hUL : ∀ w ∈ attachImage sel D, EVAdj G u w) :
    ∀ P' ∈ attachAll u sel D, IsPath (GAdj (gStar G u (attachImage sel D) hUL)) P' := by
  intro P' hP'
  rcases List.mem_map.1 hP' with ⟨P, hP, hPeq⟩
  rw [← hPeq]
  cases hb : sel P with
  | none =>
    simp only [attachOne]
    have hpp := hD.1.1 P hP
    exact ⟨hpp.1, hpp.2.1, l86chain_delStar_gStar G u P hpp.2.2 (attachImage sel D) hUL⟩
  | some sp =>
    obtain ⟨v, b⟩ := sp
    have hvEV : EVAdj G u v := hOK.1 P v b hb
    have hvL : v ∈ attachImage sel D := by
      rw [l86mem_attachImage]
      exact ⟨P, hP, b, hb⟩
    cases b with
    | true =>
      simp only [attachOne]
      exact l86attachOne_cons_path G u v hvEV P (hOK.2 P v hb).1 (hOK.2 P v hb).2
        (hD.1.1 P hP) hUL hvL
    | false =>
      simp only [attachOne]
      exact l86attachOne_append_path G u v hvEV P (hOK.3 P v hb).1
        (hOK.3 P v hb).2 (hD.1.1 P hP) hUL hvL

/-- attachAll 覆盖 gStar（G̃-边经 D 的覆盖者；星边经被选中的块）。 -/
theorem l86attachAll_cover {n : Nat} (G : Graph n) (u : Fin n) (D : List (List (Fin n)))
    (hD : IsDecomp (delStar G u) D)
    (sel : List (Fin n) → Option (Fin n × Bool)) (hOK : AttachOK G u D sel)
    (hUL : ∀ w ∈ attachImage sel D, EVAdj G u w) :
    IsCover (GAdj (gStar G u (attachImage sel D) hUL)) (attachAll u sel D) := by
  intro x y hxy
  have hxy' : (gStar G u (attachImage sel D) hUL).adjB x y = true := hxy
  rw [gStar_adj_true] at hxy'
  rcases hxy' with hd | ⟨hxu, hvL⟩ | ⟨hyu, hvL⟩
  · obtain ⟨Q, hQ, hQxy⟩ := hD.1.2.1 x y hd
    exact ⟨attachOne u (sel Q) Q, List.mem_map.2 ⟨Q, hQ, rfl⟩,
      l86attachOne_EIn_mono u (sel Q) Q x y hQxy⟩
  · -- 星边 u–y（lane_87b 修复：原稿 `subst hxu` 消去了 u，致后续 `u :: P`
    -- 成未知标识符；改在目标中改写 x → u，不替换变元；mem_map 的相等性
    -- 用 hb 改写 attachOne）
    obtain ⟨P, hP, b, hb⟩ := (l86mem_attachImage sel D y).1 hvL
    cases b with
    | true =>
      refine ⟨u :: P, List.mem_map.2 ⟨P, hP, by rw [hb]; rfl⟩, ?_⟩
      rw [hxu]
      exact l86attachOne_starEdge_head u y P (hOK.2 P y hb).1
    | false =>
      refine ⟨P ++ [u], List.mem_map.2 ⟨P, hP, by rw [hb]; rfl⟩, ?_⟩
      rw [hxu]
      exact l86attachOne_starEdge_tail u y P (hOK.3 P y hb).1
  · -- 星边 x–u（同上修复：改写 y → u，不 subst）
    obtain ⟨P, hP, b, hb⟩ := (l86mem_attachImage sel D x).1 hvL
    cases b with
    | true =>
      refine ⟨u :: P, List.mem_map.2 ⟨P, hP, by rw [hb]; rfl⟩, ?_⟩
      rw [hyu]
      exact l86EIn_swap (u :: P) u x (l86attachOne_starEdge_head u x P (hOK.2 P x hb).1)
    | false =>
      refine ⟨P ++ [u], List.mem_map.2 ⟨P, hP, by rw [hb]; rfl⟩, ?_⟩
      rw [hyu]
      exact l86EIn_swap (P ++ [u]) u x (l86attachOne_starEdge_tail u x P (hOK.3 P x hb).1)

/-- 改接单块的边反演（lane_87b）：改接路径中的边要么是原块 G̃-边，要么是
    新增星边 u–w（w = sel 选中的星顶点，且由 sel_head/sel_tail 知
    w = head/tail）。反演结果以"sel R = some (端点, b)"形式给出，供
    sel_inj 排除双星边情形。 -/
theorem l86attachOne_edge_inv {n : Nat} (G : Graph n) (u : Fin n)
    (D : List (List (Fin n))) (hD : IsDecomp (delStar G u) D)
    (sel : List (Fin n) → Option (Fin n × Bool)) (hOK : AttachOK G u D sel)
    (R : List (Fin n)) (hR : R ∈ D) (x y : Fin n)
    (h : EIn (attachOne u (sel R) R) x y) :
    EIn R x y ∨ (x = u ∧ ∃ b, sel R = some (y, b)) ∨ (y = u ∧ ∃ b, sel R = some (x, b)) := by
  cases hs : sel R with
  | none =>
    rw [hs] at h
    simp only [attachOne] at h
    exact Or.inl h
  | some p =>
    obtain ⟨w, b⟩ := p
    have hsw : sel R = some (w, b) := hs
    cases b with
    | true =>
      rw [hs] at h
      simp only [attachOne] at h
      have hhead : R.head? = some w := (hOK.2 R w hsw).1
      rcases EIn_cons_inv R h with ⟨e1, e2⟩ | ⟨e1, e2⟩ | h'
      · refine Or.inr (Or.inl ⟨e1.symm, true, ?_⟩)
        have hyw : y = w := Option.some.inj (e2.symm.trans hhead)
        rw [hyw]
      · refine Or.inr (Or.inr ⟨e1.symm, true, ?_⟩)
        have hxw : x = w := Option.some.inj (e2.symm.trans hhead)
        rw [hxw]
      · exact Or.inl h'
    | false =>
      rw [hs] at h
      simp only [attachOne] at h
      have hlast : lastOf R = some w := (hOK.3 R w hsw).1
      rcases EIn_append_inv R x y h with h' | ⟨e1, e2⟩ | ⟨e1, e2⟩
      · exact Or.inl h'
      · refine Or.inr (Or.inl ⟨e1, false, ?_⟩)
        have hyw : y = w := Option.some.inj (e2.symm.trans hlast)
        rw [hyw]
      · refine Or.inr (Or.inr ⟨e1, false, ?_⟩)
        have hxw : x = w := Option.some.inj (e2.symm.trans hlast)
        rw [hxw]

/-- attachAll 两两边不交（lane_87b 重写：原稿误用 `l86attachOne_inj` 的
    签名——其结论是表不等而非边不交，且 IsEdgeDisjoint 展开后只有一层
    合取。证明：改接路径的边 = 原块 G̃-边 ∪ 单条新增星边 u–w。两侧共享
    边 (x, y) 时：两侧都是 G̃-边 ⟹ hD 边不交矛盾；恰一侧是星边 ⟹ 另一
    侧的 G̃-路径含星边对，starPair_not_EIn 矛盾；两侧都是星边 ⟹ 同一星
    顶点被两个不同块选中，sel_inj 矛盾。 -/
theorem l86attachAll_disjoint {n : Nat} (G : Graph n) (u : Fin n)
    (D : List (List (Fin n))) (hD : IsDecomp (delStar G u) D)
    (sel : List (Fin n) → Option (Fin n × Bool)) (hOK : AttachOK G u D sel) :
    IsEdgeDisjoint (attachAll u sel D) := by
  intro A hA B hB hAB x y hE
  obtain ⟨hAx, hBx⟩ := hE
  rcases List.mem_map.1 hA with ⟨P, hP, hAeq⟩
  rcases List.mem_map.1 hB with ⟨Q, hQ, hBeq⟩
  rw [← hAeq] at hAx
  rw [← hBeq] at hBx
  have hne : P ≠ Q := by
    intro he
    apply hAB
    rw [← hAeq, ← hBeq, he]
  rcases l86attachOne_edge_inv G u D hD sel hOK P hP x y hAx with hP' | ⟨hxP, vP, hbP⟩ |
    ⟨hyP, vP, hbP⟩
  · rcases l86attachOne_edge_inv G u D hD sel hOK Q hQ x y hBx with hQ1 |
      ⟨hxQ, vQ, hbQ⟩ | ⟨hyQ, vQ, hbQ⟩
    · -- 两侧都是 G̃-边：hD 的边不交
      exact hD.1.2.2 P hP Q hQ hne x y ⟨hP', hQ1⟩
    · -- Q 侧是星边 u–y ⟹ P（G̃-路径）含星边对 u–y，矛盾
      have hEV : EVAdj G u y := hOK.1 Q y vQ hbQ
      have hspe := starPair_not_EIn G u y hEV P (hD.1.1 P hP)
      simp only [hxQ] at hP'
      exact hspe hP'
    · -- Q 侧是星边 x–u ⟹ P 含星边对 x–u，矛盾
      have hEV : EVAdj G u x := hOK.1 Q x vQ hbQ
      have hspe := starPair_not_EIn G u x hEV P (hD.1.1 P hP)
      simp only [hyQ] at hP'
      exact hspe (l86EIn_swap P x u hP')
  · -- P 侧是星边 u–y（x = u、sel P = some (y, b)）
    rcases l86attachOne_edge_inv G u D hD sel hOK Q hQ x y hBx with hQ2 |
      ⟨hxQ, vQ, hbQ⟩ | ⟨hyQ, vQ, hbQ⟩
    · -- Q 含 G̃-边 u–y ⟹ Q 含星边对，矛盾
      have hEV : EVAdj G u y := hOK.1 P y vP hbP
      have hspe := starPair_not_EIn G u y hEV Q (hD.1.1 Q hQ)
      simp only [hxP] at hQ2
      exact hspe hQ2
    · -- 双侧星边都是 u–y：同一星顶点 y 被两个不同块选中
      exact absurd rfl (hOK.4 P Q hP hQ hne hbP hbQ)
    · -- P 侧 x = u、Q 侧 y = u：sel P 选 y = u，与 EVAdj 的 u ≠ y 矛盾
      have hEV : EVAdj G u y := hOK.1 P y vP hbP
      exact hEV.1 hyQ.symm
  · -- P 侧是星边 x–u（y = u、sel P = some (x, b)）
    rcases l86attachOne_edge_inv G u D hD sel hOK Q hQ x y hBx with hQ' |
      ⟨hxQ, vQ, hbQ⟩ | ⟨hyQ, vQ, hbQ⟩
    · -- Q 含 G̃-边 x–u ⟹ Q 含星边对，矛盾
      have hEV : EVAdj G u x := hOK.1 P x vP hbP
      have hspe := starPair_not_EIn G u x hEV Q (hD.1.1 Q hQ)
      simp only [hyP] at hQ'
      exact hspe (l86EIn_swap Q x u hQ')
    · -- P 侧 y = u、Q 侧 x = u：sel Q 选的星顶点是 y = u，与 EVAdj 的 u ≠ y 矛盾
      have hEV : EVAdj G u y := hOK.1 Q y vQ hbQ
      exact hEV.1 hyP.symm
    · -- 双侧星边都是 x–u：同一星顶点 x 被两个不同块选中
      exact absurd rfl (hOK.4 P Q hP hQ hne hbP hbQ)

/-- attachAll 互异（作为路径表；lane_87b 修复——原稿给
    `l86distinct_map_inj'` 的函数参数带了多余的占位下划线，且
    `l86attachOne_inj` 的结论本就是表不等，直接投喂即可）。 -/
theorem l86attachAll_distinct {n : Nat} (G : Graph n) (u : Fin n)
    (D : List (List (Fin n))) (hD : IsDecomp (delStar G u) D)
    (sel : List (Fin n) → Option (Fin n × Bool)) (hOK : AttachOK G u D sel) :
    Distinct (attachAll u sel D) :=
  l86distinct_map_inj' (fun P => attachOne u (sel P) P) D hD.2
    (fun P Q hP hQ hne => l86attachOne_inj G u D hD sel hOK P Q hP hQ hne)

/-- 端点账本：改接后 D₁(u) = D(u) + 被选块数 = D(u) + |A|（lane_87b 修复：
    原稿漏掉 G 参数且 rw 定义名不可用，改为 show 定义展开 + cases 重写）。 -/
theorem l86attachAll_uEnd {n : Nat} (G : Graph n) (u : Fin n)
    (sel : List (Fin n) → Option (Fin n × Bool)) (D : List (List (Fin n)))
    (hOK : AttachOK G u D sel) :
    vEndCount (attachAll u sel D) u = vEndCount D u + (attachImage sel D).length := by
  induction D with
  | nil => simp [attachAll, attachImage, vEndCount]
  | cons P t ih =>
    have hsu : ∀ v : Fin n, ∀ b : Bool, sel P = some (v, b) → u ∉ P := by
      intro v b hs
      cases b with
      | true => exact (hOK.2 P v hs).2
      | false => exact (hOK.3 P v hs).2
    have hsne : sel P ≠ none → P ≠ [] := by
      intro hne h0
      rw [h0] at hne
      cases hs : sel [] with
      | none => exact absurd hs hne
      | some q =>
        obtain ⟨v, b⟩ := q
        cases b with
        | true => exact absurd (hOK.2 [] v hs).1 (by simp)
        | false => exact absurd (hOK.3 [] v hs).1 (by simp [lastOf])
    have hbit := l86vEndBit_attachOne_u u (sel P) P hsu hsne
    have ihOK := attachOK_tail G u P t sel hOK
    show vEndBit u (attachOne u (sel P) P) + vEndCount (attachAll u sel t) u
      = vEndBit u P + vEndCount t u
        + (List.filterMap (fun Q => Option.map Prod.fst (sel Q)) (P :: t)).length
    rw [hbit, ih ihOK, List.filterMap_cons]
    cases hs : sel P with
    | none => simp [attachImage]; omega
    | some p =>
      obtain ⟨v, b⟩ := p
      simp only [Option.map_some, List.length_cons,
        if_neg (by simp : ¬((some (v, b) : Option (Fin n × Bool)) = none)), attachImage]
      omega

/-- 像中星顶点的合法性。 -/
theorem l86attachImage_star {n : Nat} (G : Graph n) (u : Fin n)
    (D : List (List (Fin n)))
    (sel : List (Fin n) → Option (Fin n × Bool)) (hOK : AttachOK G u D sel) :
    ∀ v ∈ attachImage sel D, EVAdj G u v := by
  intro v hv
  obtain ⟨P, hP, b, hb⟩ := (l86mem_attachImage sel D v).1 hv
  exact hOK.1 P v b hb

/-- 像的互异性（sel_inj：不同块选不同星顶点）。lane_87b 修复：对 D 的
    归纳只需 Distinct D——IsDecomp 不遗传给尾表（P 可能独占覆盖某些边），
    且原稿的 ih 调用漏了被 induction 回退的 hD 参数。 -/
theorem l86attachImage_distinct {n : Nat} (G : Graph n) (u : Fin n)
    (D : List (List (Fin n))) (hD : IsDecomp (delStar G u) D)
    (sel : List (Fin n) → Option (Fin n × Bool)) (hOK : AttachOK G u D sel) :
    Distinct (attachImage sel D) := by
  -- lane_87b 修复：归纳需携带"E 的块都在 D 中"（sel_inj 的成员前提），
  -- 且 Distinct-cons 的第一分量是"v 不在尾表"（非整个 cons）。
  have key : ∀ (E : List (List (Fin n))), Distinct E →
      (∀ X ∈ E, X ∈ D) → Distinct (attachImage sel E) := by
    intro E
    induction E with
    | nil => intro _ _; trivial
    | cons P t ih =>
      intro hdis hsub
      obtain ⟨hPne, hdt⟩ := hdis
      have hsubT : ∀ X ∈ t, X ∈ D := fun X hX => hsub X (List.mem_cons_of_mem _ hX)
      show Distinct (List.filterMap (fun Q => Option.map Prod.fst (sel Q)) (P :: t))
      rw [List.filterMap_cons]
      cases hs : sel P with
      | none =>
        simp only [Option.map_none]
        exact ih hdt hsubT
      | some p =>
        obtain ⟨v, b⟩ := p
        simp only [Option.map_some]
        have htail : v ∉ List.filterMap (fun Q => Option.map Prod.fst (sel Q)) t := by
          intro hm
          have hm2 : v ∈ attachImage sel t := hm
          rw [l86mem_attachImage] at hm2
          obtain ⟨Q, hQ, b', hb'⟩ := hm2
          rcases Decidable.em (P = Q) with he | hne
          · exact hPne (he ▸ hQ)
          · exact absurd rfl (hOK.4 P Q (hsub P (List.mem_cons.2 (Or.inl rfl)))
              (hsub Q (List.mem_cons_of_mem _ hQ)) hne hs hb')
        exact ⟨htail, ih hdt hsubT⟩
  exact key D hD.2 (fun X hX => hX)

/-- **σ-形式分块改接构造引理（lane_86 主件）**：D′ 分解 G̃ = delStar G u，
    sel 满足 AttachOK（选中星顶点、端点位置、块不含 u、不同块不同星顶点），
    则改接后的 attachAll u sel D 分解 gStar G u (attachImage sel D)，
    条数不变，u 的端点数恰增 |A|。这就是 lane_82 赢法形态（每块恰一星顶点、
    改接 u 端）的可证化：逐块 prepend/append 一次性全局完成，无 killed 堵塞。 -/
theorem fan7_reattach {n : Nat} (G : Graph n) (u : Fin n)
    (D : List (List (Fin n))) (hD : IsDecomp (delStar G u) D)
    (sel : List (Fin n) → Option (Fin n × Bool)) (hOK : AttachOK G u D sel) :
    ∃ (A : List (Fin n)) (hAsub : ∀ v ∈ A, EVAdj G u v),
      Distinct A ∧
      IsDecomp (gStar G u A hAsub) (attachAll u sel D) ∧
      (attachAll u sel D).length = D.length ∧
      vEndCount (attachAll u sel D) u = vEndCount D u + A.length := by
  refine ⟨attachImage sel D, l86attachImage_star G u D sel hOK,
    l86attachImage_distinct G u D hD sel hOK, ⟨⟨?_, ?_, ?_⟩, ?_⟩, ?_, ?_⟩
  · -- lane_87b 修复：hUL 显式取 l86attachImage_star（原稿 `fun w hw => hw`
    -- 类型不合），并把 IsDecomp 的两层合取花括号配平
    exact l86attachAll_paths G u D hD sel hOK (l86attachImage_star G u D sel hOK)
  · exact l86attachAll_cover G u D hD sel hOK (l86attachImage_star G u D sel hOK)
  · exact l86attachAll_disjoint G u D hD sel hOK
  · exact l86attachAll_distinct G u D hD sel hOK
  · exact List.length_map _
  · exact l86attachAll_uEnd G u sel D hOK

/-- **结构化 fan7（lane_86 组装件）**：在 σ-形式上再设 hFull（每个星顶点
    都被选中），则 |A| = k = eDeg G u ≥ ⌈k/2⌉，fan7_use 的结论成立。
    一般 fan7_use 与本件的差距 = 从 hend 构造出满足 hFull 的 sel——
    机器底账（lab/fan86/）表明这一步在 σ-逐块构造下不可行（n=5 覆盖率
    40.8%），缺口是"过 u 块拆半 + 缝合"的级联重排。 -/
theorem fan7_use_goodForm {n : Nat} (G : Graph n) (u : Fin n)
    (D : List (List (Fin n))) (hD : IsDecomp (delStar G u) D)
    (sel : List (Fin n) → Option (Fin n × Bool)) (hOK : AttachOK G u D sel)
    (hFull : ∀ v : Fin n, EVAdj G u v → v ∈ attachImage sel D) :
    ∃ (A : List (Fin n)) (hAsub : ∀ v ∈ A, EVAdj G u v),
      Distinct A ∧ (eDeg G u + 1) / 2 ≤ A.length ∧
      ∃ D₁ : List (List (Fin n)),
        IsDecomp (gStar G u A hAsub) D₁ ∧ D₁.length = D.length ∧
        vEndCount D₁ u = vEndCount D u + A.length := by
  -- lane_87b 修复：A 显式取 attachImage sel D（原稿经 obtain 得到的 A 是
  -- 不透明变元，无法用 hFull 对其计数）
  have hAstar : ∀ v ∈ attachImage sel D, EVAdj G u v :=
    l86attachImage_star G u D sel hOK
  have hAdis : Distinct (attachImage sel D) :=
    l86attachImage_distinct G u D hD sel hOK
  have hD₁ : IsDecomp (gStar G u (attachImage sel D) hAstar) (attachAll u sel D) :=
    ⟨⟨l86attachAll_paths G u D hD sel hOK hAstar,
      l86attachAll_cover G u D hD sel hOK hAstar,
      l86attachAll_disjoint G u D hD sel hOK⟩,
      l86attachAll_distinct G u D hD sel hOK⟩
  have hlen : (attachAll u sel D).length = D.length := List.length_map _
  have hledger : vEndCount (attachAll u sel D) u
      = vEndCount D u + (attachImage sel D).length :=
    l86attachAll_uEnd G u sel D hOK
  refine ⟨attachImage sel D, hAstar, hAdis, ?_, attachAll u sel D, hD₁, hlen, hledger⟩
  -- |A| = k：starList ⊆ A（hFull）且 A ⊆ starList（像中皆星顶点）
  have hsub1 : ∀ v ∈ starList G u, v ∈ attachImage sel D := fun v hv =>
    hFull v ((starList_spec G u v).1 hv)
  have hsub2 : ∀ v ∈ attachImage sel D, v ∈ starList G u := fun v hv =>
    (starList_spec G u v).2 (hAstar v hv)
  have hk1 : (starList G u).length ≤ (attachImage sel D).length :=
    pigeon (starList G u) (attachImage sel D) (starList_distinct G u) hsub1
  have hk2 : (attachImage sel D).length ≤ (starList G u).length :=
    pigeon (attachImage sel D) (starList G u) hAdis hsub2
  have hkeq : (starList G u).length = eDeg G u := rfl
  -- (k+1)/2 ≤ k
  have hdm := Nat.div_add_mod (eDeg G u + 1) 2
  have hmlt : (eDeg G u + 1) % 2 < 2 := Nat.mod_lt _ (by omega)
  omega

/-! ## lane_87b：干净匹配计数 + fan7_use 组装（分块改接路线收口）

机器底账（lab/fan87/exp_fan7_route.py，n=4/5 全空间 + n=6 k≥3 剪枝，
2,369,096 实例）：R1（无脏星顶点 ⟹ 纯改接匹配已达 ⌈k/2⌉）、R2（改接缺口
⟹ 必有脏星顶点）、R3（改接 + W/R + 头合并 + 首边翻转贪心全达标）。
本节把 R1 侧完整 Lean 化，并把 `fan7_use` 组装为"全清洁支（真证）∨
脏星支（唯一残余 sorry）"。 -/

/-- 非空列表有末元素（lane_87b）。 -/
theorem lastOf_some_of_ne_nil {V : Type} : ∀ (P : List V), P ≠ [] → ∃ c, lastOf P = some c
  | [], h => absurd rfl h
  | [a], _ => ⟨a, rfl⟩
  | _ :: b :: r, _ => lastOf_some_of_ne_nil (b :: r) (by cases r <;> simp)

/-- 端点判定（Bool 版；`isEnd` 的 decide 镜像，lane_87b）。 -/
def isEndB {V : Type} [DecidableEq V] (v : V) (P : List V) : Bool :=
  decide (P.head? = some v ∨ lastOf P = some v)

/-- map 保持互异 ⟹ map 函数在表上单射（lane_87b）。 -/
theorem distinctMapInjOn {V W : Type} (f : V → W) :
    ∀ (l : List V), Distinct (l.map f) →
      ∀ x y : V, x ∈ l → y ∈ l → f x = f y → x = y
  | [], _, x, _, hx, _, _ => absurd hx (by simp)
  | a :: t, hd, x, y, hx, hy, hfx => by
      rcases List.mem_cons.1 hx with hxa | hxt
      · rcases List.mem_cons.1 hy with hya | hyt
        · exact hxa.trans hya.symm
        · exfalso
          obtain ⟨hnot, _⟩ := hd
          have hmem : f y ∈ List.map f t := List.mem_map.2 ⟨y, hyt, rfl⟩
          rw [← hfx, hxa] at hmem
          exact hnot hmem
      · rcases List.mem_cons.1 hy with hya | hyt
        · exfalso
          obtain ⟨hnot, _⟩ := hd
          have hmem : f x ∈ List.map f t := List.mem_map.2 ⟨x, hxt, rfl⟩
          rw [hfx, hya] at hmem
          exact hnot hmem
        · exact distinctMapInjOn f t hd.2 x y hxt hyt hfx

/-- **匹配减半引理（lane_87b 主件；纯抽象、零 sorry）**：路径表 T 中
    S 的每个星都有端点路径 ⟹ 存在匹配 M（路径互异、星互异、逐对为
    (路径, 星, 头/尾) 合法对）使 |S| ≤ 2|M|（即 |M| ≥ ⌈|S|/2⌉）。
    证明：对 T 归纳。当前路径无星端点则跳过；有星端点 v 则配对
    (P, v) 并把 P 的全部星端点（≤ 2 个）从 S 剔除后归纳——每步
    恰增 1 对、至多耗 2 星，计数不变式保持。 -/
theorem matchHalve {V : Type} [DecidableEq V] :
    ∀ (T : List (List V)) (S : List V), Distinct S →
      (∀ v ∈ S, ∃ Q ∈ T, isEnd v Q) →
      ∃ M : List (List V × (V × Bool)),
        Distinct (M.map (fun pr : List V × (V × Bool) => pr.1)) ∧
        Distinct (M.map (fun pr : List V × (V × Bool) => pr.2.1)) ∧
        (∀ pr ∈ M, pr.1 ∈ T ∧ pr.2.1 ∈ S ∧
          ((pr.2.2 = true ∧ pr.1.head? = some pr.2.1) ∨
           (pr.2.2 = false ∧ lastOf pr.1 = some pr.2.1))) ∧
        S.length ≤ 2 * M.length := by
  intro T
  induction T with
  | nil =>
    intro S _ hinc
    have hS0 : S = [] := by
      cases S with
      | nil => rfl
      | cons a0 t0 =>
        obtain ⟨Q, hQ, _⟩ := hinc a0 (List.mem_cons.2 (Or.inl rfl))
        simp at hQ
    refine ⟨[], trivial, trivial, ?_, ?_⟩
    · intro pr hpr
      simp at hpr
    · rw [hS0]
      simp
  | cons P T' ih =>
    intro S hSdis hinc
    by_cases hE : S.filter (fun x => isEndB x P) = []
    · -- P 无星端点：跳过后归纳
      have hinc' : ∀ v ∈ S, ∃ Q ∈ T', isEnd v Q := by
        intro v hv
        obtain ⟨Q, hQ, hQv⟩ := hinc v hv
        rcases List.mem_cons.1 hQ with h1 | h2
        · exfalso
          have hvE : v ∈ S.filter (fun x => isEndB x P) :=
            List.mem_filter.2 ⟨hv, decide_eq_true_iff.2 (h1 ▸ hQv)⟩
          rw [hE] at hvE
          exact absurd hvE (by simp)
        · exact ⟨Q, h2, hQv⟩
      obtain ⟨M, hd1, hd2, hd3, hd4⟩ := ih S hSdis hinc'
      refine ⟨M, hd1, hd2, ?_, hd4⟩
      intro pr hpr
      obtain ⟨hA, hB, hC⟩ := hd3 pr hpr
      exact ⟨List.mem_cons_of_mem _ hA, hB, hC⟩
    · -- P 有星端点：配对一步，剔除其全部星端点
      obtain ⟨v, hvE⟩ := List.exists_mem_of_ne_nil _ hE
      have step : ∀ b : Bool,
          (b = true ∧ P.head? = some v) ∨ (b = false ∧ lastOf P = some v) →
          ∃ M : List (List V × (V × Bool)),
            Distinct (M.map (fun pr : List V × (V × Bool) => pr.1)) ∧
            Distinct (M.map (fun pr : List V × (V × Bool) => pr.2.1)) ∧
            (∀ pr ∈ M, pr.1 ∈ P :: T' ∧ pr.2.1 ∈ S ∧
              ((pr.2.2 = true ∧ pr.1.head? = some pr.2.1) ∨
               (pr.2.2 = false ∧ lastOf pr.1 = some pr.2.1))) ∧
            S.length ≤ 2 * M.length := by
        intro b hbv
        have hS'dis : Distinct (S.filter (fun x => !isEndB x P)) :=
          distinct_filter _ S hSdis
        have hinc' : ∀ w ∈ S.filter (fun x => !isEndB x P), ∃ Q ∈ T', isEnd w Q := by
          intro w hw
          obtain ⟨hwS, hnw⟩ := List.mem_filter.1 hw
          obtain ⟨Q, hQ, hQw⟩ := hinc w hwS
          rcases List.mem_cons.1 hQ with h1 | h2
          · exfalso
            have hwB : isEndB w P = true := decide_eq_true_iff.2 (h1 ▸ hQw)
            rw [hwB] at hnw
            exact Bool.noConfusion hnw
          · exact ⟨Q, h2, hQw⟩
        obtain ⟨M', hd1', hd2', hd3', hd4'⟩ := ih _ hS'dis hinc'
        refine ⟨(P, (v, b)) :: M', ?_, ?_, ?_, ?_⟩
        · -- 路径互异：P 的星端点已全部剔除
          rw [List.map_cons]
          refine ⟨?_, hd1'⟩
          intro hm
          obtain ⟨pr, hprM, hprP⟩ := List.mem_map.1 hm
          have hprP' : pr.1 = P := hprP
          have hIse : isEnd pr.2.1 pr.1 := by
            rcases (hd3' pr hprM).2.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · exact Or.inl h2
            · exact Or.inr h2
          rw [hprP'] at hIse
          have hIseB : isEndB pr.2.1 P = true := decide_eq_true_iff.2 hIse
          have hnw := (List.mem_filter.1 (hd3' pr hprM).2.1).2
          rw [hIseB] at hnw
          exact Bool.noConfusion hnw
        · -- 星互异：v 不在剩余星表中
          rw [List.map_cons]
          refine ⟨?_, hd2'⟩
          intro hm
          obtain ⟨pr, hprM, hprV⟩ := List.mem_map.1 hm
          have hprV' : pr.2.1 = v := hprV
          have hnw := (List.mem_filter.1 (hd3' pr hprM).2.1).2
          rw [hprV'] at hnw
          have hvB : isEndB v P = true := (List.mem_filter.1 hvE).2
          rw [hvB] at hnw
          exact Bool.noConfusion hnw
        · -- 成员与逐对合法性
          intro pr hpr
          rcases List.mem_cons.1 hpr with h1 | h2
          · rw [h1]
            exact ⟨List.mem_cons.2 (Or.inl rfl), (List.mem_filter.1 hvE).1, hbv⟩
          · exact ⟨List.mem_cons_of_mem _ (hd3' pr h2).1,
              (List.mem_filter.1 (hd3' pr h2).2.1).1, (hd3' pr h2).2.2⟩
        · -- 计数：|S| = |E| + |S'|，1 ≤ |E| ≤ 2，|S'| ≤ 2|M'|
          have hsplit := filterLensSplit (fun _ : V => true) (fun x => isEndB x P) S
          have hc1 : (S.filter (fun x => true && isEndB x P)).length
              = (S.filter (fun x => isEndB x P)).length :=
            filterLensCongr _ _ (fun x => by simp) S
          have hc2 : (S.filter (fun x => true && !isEndB x P)).length
              = (S.filter (fun x => !isEndB x P)).length :=
            filterLensCongr _ _ (fun x => by simp) S
          have hTl : (S.filter (fun _ : V => true)).length = S.length := by simp
          rw [hc1, hc2, hTl] at hsplit
          have hEpos : 0 < (S.filter (fun x => isEndB x P)).length := by
            cases hF : S.filter (fun x => isEndB x P) with
            | nil => rw [hF] at hvE; exact absurd hvE (by simp)
            | cons x0 t0 => simp
          have hEle2 : (S.filter (fun x => isEndB x P)).length ≤ 2 := by
            have hPne : P ≠ [] := by
              intro h0
              rw [h0] at hvE
              have hB : isEndB v ([] : List V) = true := (List.mem_filter.1 hvE).2
              exact Bool.noConfusion hB
            obtain ⟨a, t, rfl⟩ : ∃ (a : V) (t : List V), P = a :: t := by
              cases P with
              | nil => exact absurd rfl hPne
              | cons a0 t0 => exact ⟨a0, t0, rfl⟩
            have hhead : (a :: t).head? = some a := rfl
            obtain ⟨c, hc⟩ := lastOf_some_of_ne_nil (a :: t) (by simp)
            have hcA : ∀ x : V, (isEndB x (a :: t) && decide (x = a)) = decide (x = a) := by
              intro x
              by_cases hxa : x = a
              · rw [hxa]
                have hbA : isEndB a (a :: t) = true := by
                  show decide ((a :: t).head? = some a ∨ lastOf (a :: t) = some a)
                  rw [hhead]
                  simp
                rw [hbA, decide_eq_true_iff.2 rfl, Bool.true_and]
              · rw [decide_eq_false_iff_not.2 hxa, Bool.and_false]
            have hcC : ∀ x : V, (isEndB x (a :: t) && !decide (x = a)) = true →
                decide (x = c) = true := by
              intro x hx
              obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.1 hx
              rcases decide_eq_true_iff.1 h1 with h3 | h3
              · have hxa' : x = a := by
                  have hsome : some a = some x := hhead.symm.trans h3
                  exact (Option.some.inj hsome).symm
                have hxT : decide (x = a) = true := decide_eq_true_iff.2 hxa'
                rw [hxT] at h2
                exact Bool.noConfusion h2
              · have hcx : c = x := Option.some.inj (hc.symm.trans h3)
                rw [hcx]
                exact decide_eq_true_iff.2 rfl
            have hsplit2 := filterLensSplit (fun x => isEndB x (a :: t))
              (fun x => decide (x = a)) S
            have hcA' : (S.filter (fun x => isEndB x (a :: t) && decide (x = a))).length
                = (S.filter (fun x => decide (x = a))).length :=
              filterLensCongr _ _ hcA S
            have hcC' : (S.filter (fun x => isEndB x (a :: t) && !decide (x = a))).length
                ≤ (S.filter (fun x => decide (x = c))).length :=
              filter_len_mono _ _ hcC S
            have h1a := distinctFilterEqLen S a hSdis
            have h1c := distinctFilterEqLen S c hSdis
            rw [hcA'] at hsplit2
            omega
          simp only [List.length_cons]
          omega
      rcases decide_eq_true_iff.1 (List.mem_filter.1 hvE).2 with hhead | hlast
      · exact step true (Or.inl ⟨rfl, hhead⟩)
      · exact step false (Or.inr ⟨rfl, hlast⟩)

/-- 匹配表的 σ-选取函数：路径 Q 在 M 中的配对；无配对时 none（lane_87b）。 -/
def selOf {n : Nat} (M : List (List (Fin n) × (Fin n × Bool))) (Q : List (Fin n)) :
    Option (Fin n × Bool) :=
  ((M.filter (fun pr => decide (pr.1 = Q))).head?).map (fun pr => pr.2)

/-- selOf 选中即配对在 M 中（lane_87b）。 -/
theorem mem_selOf {n : Nat} (M : List (List (Fin n) × (Fin n × Bool))) (Q : List (Fin n))
    (vb : Fin n × Bool) (h : selOf M Q = some vb) : (Q, vb) ∈ M := by
  unfold selOf at h
  cases hF : M.filter (fun pr => decide (pr.1 = Q)) with
  | nil =>
    rw [hF] at h
    exact absurd h (by simp)
  | cons x t =>
    rw [hF] at h
    have hEq2 : x.2 = vb := by simpa using h
    have hmem : x ∈ M.filter (fun pr => decide (pr.1 = Q)) := by
      rw [hF]
      exact List.mem_cons.2 (Or.inl rfl)
    have hEq1 : x.1 = Q := decide_eq_true_iff.1 (List.mem_filter.1 hmem).2
    have hxM : x ∈ M := (List.mem_filter.1 hmem).1
    cases x with
    | mk p1 p2 =>
      rw [← hEq1, ← hEq2]
      exact hxM

/-- 匹配成员必被自身选取函数选中（路径唯一性，lane_87b）。 -/
theorem selOf_self {n : Nat} (M : List (List (Fin n) × (Fin n × Bool)))
    (pr : List (Fin n) × (Fin n × Bool)) (hpr : pr ∈ M)
    (hinj : ∀ x y : List (Fin n) × (Fin n × Bool), x ∈ M → y ∈ M → x.1 = y.1 → x = y) :
    selOf M pr.1 = some pr.2 := by
  have hfil : pr ∈ M.filter (fun x => decide (x.1 = pr.1)) :=
    List.mem_filter.2 ⟨hpr, decide_eq_true_iff.2 rfl⟩
  cases hF : M.filter (fun x => decide (x.1 = pr.1)) with
  | nil =>
    rw [hF] at hfil
    exact absurd hfil (by simp)
  | cons x t =>
    have hxF : x ∈ M.filter (fun x => decide (x.1 = pr.1)) := by
      rw [hF]
      exact List.mem_cons.2 (Or.inl rfl)
    have hxM : x ∈ M := (List.mem_filter.1 hxF).1
    have hxEq : x.1 = pr.1 := decide_eq_true_iff.1 (List.mem_filter.1 hxF).2
    have hxE : x = pr := hinj x pr hxM hpr hxEq
    unfold selOf
    rw [hF, hxE]
    rfl

/-- 匹配表四条件 ⟹ σ-选取函数满足 AttachOK（lane_86 接口；lane_87b）。 -/
theorem attachOK_of_match {n : Nat} (G : Graph n) (u : Fin n) (D : List (List (Fin n)))
    (M : List (List (Fin n) × (Fin n × Bool)))
    (hM1 : Distinct (M.map (fun pr : List (Fin n) × (Fin n × Bool) => pr.1)))
    (hM2 : Distinct (M.map (fun pr : List (Fin n) × (Fin n × Bool) => pr.2.1)))
    (hMV : ∀ pr ∈ M,
      (pr.2.2 = true ∧ pr.1.head? = some pr.2.1) ∨
      (pr.2.2 = false ∧ lastOf pr.1 = some pr.2.1))
    (hMu : ∀ pr ∈ M, u ∉ pr.1)
    (hMstar : ∀ pr ∈ M, EVAdj G u pr.2.1) :
    AttachOK G u D (selOf M) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro P v b hb
    exact hMstar _ (mem_selOf M P (v, b) hb)
  · intro P v hb
    obtain hval := hMV _ (mem_selOf M P (v, true) hb)
    rcases hval with ⟨_, hE⟩ | ⟨hF, _⟩
    · exact ⟨hE, hMu _ (mem_selOf M P (v, true) hb)⟩
    · exact Bool.noConfusion hF
  · intro P v hb
    obtain hval := hMV _ (mem_selOf M P (v, false) hb)
    rcases hval with ⟨hT, _⟩ | ⟨_, hE⟩
    · exact Bool.noConfusion hT
    · exact ⟨hE, hMu _ (mem_selOf M P (v, false) hb)⟩
  · intro v b w c P Q _ _ hPQ hb hc
    intro hvw
    have h1 := mem_selOf M P (v, b) hb
    have h2 := mem_selOf M Q (w, c) hc
    have hEq : (P, (v, b)) = (Q, (w, c)) := by
      refine distinctMapInjOn (fun pr : List (Fin n) × (Fin n × Bool) => pr.2.1) M hM2
        (P, (v, b)) (Q, (w, c)) h1 h2 ?_
      show v = w
      rw [hvw]
    exact hPQ (congrArg Prod.fst hEq)

/-- 匹配的星顶点全部落入 attachImage ⟹ |M| ≤ |A|（lane_87b）。 -/
theorem matchStars_le_image {n : Nat}
    (M : List (List (Fin n) × (Fin n × Bool))) (D : List (List (Fin n)))
    (hM1 : Distinct (M.map (fun pr : List (Fin n) × (Fin n × Bool) => pr.1)))
    (hM2 : Distinct (M.map (fun pr : List (Fin n) × (Fin n × Bool) => pr.2.1)))
    (hMD : ∀ pr ∈ M, pr.1 ∈ D) :
    M.length ≤ (attachImage (selOf M) D).length := by
  have hinjP : ∀ x y : List (Fin n) × (Fin n × Bool), x ∈ M → y ∈ M → x.1 = y.1 → x = y :=
    fun x y hx hy h =>
      distinctMapInjOn (fun pr : List (Fin n) × (Fin n × Bool) => pr.1) M hM1 x y hx hy h
  have hsub : ∀ e ∈ M.map (fun pr : List (Fin n) × (Fin n × Bool) => pr.2.1),
      e ∈ attachImage (selOf M) D := by
    intro e he
    obtain ⟨pr, hprM, hprE⟩ := List.mem_map.1 he
    rw [← hprE, l86mem_attachImage]
    exact ⟨pr.1, hMD pr hprM, pr.2.2, selOf_self M pr hprM hinjP⟩
  have hlen := pigeon
    (M.map (fun pr : List (Fin n) × (Fin n × Bool) => pr.2.1))
    (attachImage (selOf M) D) hM2 hsub
  rw [List.length_map] at hlen
  exact hlen

/-- **fan7 的全清洁情形（lane_87b 真证 = 机器命题 R1 的 Lean 化）**：
    hend 之上再加"每个星顶点都有避开 u 的端点路径"，则 fan7_use 结论完整
    成立。证明 = matchHalve（匹配 |M| ≥ ⌈k/2⌉）+ σ-改接组装（lane_86 底件，
    与 `fan7_reattach` 同体；这里显式取 A = attachImage (selOf M) D′
    以便对 |A| 计数）。 -/
theorem fan7_use_clean {n : Nat} (G : Graph n) (u : Fin n)
    (D' : List (List (Fin n))) (hD' : IsDecomp (delStar G u) D')
    (hend : ∀ w : Fin n, G.adjB w u = true → 0 < vEndCount D' w)
    (hclean : ∀ v : Fin n, EVAdj G u v → ∃ P ∈ D', isEnd v P ∧ u ∉ P) :
    ∃ (A : List (Fin n)) (hAsub : ∀ v ∈ A, EVAdj G u v),
      Distinct A ∧ (eDeg G u + 1) / 2 ≤ A.length ∧
      ∃ D₁ : List (List (Fin n)),
        IsDecomp (gStar G u A hAsub) D₁ ∧ D₁.length = D'.length ∧
        vEndCount D₁ u = vEndCount D' u + A.length := by
  obtain ⟨M, hM1, hM2, hM3, hM4⟩ :=
    matchHalve (D'.filter (fun P => !decide (u ∈ P))) (starList G u)
      (starList_distinct G u) (by
        intro v hv
        obtain ⟨P, hP, hEvP, huP⟩ := hclean v ((starList_spec G u v).1 hv)
        exact ⟨P, List.mem_filter.2 ⟨hP, by
          show (!decide (u ∈ P)) = true
          rw [decide_eq_false_iff_not.2 huP]
          rfl⟩, hEvP⟩)
  have hinjP : ∀ x y : List (Fin n) × (Fin n × Bool), x ∈ M → y ∈ M → x.1 = y.1 → x = y :=
    fun x y hx hy h =>
      distinctMapInjOn (fun pr : List (Fin n) × (Fin n × Bool) => pr.1) M hM1 x y hx hy h
  have hMu : ∀ pr ∈ M, u ∉ pr.1 := by
    intro pr hpr
    have hB := (List.mem_filter.1 (hM3 pr hpr).1).2
    intro hc
    rw [decide_eq_true_iff.2 hc] at hB
    exact Bool.noConfusion hB
  have hMstar : ∀ pr ∈ M, EVAdj G u pr.2.1 := fun pr hpr =>
    (starList_spec G u (pr.2.1)).1 (hM3 pr hpr).2.1
  have hOK : AttachOK G u D' (selOf M) :=
    attachOK_of_match G u D' M hM1 hM2 (fun pr hpr => (hM3 pr hpr).2.2) hMu hMstar
  -- σ-改接组装（lane_86 底件；A 显式取 attachImage 以便计数）
  have hAstar : ∀ v ∈ attachImage (selOf M) D', EVAdj G u v :=
    l86attachImage_star G u D' (selOf M) hOK
  have hAdis : Distinct (attachImage (selOf M) D') :=
    l86attachImage_distinct G u D' hD' (selOf M) hOK
  have hD₁ : IsDecomp (gStar G u (attachImage (selOf M) D') hAstar)
      (attachAll u (selOf M) D') :=
    ⟨⟨l86attachAll_paths G u D' hD' (selOf M) hOK hAstar,
      l86attachAll_cover G u D' hD' (selOf M) hOK hAstar,
      l86attachAll_disjoint G u D' hD' (selOf M) hOK⟩,
      l86attachAll_distinct G u D' hD' (selOf M) hOK⟩
  have hlen : (attachAll u (selOf M) D').length = D'.length := List.length_map _
  have hledger : vEndCount (attachAll u (selOf M) D') u
      = vEndCount D' u + (attachImage (selOf M) D').length :=
    l86attachAll_uEnd G u (selOf M) D' hOK
  refine ⟨attachImage (selOf M) D', hAstar, hAdis, ?_, attachAll u (selOf M) D',
    hD₁, hlen, hledger⟩
  have hMle := matchStars_le_image M D' hM1 hM2 (fun pr hpr =>
    (List.mem_filter.1 (hM3 pr hpr).1).1)
  have hksl : (starList G u).length = eDeg G u := rfl
  have hdm := Nat.div_add_mod (eDeg G u + 1) 2
  have hmlt : (eDeg G u + 1) % 2 < 2 := Nat.mod_lt _ (by omega)
  omega

/-- **fan7 的脏星残余（lane_87b 唯一新占位 sorry）**：全清洁判定失败
    （存在"脏"星顶点：其一切 D′-端点路径都含 u）时，需要 W/R 脏星移动、
    头合并、首边翻转的级联重排后才能回到纯改接匹配。机器底账
    （lab/fan87/exp_fan7_route.py）：R3 改接+四移动贪心在
    2,332,320/2,332,320 实例（n=4/5 全空间 + n=6 k≥3 剪枝）全部达
    ⌈k/2⌉、构造级自检 0 违反；R2 改接缺口实例必脏（n=5: 2,400、
    n=6: 49,680，0 例外）。Lean 化 = 对移动序列归纳（每步：路径改写 +
    IsPathDecomp 保持 + u 端点 +1 + 条数不变），留给后续 lane。 -/
theorem fan7_use_dirty_moves {n : Nat} (G : Graph n) (u : Fin n)
    (D' : List (List (Fin n))) (hD' : IsDecomp (delStar G u) D')
    (hend : ∀ w : Fin n, G.adjB w u = true → 0 < vEndCount D' w)
    (hdirty : ¬ ∀ v : Fin n, EVAdj G u v → ∃ P ∈ D', isEnd v P ∧ u ∉ P) :
    ∃ (A : List (Fin n)) (hAsub : ∀ v ∈ A, EVAdj G u v),
      Distinct A ∧ (eDeg G u + 1) / 2 ≤ A.length ∧
      ∃ D₁ : List (List (Fin n)),
        IsDecomp (gStar G u A hAsub) D₁ ∧ D₁.length = D'.length ∧
        vEndCount D₁ u = vEndCount D' u + A.length := by
  sorry

/-- **fan7 接口（lane_68 占位 → lane_87b 两支组装件）**：paper lem:fan7 =
    Fan 2005 Lemma 3.6 = BS21 Lemma 7（"star absorption"），累计形式，
    特化到 u 的完整 E-星。陈述与 lane_68 原文一字不差。证明两支：
    全清洁 ⟹ `fan7_use_clean`（匹配计数 + σ-改接，真证）；判定失败 ⟹
    `fan7_use_dirty_moves`（脏星残余，唯一占位）。位置说明：本定理依赖
    lane_86/lane_87b 各件，故移至其后；消费方 `reinsert_star` 不受影响。 -/
theorem fan7_use {n : Nat} (G : Graph n) (u : Fin n)
    (D' : List (List (Fin n))) (hD' : IsDecomp (delStar G u) D')
    (hend : ∀ w : Fin n, G.adjB w u = true → 0 < vEndCount D' w) :
    ∃ (A : List (Fin n)) (hAsub : ∀ v ∈ A, EVAdj G u v),
      Distinct A ∧ (eDeg G u + 1) / 2 ≤ A.length ∧
      ∃ D₁ : List (List (Fin n)),
        IsDecomp (gStar G u A hAsub) D₁ ∧ D₁.length = D'.length ∧
        vEndCount D₁ u = vEndCount D' u + A.length := by
  by_cases hclean : ∀ v : Fin n, EVAdj G u v → ∃ P ∈ D', isEnd v P ∧ u ∉ P
  · exact fan7_use_clean G u D' hD' hend hclean
  · exact fan7_use_dirty_moves G u D' hD' hend hclean

/-! ## Fan 类定理与回插引擎 -/


/-- **回插引擎（lane_68 真证）**（paper Thm 3.1 Step 3–4 = Fan lem:fan7 +
    lem:fan6 循环；lane_31 T31.2 回插段）：设 D′ 是 G̃ = delStar G u 的分解，
    u 在 G 中的每个邻居在 D′ 中有端点路径，星顶点全低 E-度，则整条 E-星可
    免费回插：得 G 的分解且条数不变。
    证明：fan7 给 A（|A| ≥ ⌈k/2⌉，k = eDeg u）朝 u 回插得 D₁
    （D₁(u) = D′(u) + |A| ≥ 1 + ⌈k/2⌉，D′(u) ≥ 1 由 u 奇于 G̃ + LB1(ii)）；
    剩余 L = F ∖ A（|L| = k − |A|）经 `lEngine` 逐条朝其星顶点回插——
    每步死邻居被 `deadCount_gStar_le` 限到 N_EV(v) ∖ {u}（≤ eDeg v − 1 ≤ 2），
    预算 D(u) ≥ |L| + 2 ≥ 3 > 2 逐步紧成立（budget_last 的不等式在
    lEngine 的预算不变量中等价实现）；末步经 `gStar_full` 把 gStar (A ∪ L)
    逐点等同于 G。两处外部输入为 `fan6_use`（W4' 起 = 直接占位，lane_111；
    原 fan6_nf 组装链因 fan6_nf 陈述被机器反例证伪而摘除，见 Fan.lean 封存
    注释与 campaign/lane_109_audit.md）/ `fan7_use`
    （Fan 2005 Lem 3.6 的一对一占位）。本定理自身的组合逻辑与计数全部真证。 -/
theorem reinsert_star {n : Nat} (G : Graph n) (u : Fin n)
    (hA1 : A1 G) (hlow : ∀ v : Fin n, EVAdj G u v → eDeg G v ≤ 3)
    (huOddE : eDeg G u % 2 = 1)
    (D' : List (List (Fin n))) (hD' : IsDecomp (delStar G u) D')
    (hend : ∀ w : Fin n, G.adjB w u = true → 0 < vEndCount D' w) :
    ∃ D : List (List (Fin n)), IsDecomp G D ∧ D.length = D'.length := by
  -- Step 3：fan7 星吸收，得 A 与 D₁（G̃ + A 的分解）
  obtain ⟨A, hAsub, hAdis, hAlen, D₁, hD₁, hlen₁, hu₁⟩ := fan7_use G u D' hD' hend
  -- L := F ∖ A（F = starList G u）
  have hFL : ∀ v ∈ (starList G u).filter (fun w => !(decide (w ∈ A))), EVAdj G u v := by
    intro v hv
    obtain ⟨hm, _⟩ := List.mem_filter.1 hv
    exact (starList_spec G u v).1 hm
  have hLdis : Distinct ((starList G u).filter (fun w => !(decide (w ∈ A)))) :=
    distinct_filter _ (starList G u) (starList_distinct G u)
  have hLA : ∀ v ∈ (starList G u).filter (fun w => !(decide (w ∈ A))), v ∉ A := by
    intro v hv
    have h2 := (List.mem_filter.1 hv).2
    intro hm
    rw [decide_eq_true_iff.2 hm] at h2
    exact Bool.noConfusion h2
  -- 计数 |L| + |A| = eDeg G u（F = A ⊔ L 双向鸽笼）
  have hcardL : ((starList G u).filter (fun w => !(decide (w ∈ A)))).length + A.length
      = eDeg G u := by
    have hAsubF : ∀ v ∈ A, v ∈ starList G u :=
      fun v hv => (starList_spec G u v).2 (hAsub v hv)
    have hInt : ((starList G u).filter (fun w => decide (w ∈ A))).length = A.length := by
      have h1 := pigeon A ((starList G u).filter (fun w => decide (w ∈ A))) hAdis
        (fun x hx => List.mem_filter.2 ⟨hAsubF x hx, decide_eq_true_iff.2 hx⟩)
      have h2 := pigeon ((starList G u).filter (fun w => decide (w ∈ A))) A
        (distinct_filter _ (starList G u) (starList_distinct G u))
        (fun x hx => decide_eq_true_iff.1 (List.mem_filter.1 hx).2)
      omega
    have hsplit := filterLensSplit (fun _ : Fin n => true) (fun w => decide (w ∈ A))
      (starList G u)
    have hT : ((starList G u).filter (fun _ : Fin n => true)).length = eDeg G u := by
      show ((starList G u).filter (fun _ : Fin n => true)).length = (starList G u).length
      simp
    have hc1 : ((starList G u).filter
        (fun w => (fun _ : Fin n => true) w && decide (w ∈ A))).length
        = ((starList G u).filter (fun w => decide (w ∈ A))).length :=
      filterLensCongr _ _ (fun w => by simp) (starList G u)
    have hc2 : ((starList G u).filter
        (fun w => (fun _ : Fin n => true) w && !(decide (w ∈ A)))).length
        = ((starList G u).filter (fun w => !(decide (w ∈ A)))).length :=
      filterLensCongr _ _ (fun w => by simp) (starList G u)
    rw [hc1, hc2, hT, hInt] at hsplit
    omega
  -- 预算：D′(u) ≥ 1 且 2|A| ≥ k + 1 ⟹ |L| + 2 ≤ D₁(u) = D′(u) + |A|
  have huD' : 0 < vEndCount D' u :=
    vEndCount_pos_of_odd (delStar G u) D' hD' u (odd_delStar_u G u huOddE).1
  have h2A : eDeg G u + 1 ≤ 2 * A.length := by omega
  have hAL : ∀ v ∈ A ++ ((starList G u).filter (fun w => !(decide (w ∈ A)))),
      EVAdj G u v := by
    intro v hv
    rcases List.mem_append.1 hv with h1 | h2
    · exact hAsub v h1
    · exact hFL v h2
  -- Step 4：lEngine 逐条朝星顶点回插 L
  obtain ⟨D₂, hD₂, hlen₂, _⟩ :=
    lEngine G u hA1 hlow ((starList G u).filter (fun w => !(decide (w ∈ A)))) hFL hLdis
      A hAsub hAdis hLA hAL D₁ hD₁ (by omega)
  -- gStar (A ∪ L) 逐点等于 G
  have hvM : ∀ v : Fin n, EVAdj G u v →
      v ∈ A ++ ((starList G u).filter (fun w => !(decide (w ∈ A)))) := by
    intro v hvE
    by_cases hvA : v ∈ A
    · exact List.mem_append.2 (Or.inl hvA)
    · exact List.mem_append.2 (Or.inr (List.mem_filter.2
        ⟨(starList_spec G u v).2 hvE, by
          rw [decide_eq_false_iff_not.2 hvA]
          rfl⟩))
  have hEqG := gStar_full G u
    (A ++ ((starList G u).filter (fun w => !(decide (w ∈ A))))) hAL hvM
  exact ⟨D₂, decomp_congr hEqG hD₂, hlen₂.trans hlen₁⟩

/-- 预算算术（paper Step 4 末步：D_j(u) ≥ 1 + ⌈k/2⌉ − (j−1) ≥ 3 > 2；
    j ≥ 1 对应回插循环的步号）。 -/
theorem budget_last {k j : Nat} (hk : k % 2 = 1) (hj1 : 0 < j)
    (hj : j ≤ (k - 1) / 2) :
    3 ≤ 1 + (k + 1) / 2 - (j - 1) := by
  have hmk : ∃ m : Nat, k = 2 * m + 1 := ⟨k / 2, by omega⟩
  obtain ⟨m, hm⟩ := hmk
  have h1 : (k + 1) / 2 = m + 1 :=
    Nat.div_eq_of_eq_mul_left (by omega) (by rw [hm]; omega)
  have h2 : (k - 1) / 2 = m :=
    Nat.div_eq_of_eq_mul_left (by omega) (by rw [hm]; omega)
  rw [h2] at hj
  rw [h1]
  omega

/-! ### 边数严格下降（归纳步） -/

/-- 互异列表的真子集长度严格小。 -/
theorem distinctSublistLenLt {V : Type} [DecidableEq V] {l₁ l₂ : List V}
    (hd₁ : Distinct l₁) (hd₂ : Distinct l₂) (hsub : ∀ x ∈ l₁, x ∈ l₂) (e : V)
    (he₂ : e ∈ l₂) (hnot : ∀ x ∈ l₁, x ≠ e) : l₁.length < l₂.length := by
  have hle := pigeon l₁ (l₂.filter (fun x => decide (x ≠ e))) hd₁
    (fun x hx => List.mem_filter.2 ⟨hsub x hx, decide_eq_true_iff.2 (hnot x hx)⟩)
  have hpart := filterLensSplit (fun _ => true) (fun x => decide (x = e)) l₂
  have hc1 : ((l₂.filter (fun x => true && decide (x = e)))).length
      = ((l₂.filter (fun x => decide (x = e)))).length :=
    filterLensCongr _ _ (fun x => by simp) l₂
  have hc2 : ((l₂.filter (fun x => true && !(decide (x = e))))).length
      = ((l₂.filter (fun x => decide (x ≠ e)))).length :=
    filterLensCongr _ _ (fun x => by
      by_cases hxe : x = e
      · simp [hxe]
      · simp [hxe]) l₂
  have hT : (l₂.filter (fun x => true)).length = l₂.length := by simp
  have hge2 : 0 < (l₂.filter (fun x => decide (x = e))).length := by
    have hmem : e ∈ l₂.filter (fun x => decide (x = e)) := by
      simp [he₂]
    exact Nat.pos_of_ne_zero (by
      intro h0
      have hnil : List.filter (fun x => decide (x = e)) l₂ = [] :=
        List.eq_nil_of_length_eq_zero h0
      rw [hnil] at hmem
      exact absurd hmem (by simp))
  rw [hc1, hc2] at hpart
  rw [hT] at hpart
  omega

/-- 删星严格减少边数（u 至少有一个 EV-邻居）。 -/
theorem edgeCount_delStar_lt {n : Nat} (G : Graph n) (u v : Fin n) (h : EVAdj G u v) :
    edgeCount (delStar G u) < edgeCount G := by
  have hsub : ∀ e ∈ edgesOf (delStar G u), e ∈ edgesOf G := by
    intro e he
    obtain ⟨x, _, hy⟩ := List.mem_flatMap.1 he
    obtain ⟨y, hy2, hproj⟩ := List.mem_map.1 hy
    have hc : (decide (x.val < y.val) && delAdj G u x y) = true :=
      (List.mem_filter.1 hy2).2
    have hlt : x.val < y.val := decide_eq_true_iff.1 (Bool.and_eq_true_iff.1 hc).1
    have hda : delAdj G u x y = true := (Bool.and_eq_true_iff.1 hc).2
    have he' : e = (x, y) := by rw [← hproj]
    rw [he']
    exact (mem_edgesOf_iff G x y).2 ⟨hlt, (delAdj_true_iff G u x y).1 hda |>.1⟩
  have hnot : ∀ e ∈ edgesOf (delStar G u), e ≠ normPair u v := by
    intro e he hne
    obtain ⟨x, _, hy⟩ := List.mem_flatMap.1 he
    obtain ⟨y, hy2, hproj⟩ := List.mem_map.1 hy
    have hc : (decide (x.val < y.val) && delAdj G u x y) = true :=
      (List.mem_filter.1 hy2).2
    have hda : delAdj G u x y = true := (Bool.and_eq_true_iff.1 hc).2
    have he' : e = (x, y) := by rw [← hproj]
    rw [he'] at hne
    unfold normPair at hne
    split at hne
    · have h1 : u = x ∧ v = y := by simpa [Prod.mk.injEq] using hne.symm
      rw [← h1.1, ← h1.2] at hda
      simp [delAdj, h] at hda
    · have h1 : v = x ∧ u = y := by simpa [Prod.mk.injEq] using hne.symm
      rw [← h1.1, ← h1.2] at hda
      simp [delAdj, h] at hda
  exact distinctSublistLenLt (edgesOf_distinct _) (edgesOf_distinct G) hsub
    (normPair u v) (adj_normPair_mem_edgesOf G u v h.2.1 h.1) hnot

/-- 无边图的空分解。 -/
theorem nilDecomp_of_edgeNil {n : Nat} (G : Graph n) (hE : edgeCount G = 0) :
    IsDecomp G [] := by
  have hcover : IsCover (GAdj G) [] := by
    intro x y hxy
    exfalso
    have hne : x ≠ y := by
      intro he
      rw [he] at hxy
      exact Bool.noConfusion (hxy.symm.trans (G.loopless y))
    have hnp := adj_normPair_mem_edgesOf G x y hxy hne
    rcases hE' : edgesOf G with _ | ⟨e, l⟩
    · rw [hE'] at hnp
      exact absurd hnp (by simp)
    · have hE1 : (edgesOf G).length = 0 := hE
      rw [hE'] at hE1
      simp at hE1
  refine ⟨⟨fun P hP => absurd hP (by simp), hcover,
    fun P hP => absurd hP (by simp)⟩, by trivial⟩

/-! ## A\* 主定理组装（真证） -/

/-- **Step 2（宿主）**：u 在 G 中的每个邻居在 G̃ 的任意分解中都有端点路径。
    星顶点在 G̃ 中奇（度 −1）；非星邻居在 G 中奇（若偶则成 EV-边）且度不变。 -/
theorem hend_of_delStar {n : Nat} (G : Graph n) (u : Fin n) (huEven : EvenDeg G u)
    (D' : List (List (Fin n))) (hD' : IsDecomp (delStar G u) D') :
    ∀ w : Fin n, G.adjB w u = true → 0 < vEndCount D' w := by
  intro w hwu
  have hwu' : G.adjB u w = true := G.symm w u hwu
  have hwne : w ≠ u := by
    intro he
    rw [he] at hwu
    exact Bool.noConfusion ((G.loopless u).symm.trans hwu)
  by_cases hevw : EVAdj G u w
  · have hodd : deg (delStar G u) w % 2 = 1 := by
      have h1 := deg_delStar_of_star G u w hevw
      have h2 : deg G w % 2 = 0 := hevw.2.2.2
      omega
    exact vEndCount_pos_of_odd (delStar G u) D' hD' w hodd
  · have hoddG : deg G w % 2 = 1 := by
      by_cases hc : deg G w % 2 = 1
      · exact hc
      · have h0 : deg G w % 2 = 0 := by
          have := Nat.mod_two_eq_zero_or_one (deg G w)
          omega
        have hE : EVAdj G u w := ⟨hwne.symm, hwu', huEven, h0⟩
        exact absurd hE hevw
    have hfar := deg_delStar_of_far G u w hwne hevw
    have hodd : deg (delStar G u) w % 2 = 1 := by omega
    exact vEndCount_pos_of_odd (delStar G u) D' hD' w hodd

/-! ## lane_81：fan_class 分解（奇步真证 + 两个核） -/

/-- **核 K-T（终态：EV 无边）**：一切 E-度 = 0（EV(G) 无边，每条边都触奇点）
    ⟹ pn(G) ≤ ⌊n/2⌋。这是 Pyber 型定理（paper thm:pyber "EV 森林"的无边特例），
    证明需自造分解（Lovász 路-圈分解的圈消除在这类上非自由：割一圈丢一边覆盖）。
    【占位 sorry——lane_81 fan_class 分解出的核之一；陈述经穷举验证：
    lab/fan81/，n ≤ 6 全空间 26,402 个类成员中 8,945 个终态实例 0 违反；
    n = 7 全空间 0 违反（1,491,410 成员，终态 373,409 例），
    见 lab/fan81/run_n7_shard*.log】 -/
theorem fan_class_terminal {n : Nat} (G : Graph n)
    (h0 : ∀ v : Fin n, eDeg G v = 0) :
    pNumG G ≤ n / 2 := by
  sorry

/-- **核 K-02（case02：全 E-度 ∈ {0,2} 且有 2）**：EV 的非孤立点部分 2-正则
    = 不交圈（(A1) ⟹ 圈长 ≥ 4），Fan 2005 的双圈边删除 + 两次 fan6 回插案例
    （lane_02 §6.2 P2b 备注）。注意两次单边 fan6 链接在一般预算下不闭合
    （圈前驱点 D̃ 可为 0），构造需 Fan 原文的圈-对选择（[UNVERIFIED-原文级]）。
    【占位 sorry——lane_81 fan_class 分解出的核之一；陈述经穷举验证：
    lab/fan81/，n ≤ 6 全空间 897 个 case02 实例 0 违反（其中全部 897 个
    还存在保类双删边 G′ 使 pn(G) ≤ pn(G′)，即 Fan 归约形式在这些范围内
    也成立）；n = 7 全空间 0 违反（1,491,410 成员，终态 373,409 例），
    见 lab/fan81/run_n7_shard*.log】 -/
theorem fan_class_case02 {n : Nat} (G : Graph n) (h1 : A1 G)
    (h02 : ∀ v : Fin n, eDeg G v = 0 ∨ eDeg G v = 2)
    (h2 : ∃ v : Fin n, eDeg G v = 2) :
    pNumG G ≤ n / 2 := by
  sorry

/-- **fan_class 归纳骨架（lane_81 真证）**：对边数强归纳，三分情形。
    情形 1（存在奇正 E-度点 u ⟹ E-度 ∈ {1,3}）：整星删除后类遗传
    （`A1_delStar` + `eDeg_delStar_le3`，均真证），归纳假设给 G̃ 的分解，
    `hend_of_delStar`（真证）给宿主端点，`reinsert_star`（lane_68 真证引擎，
    经 fan6_use/fan7_use）免费回插整星——k = 1 时 fan7 给 |A| ≥ 1 = k，L 空，
    与 k = 3 统一处理。
    情形 2（一切 E-度 ∈ {0,2} 且有 2）：核 K-02。
    情形 3（一切 E-度 = 0）：核 K-T。
    除两核外全部真证；`fan_class` 陈述不变，由本骨架背书。 -/
theorem fan_class_aux {n : Nat} :
    ∀ (m : Nat) (G : Graph n), edgeCount G ≤ m →
      A1 G → (∀ v : Fin n, eDeg G v ≤ 3) → pNumG G ≤ n / 2 := by
  intro m
  induction m with
  | zero =>
    intro G hE _ _
    have hE0 : edgeCount G = 0 := by omega
    have hnil : pNumG G ≤ 0 := pNumG_min G 0 ⟨[], nilDecomp_of_edgeNil G hE0, rfl⟩
    omega
  | succ m ih =>
    intro G hE h1 hlow
    by_cases hodd : ∃ u : Fin n, eDeg G u % 2 = 1 ∧ 0 < eDeg G u
    · -- 情形 1：奇步（真证组装）
      obtain ⟨u, hu⟩ := hodd
      have huOddE : eDeg G u % 2 = 1 := hu.1
      have huEven : EvenDeg G u := evenDeg_of_eDeg_pos G u hu.2
      have hA1' : A1 (delStar G u) := A1_delStar G u huOddE h1
      have hlow' : ∀ v : Fin n, eDeg (delStar G u) v ≤ 3 :=
        eDeg_delStar_le3 G u huOddE hlow
      obtain ⟨v₀, hv₀⟩ := exists_EVAdj_of_pos G u hu.2
      have hEc : edgeCount (delStar G u) < edgeCount G :=
        edgeCount_delStar_lt G u v₀ hv₀
      have hle : edgeCount (delStar G u) ≤ m := by omega
      have hpn' : pNumG (delStar G u) ≤ n / 2 := ih (delStar G u) hle hA1' hlow'
      obtain ⟨D', hD', hlen'⟩ := pNumG_spec (delStar G u)
      have hlen : D'.length ≤ n / 2 := by rw [hlen']; exact hpn'
      have hend := hend_of_delStar G u huEven D' hD'
      obtain ⟨D, hD, hlenD⟩ :=
        reinsert_star G u h1 (fun v _ => hlow v) huOddE D' hD' hend
      have hmin := pNumG_min G D.length ⟨D, hD, by rw [hlenD]⟩
      rw [hlenD] at hmin
      omega
    · by_cases h2 : ∃ v : Fin n, eDeg G v = 2
      · -- 情形 2：case02 核
        have h02 : ∀ v : Fin n, eDeg G v = 0 ∨ eDeg G v = 2 := by
          intro v
          have h3 := hlow v
          rcases Nat.eq_zero_or_pos (eDeg G v) with h0 | h0
          · exact Or.inl h0
          · have hne1 : eDeg G v % 2 ≠ 1 := by
              rintro hc
              exact hodd ⟨v, hc, h0⟩
            have h2m := Nat.mod_two_eq_zero_or_one (eDeg G v)
            omega
        exact fan_class_case02 G h1 h02 h2
      · -- 情形 3：终态核
        have h0 : ∀ v : Fin n, eDeg G v = 0 := by
          intro v
          have h3 := hlow v
          rcases Nat.eq_zero_or_pos (eDeg G v) with h0' | h0'
          · exact h0'
          · have hne1 : eDeg G v % 2 ≠ 1 := by
              rintro hc
              exact hodd ⟨v, hc, h0'⟩
            have h2m := Nat.mod_two_eq_zero_or_one (eDeg G v)
            have he2 : eDeg G v = 2 := by omega
            exact absurd ⟨v, he2⟩ h2
        exact fan_class_terminal G h0

/-- **Fan 类定理**（paper thm:fan 分量式 + lem:sum 被此陈述吸收）：
    EV 三角无关且一切 E-度 ≤ 3 ⟹ pn(G) ≤ ⌊n/2⌋。
    【lane_81 分解：陈述不变；证明 = `fan_class_aux` 强归纳骨架（真证：
    奇步删星-回插全组装 + 类遗传），缺口收缩为两个机器验证过的核
    `fan_class_terminal`（EV 无边 / Pyber 型）与 `fan_class_case02`
    （E-度 ∈ {0,2} / Fan 双圈边删除）。原 lane_68 评估的"千行 Fan 引擎"
    中，归纳组织与奇 E-度案例已真证；剩余是两个可独立攻击的核，各自
    一对一机器验证（lab/fan81/，n ≤ 6 全空间 0 违反）。lane_31/33 的
    DP 见证（579+ (A1)(A2) 实例）继续覆盖本引理的语义面。】 -/
theorem fan_class {n : Nat} (G : Graph n) (h1 : A1 G)
    (hlow : ∀ v : Fin n, eDeg G v ≤ 3) :
    pNumG G ≤ n / 2 :=
  fan_class_aux (edgeCount G) G (Nat.le_refl _) h1 hlow

/-- **A\* 修复版（paper thm:Astar / lane_31 T31.1）**：
    (A1)(A2)(A4) ⟹ pn(G) ≤ ⌊n/2⌋。
    证明 = paper Step 1–4：Step 1（结构 + 全低 E-度）经 `eDeg_delStar_le` 真证；
    Step 2（宿主端点）经 `hend_of_delStar` 真证；Step 3–4 = `reinsert_star`。
    连通性前提在证明中不使用（与 paper 一致：thm:sep 明言连通非必需）。 -/
theorem astar {n : Nat} (G : Graph n) (hconn : Connected G)
    (h1 : A1 G) (h2 : A2 G) (h4 : A4 G) :
    pNumG G ≤ n / 2 := by
  obtain ⟨u, huHigh, hA4⟩ := h4
  have huOddE : eDeg G u % 2 = 1 := (h2 u huHigh).1
  have huEven : EvenDeg G u :=
    evenDeg_of_eDeg_pos G u (by unfold IsHigh at huHigh; omega)
  -- Step 1：G̃ 满足 Fan 类假设
  have hA1' : A1 (delStar G u) := A1_delStar G u huOddE h1
  have hlow' : ∀ x : Fin n, eDeg (delStar G u) x ≤ 3 :=
    eDeg_delStar_le G u huHigh h2 hA4
  have hpn : pNumG (delStar G u) ≤ n / 2 := fan_class _ hA1' hlow'
  obtain ⟨D', hD', hlen'⟩ := pNumG_spec (delStar G u)
  have hlen : D'.length ≤ n / 2 := by rw [hlen']; exact hpn
  -- Step 2：u 的一切 G-邻居在 D′ 中有端点路径
  have hend := hend_of_delStar G u huEven D' hD'
  -- Step 3–4：回插引擎
  obtain ⟨D, hD, hlenD⟩ :=
    reinsert_star G u h1 ((h2 u huHigh).2) huOddE D' hD' hend
  have h1 := pNumG_min G D.length ⟨D, hD, by rw [hlenD]⟩
  rw [hlenD] at h1
  omega

/-! ## (A2)/(A3) 遗传与 astar_separated（lane_31 T31.2 强归纳） -/

/-- (A2) 遗传：删星后 G̃ 仍满足 (A2)。G̃ 的偶点全在 Far(u) 中，远高点的
    t_x = |N_EV(x) ∩ N_EV(u)| = 0（A3），故 E-度奇性与邻居低性均保持。 -/
theorem A2_delStar {n : Nat} (G : Graph n) (u : Fin n) (huHigh : IsHigh G u)
    (h2 : A2 G) (h3 : A3 G) : A2 (delStar G u) := by
  have huOddE : eDeg G u % 2 = 1 := (h2 u huHigh).1
  intro x hx
  have hx4 : 4 ≤ eDeg (delStar G u) x := hx
  have hxu : x ≠ u := by
    intro he
    rw [he] at hx
    unfold IsHigh at hx
    rw [eDeg_delStar_u G u huOddE] at hx
    omega
  have hpos : 0 < eDeg (delStar G u) x := by omega
  have hxe' : EvenDeg (delStar G u) x := evenDeg_of_eDeg_pos _ _ hpos
  obtain ⟨hxa, hxna, hxe⟩ := evenFar_of_delStar G u x huOddE hxe'
  have hP4 := eDeg_delStar_of_far G u x huOddE hxa hxna hxe
  have hxHigh : IsHigh G x := by
    show 4 ≤ eDeg G x
    omega
  have hc0 : evCommon G x u = 0 := by
    show ((finList n).filter
      (fun w => decide (EVAdj G x w ∧ EVAdj G u w))).length = 0
    refine filter_nil_len (fun w => decide (EVAdj G x w ∧ EVAdj G u w)) (finList n)
      (fun w _ => ?_)
    cases hd : decide (EVAdj G x w ∧ EVAdj G u w) with
    | false => rfl
    | true =>
      have hP : EVAdj G x w ∧ EVAdj G u w := decide_eq_true_iff.1 hd
      exact absurd hP (by
        intro hc
        exact h3 u x w huHigh hxHigh hxu.symm hc.2 hc.1)
  refine ⟨?_, ?_⟩
  · have hE1 : eDeg G x % 2 = 1 := (h2 x hxHigh).1
    omega
  · intro w hwEV
    have hfarW := evenFar_of_delStar G u w huOddE hwEV.2.2.2
    have hmono := EVAdj_delStar_mono G u x w huOddE hwEV
    have hP4w := eDeg_delStar_of_far G u w huOddE hfarW.1 hfarW.2.1 hfarW.2.2
    have hwLow : eDeg G w ≤ 3 := (h2 x hxHigh).2 w hmono
    omega

/-- (A3) 遗传：G̃ 的 EV-邻域 ⊆ G 的 EV-邻域，分离条件保持。 -/
theorem A3_delStar {n : Nat} (G : Graph n) (u : Fin n) (huHigh : IsHigh G u)
    (huOddE : eDeg G u % 2 = 1) (h3 : A3 G) : A3 (delStar G u) := by
  intro a b w ha hb hab haw hbw
  have haH : IsHigh G a := by
    have ha4 : 4 ≤ eDeg (delStar G u) a := ha
    have haE : EvenDeg (delStar G u) a := evenDeg_of_eDeg_pos _ _ (by omega)
    obtain ⟨ha1, ha2, ha3⟩ := evenFar_of_delStar G u a huOddE haE
    have hP4 := eDeg_delStar_of_far G u a huOddE ha1 ha2 ha3
    show 4 ≤ eDeg G a
    omega
  have hbH : IsHigh G b := by
    have hb4 : 4 ≤ eDeg (delStar G u) b := hb
    have hbE : EvenDeg (delStar G u) b := evenDeg_of_eDeg_pos _ _ (by omega)
    obtain ⟨hb1, hb2, hb3⟩ := evenFar_of_delStar G u b huOddE hbE
    have hP4 := eDeg_delStar_of_far G u b huOddE hb1 hb2 hb3
    show 4 ≤ eDeg G b
    omega
  exact h3 a b w haH hbH hab (EVAdj_delStar_mono G u a w huOddE haw)
    (EVAdj_delStar_mono G u b w huOddE hbw)

/-- **A\* 分离高点版（paper thm:sep / lane_31 T31.2）**：对一切满足
    (A1)(A2)(A3) 的图（不限连通）按边数强归纳。无高点 → Fan 类；
    有高点 → 删星遗传 + 归纳 + 回插引擎。 -/
theorem astar_separated_aux {n : Nat} :
    ∀ (m : Nat) (G : Graph n), edgeCount G ≤ m →
      A1 G → A2 G → A3 G → pNumG G ≤ n / 2 := by
  intro m
  induction m with
  | zero =>
    intro G hE _
    have hE0 : edgeCount G = 0 := by omega
    have hnil : pNumG G ≤ 0 := pNumG_min G 0 ⟨[], nilDecomp_of_edgeNil G hE0, rfl⟩
    omega
  | succ m ih =>
    intro G hE h1 h2 h3
    by_cases hH : ∃ v, IsHigh G v
    · obtain ⟨u, hu⟩ := hH
      have huOddE : eDeg G u % 2 = 1 := (h2 u hu).1
      obtain ⟨v₀, hv₀⟩ := exists_EVAdj_of_pos G u
        (by unfold IsHigh at hu; omega)
      -- 遗传
      have hA1' : A1 (delStar G u) := A1_delStar G u huOddE h1
      have hA2' : A2 (delStar G u) := A2_delStar G u hu h2 h3
      have hA3' : A3 (delStar G u) := A3_delStar G u hu huOddE h3
      have hEc : edgeCount (delStar G u) < edgeCount G := edgeCount_delStar_lt G u v₀ hv₀
      have hle : edgeCount (delStar G u) ≤ m := by omega
      have hpn' : pNumG (delStar G u) ≤ n / 2 :=
        ih (delStar G u) hle hA1' hA2' hA3'
      obtain ⟨D', hD', hlen'⟩ := pNumG_spec (delStar G u)
      have huEven : EvenDeg G u :=
        evenDeg_of_eDeg_pos G u (by unfold IsHigh at hu; omega)
      -- Step 2：宿主端点
      have hend := hend_of_delStar G u huEven D' hD'
      -- 回插引擎
      obtain ⟨D, hD, hlenD⟩ :=
        reinsert_star G u h1 ((h2 u hu).2) huOddE D' hD' hend
      have hmin := pNumG_min G D.length ⟨D, hD, by rw [hlenD]⟩
      rw [hlenD] at hmin
      omega
    · -- 无高点：全低 E-度 → Fan 类
      have hlow : ∀ v : Fin n, eDeg G v ≤ 3 := by
        intro v
        by_cases hh : 4 ≤ eDeg G v
        · exact absurd ⟨v, hh⟩ hH
        · omega
      exact fan_class G h1 hlow

/-- **A\* 分离高点版（paper thm:sep / lane_31 T31.2）**：
    (A1)(A2)(A3) ⟹ pn(G) ≤ ⌊n/2⌋。真证：对边数强归纳；
    删星遗传（(A1)(A2)(A3) 保持）+ 归纳假设给 G̃ 的分解 + 回插引擎重建 G 的分解。
    连通性前提在证明中不使用（paper thm:sep 证明即对不连通图成立）。 -/
theorem astar_separated {n : Nat} (G : Graph n) (hconn : Connected G)
    (h1 : A1 G) (h2 : A2 G) (h3 : A3 G) :
    pNumG G ≤ n / 2 :=
  astar_separated_aux (edgeCount G) G (Nat.le_refl _) h1 h2 h3

/-- **唯一高点特例（paper Cor 3.2 / lane_31 C31.4）**：(A1)(A2) + 恰一个高点 ⟹
    pn(G) ≤ ⌊n/2⌋。此为 astar 的直接推论：唯一高点 ⟹ (A4) 自动成立
    （一切偶度点 x ≠ u 均非高 ⟹ E-度 ≤ 3，Nat 截断减法保持 ≤ 3）。 -/
theorem astar_unique_high {n : Nat} (G : Graph n) (hconn : Connected G)
    (h1 : A1 G) (h2 : A2 G)
    (hex : ∃ u, IsHigh G u)
    (huniq : ∀ u x : Fin n, IsHigh G u → IsHigh G x → u = x) :
    pNumG G ≤ n / 2 := by
  -- (A4) 在唯一高点下自动成立
  have h4 : A4 G := by
    obtain ⟨u, hu⟩ := hex
    refine ⟨u, hu, ?_⟩
    intro x hx hxu hxuadj
    -- x 是偶度点且不是 u 的 EV-邻居：x 非高（否则与唯一高点矛盾）⟹ eDeg x ≤ 3
    have hxnotHigh : ¬ IsHigh G x := by
      intro hxx
      exact hxu (huniq u x hu hxx).symm
    -- Nat 截断减法：eDeg x - t ≤ eDeg x ≤ 3
    calc eDeg G x - evCommon G x u ≤ eDeg G x := Nat.sub_le _ _
      _ ≤ 3 := by
        cases Nat.lt_or_ge (eDeg G x) 4 with
        | inl h => exact Nat.lt_succ_iff.mp h
        | inr h => exact absurd h hxnotHigh
  exact astar G hconn h1 h2 h4

end Front583

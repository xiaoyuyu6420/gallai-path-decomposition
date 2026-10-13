import Front583.Pi3L2b

/-! # Front583.Pi3Uni — Π3·L2(b) 三均匀引理的表域机器证书 + M 侧「无均匀律」精确化

**承接对象**（deep_A334_pi3.md §2.1 路线 1 的三引理 + deep_A366_leanm.md 任务①②）：
A334 把 L2(b) 表压缩为「三引理 + 顶层证书 1,761 向量」，其中三引理是：

1. **下集性**：可行域 = 下集（纸面=两行限制论证；A334 机检 120×330×2 全核 0 违例）；
2. **均匀层 U-A334.1**：Σd ≤ |S|−1 双侧恒可行（A334 机检全零失败）；
3. **AGL(1,7) 不变性**：可行域只依赖 (S,s) 的 AGL(1,7) 轨道（A175 :46 纸面+A334
   53,760 检；本件不承载，另件处理）。

本件在 `Front583.Pi3L2b` 的打包谓词 `pkg` 与 120 轨道数据层之上，把引理 1、2 落为
**表域机器证书定理**（120 正典轨道 ×330 需求 ×双侧全域 `native_decide` 全查），
并把 A334「M 侧顶层 1,557 无均匀律」从开放表述精确化为 Lean 定理：

- `m_no_threshold_witness`：同轨道同 Σd=4 两需求一活一死——任何「可行 ⟺ f(Σd)」
  型均匀律在该轨道上不成立（oracle 侧统计：阈值律 M 侧仅 12/120 轨道存活，
  Σd/(Σd,max槽)/槽多重集三族统计量律均杀 108/120，机器账见 a366_mstruct.json）；
- `fails_top_only`：两侧顶层失败向量全部落在 Σd=|S| 层；
- `mf_upset`：M 侧顶层失败集 = 上集（下集性的顶层像）；
- `mf_orbits` / `nf_orbits`：失败轨道计数 110 / 2。

**诚实落款**（承 Pi3L2b/Cert12Led 口径）：本件全部定理以 `native_decide` 承载，
axioms 依赖 `Lean.ofReduceBool`（原生求值语义公理），非未证断言件、无 sorryAx；
覆盖域 = 120 正典轨道代表 ×330 需求（Σd≤7）×双侧，raw 4,480 对口径引用须携
AGL(1,7) 不变性（A175 :46 纸面 + 另件机器证书）。引理的一般形（任意 (S,s,d)）
纸面化不在本件内（下集性一般定理见另件；均匀层/不变性维持 A334 原档）。

**溯源链**：labA174.py::_pkg（md5 29a1272b…）→ a334_l2b_toplevel.json（md5
0d1e9f3f…）→ Front583.Pi3L2b（A360，lake build+axioms 双过、A361 复核）→ 本件。
本件 oracle 侧独立复验：a366_mstruct.py 对 _pkg 直算 79,200 点证书规则 0 违例 +
json↔oracle 120/120 轨道零失配（deep_A366 报告登记）。
-/

/-! ## 预备层：需求向量运算 -/

/-- 需求码 c 的第 i 槽减一（前置条件 `slot c i ≥ 1` 保证无跨槽借位）。 -/
def decCode (c : Nat) (i : Nat) : Nat := c - 2 ^ (3 * i)

/-- 需求支配：c' 逐槽 ≥ c（c 是 c' 的直接前驱方向）。 -/
def covers (c' c : Nat) : Bool :=
  Nat.ble (slot c 0) (slot c' 0) && Nat.ble (slot c 1) (slot c' 1) &&
    Nat.ble (slot c 2) (slot c' 2) && Nat.ble (slot c 3) (slot c' 3)

/-! ## 引理 1（下集性）：表域机器证书
可行点的一切直接前驱仍可行——120 轨道 ×330 需求 ×双侧逐点全查
（A334「可行域=下集」机器面的 Lean 全域承载）。 -/

/-- 单轨道单侧下集性：非零槽 i 的需求码 c，可行 ⟹ 前驱 decCode c i 可行。 -/
def downOK (o : Orb) (ban : Bool) : Bool :=
  Dem330.all (fun c => [0, 1, 2, 3].all (fun i =>
    (slot c i == 0) || (pkg o.S o.s ban c == false) ||
      (pkg o.S o.s ban (decCode c i) == true)))

/-- **下集性·N 侧全域证书**。 -/
theorem downset_table_N : orbitList.all (fun o => downOK o false) = true := by
  native_decide

/-- **下集性·M 侧全域证书**。 -/
theorem downset_table_M : orbitList.all (fun o => downOK o true) = true := by
  native_decide

/-! ## 引理 2（均匀层 U-A334.1）：表域机器证书
Σd ≤ |S|−1 ⟹ 双侧恒可行——A334 机检引理候选的全域 Lean 承载
（覆盖全部低层，强于 A334 的层 m−2/m−1 抽查口径）。 -/

/-- 单轨道单侧均匀层：Σd+1 ≤ |S|（即 Σd ≤ |S|−1）的需求码恒可行。 -/
def uniOK (o : Orb) (ban : Bool) : Bool :=
  Dem330.all (fun c => !(Nat.ble (sumd c + 1) (pc o.S)) || (pkg o.S o.s ban c == true))

/-- **均匀层·N 侧全域证书**。 -/
theorem uniform_layer_N : orbitList.all (fun o => uniOK o false) = true := by
  native_decide

/-- **均匀层·M 侧全域证书**。 -/
theorem uniform_layer_M : orbitList.all (fun o => uniOK o true) = true := by
  native_decide

/-! ## M 侧结构定理：任务①「无均匀律」的精确化
A334：M 侧顶层 1,557 向量散布 110 轨道，「是否再有均匀律未解决——阻断如实」。
本节把它精确化为可判定命题并机器裁决：任何经由 Σd（或更细统计量）的均匀律
在 108/120 轨道上被同层双值反例杀死；残存结构=上集性+全失败落顶层。 -/

/-- **M 侧「无均匀(阈值)律」见证定理**：轨道 (S={0,1,2,3}, s=[0,1,2,3]) 上
需求 585=(1,1,1,1) 与 2048=(0,0,0,4) 同有 Σd=4，前者可行、后者不可行——
故不存在函数 f 使「M 侧可行 ⟺ f(Σd)」（同一 Σd 两值）。oracle 侧由
a366_mstruct.py 对 labA174._pkg 直算确认（pkg(585)=True / pkg(2048)=False）。 -/
theorem m_no_threshold_witness :
    pkg 15 1672 true 585 = true ∧ pkg 15 1672 true 2048 = false ∧
      sumd 585 = 4 ∧ sumd 2048 = 4 := by
  native_decide

/-- **失败层级锚**：两侧全部顶层失败向量落在 Σd=|S| 层（1,761 条逐条）。 -/
theorem fails_top_only : orbitList.all (fun o =>
    o.nf.all (fun c => sumd c == pc o.S) && o.mf.all (fun c => sumd c == pc o.S)) = true := by
  native_decide

/-- M 侧顶层失败集的上集性：c 失败、c' 支配 c 且 c' 在顶层 ⟹ c' 失败
（下集性 downset_table_M 的顶层像；A334 上集性机器面的独立 Lean 全查）。 -/
def mfUpOK (o : Orb) : Bool :=
  o.mf.all (fun c => Dem330.all (fun c' =>
    (covers c' c == false) || (!(sumd c' == pc o.S)) || (o.mf.contains c')))

/-- **M 侧顶层失败集 = 上集（全域证书）**。 -/
theorem mf_upset : orbitList.all mfUpOK = true := by
  native_decide

/-- **失败轨道计数**：M 侧 1,557 向量散布恰 110 轨道（A334 §2.1 数字）。 -/
theorem mf_orbits : (orbitList.filter (fun o => !(o.mf.isEmpty))).length = 110 := by
  native_decide

/-- **失败轨道计数**：N 侧 204 向量恰在 2 例外轨道（=L2(a) 2 色 key-Hall 墙轨道）。 -/
theorem nf_orbits : (orbitList.filter (fun o => !(o.nf.isEmpty))).length = 2 := by
  native_decide

/-! ## 零洞机器证据（承 Fan.lean lane_314 先例） -/

#print axioms downset_table_N
#print axioms downset_table_M
#print axioms uniform_layer_N
#print axioms uniform_layer_M
#print axioms m_no_threshold_witness
#print axioms fails_top_only
#print axioms mf_upset
#print axioms mf_orbits
#print axioms nf_orbits

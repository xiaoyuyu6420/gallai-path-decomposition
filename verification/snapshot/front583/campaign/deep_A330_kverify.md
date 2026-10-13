# deep_A330_kverify：K/Krenn–Gu 归约线终审前置重验（全战役最大未定价风险正面清偿）

> 2026-10-10。深度平面重验棒 A330。任务：对 K 线时代承下的上层归约链（Gallai ⟸ 猜想K(β) ⟸ SC-PH/N*(deg=2层) ⟸ GAP-20a′ ⟸ (E)+(R) ⟸ C165.1/C236.F ⟸ 引理丙 ⟸ 266.3(so1)）按现行审计标准做从零重推导；默认链有错，断点比 PASS 更有价值。
> 净域 /tmp/deepA33x/（a330_ 前缀）。全程离线。正典四件（STATE.md / FRONTIER.md / paper / EXTERNAL_P1_LOVASZ_VERIFY.md）全程只读。本报告为唯一写盘正典外件。
> **深度平面结论：verdict = won（partial 偏 won 的保守读法见 §6）——链的全部承重蕴含经从零独立重推成立、六组独立机检零失败；但坐实 3 处表述/登记层断点（W-A330-1/2/3，verbatim 见 §5），均不改变任何蕴含方向或前提真实性，修复成本低；无实质数学洞。Π1 离线证明重构达骨架级（完整重构未达成，卡点如实定位 §4.9）。**

---

## 0. 素材亲读清单（全部本棒全文直读）

| 件 | 用途 |
|---|---|
| paper/sec6-10.tex:340-826（§7 条件章全节） | 装配节：lem:T1 / prop:buried / def:beta / conj:K / thm:Kgallai / prop:Nequiv / conj:N / conj:SCPH / thm:reduction / ledger 三行式 / Π1-Π8 / thm:gallaimodulo / rem:moduloassembly |
| paper/sec6-10.tex:19-338（§6 机器章） | thm:machM 三档 / prop:2663cand / conj:tdich / 依赖链五步 / 审计锚索引 |
| paper/sec1-3.tex:224-453（§2 prelim + 记号节） | lem:LB1 / lem:LB2 / thm:lovasz / lem:fan6/7 / def:osc / lem:walecki / def:endpointbudget / so1 语言 |
| paper/appendix.tex:185-229（app:comp 证据表） | conj:K / conj:N 证据行与 count note（210,864 记载） |
| paper/appendix.tex:2412-2845（app:mu2663 头部 + 282.A-F 定位） | Π8 宿主（partial 状态自述） |
| campaign/STATE.md（§①环图 R0-R10、②登记簿、③数字、⑤术语、⑥开放清单 + REVISE 段） | K 线原始登记 |
| campaign/FRONTIER.md（REVISE-71 期） | 当前期 + 六不宣称 |
| campaign/EXTERNAL_P1_LOVASZ_VERIFY.md | Π1 五源核验记录 |
| campaign/lane_11_conjecture_K.md（全文 210 行） | T11.2/T11.1/T11.3/T11.4/R₂/死区 |
| campaign/lane_17_ph_conjectures.md（全文 345 行 + REVISE） | PH 对/T17.6/T17.9/五支表 |
| campaign/lane_19_conjecture_N.md（全文 267 行 + REVISE R1/R2） | T19.0/T19.5/批K3/210,864 口径 |
| campaign/lane_20_scph.md（全文 245 行 + REVISE R1/R2） | T20.1/T20.2/GAP-20a′/T20.4 降格 |
| campaign/lane_96_conjK.md（全文 292 行） | T96.1/T96.2/T96.3/GAP-96a/96b/96c |
| campaign/lane_102_gap96a.md（全文 234 行） | T102 族/L102.1/L102.6/T102.7/CORE-E/CHORD-E |
| campaign/lane_256_c236f_proof.md（全文 165 行 + REVISE×2） | 引理甲/乙/丙、命题 256.A、四角位、(H2) 守卫 |
| campaign/lane_260_muk3.md:25-50 | 引理 260.A |
| campaign/deep_V1_bridge.md（全文） | 链 A 权威提取 + V1 重验范围声明 |
| campaign/deep_V2_bridge_attack.md（全文） | 攻击审计 + 口径漂移登记 |
| campaign/deep_W1_lowermid.md（§0/§1/§3.2 + 结论行） | W1a.1 单调归约 |

---

## 1. 链提取：34 条承重蕴含清单

方向语义承 STATE §①：`X ⟸ Y` = Y 闭合则 X 获支撑。

### A. 装配主链（paper §7 直接承重，对应 ledger Edge 1-5 + Bridge）

| # | 蕴含 | paper 宿主 | 原始证明 | 承重前提 |
|---|---|---|---|---|
| L01 | K ⟹ Gallai | thm:Kgallai (:439-452) | lane_11:28-32 T11.2 | Π1（Lovász 全奇支） |
| L02 | BP-odd(Π2) ∧ SC-PH(Π4) ⟹ PH 对 | （T17.6，paper 经 thm:reduction 间接引用） | lane_17:125-140 | Π2∧Π4 |
| L03 | N*(Π3) ∧ SC-PH(Π4) ⟹ PH 对 | （T19.5，assembly 主支 :738-741） | lane_19:123-134 | Π3∧Π4 |
| L04 | PH 对 + A/B/mixed 分支(modulo J) + SC-PH ⟹ K 的 deg=2 层 | rem:moduloassembly「close the degree-two layer」 | lane_11 T11.4 + lane_16/17 五支表 | J(≤n−1) 强归纳接口 |
| L05 | GAP-20a′ ⟹ SC-PH | ledger Edge 3 (:605-614) | lane_20:58-89 T20.2 | 无（蕴含本身无条件） |
| L06 | (E) ∧ (R) ⟹ GAP-20a′ | ledger Edge 4 (:616-629) | lane_96:116-142 T96.2（内含 T96.1） | 无 |
| L07 | 森林域 (E)：T102.1/T102.2/T102.4 ⟹ 森林型 (E) 全解 | ledger Edge 5 (:631-648) | lane_102:38-42 | 无（域内） |
| L08 | 含圈域 (E) ⟸ C165.1（开放）= Π6 | ledger Edge 5 gap 行 | lane_171 收窄；机器背书 C157.1 | 开放（诚实登记） |
| L09 | (R) 的 3f≥k 残余 = Π7（[GAP-96b]） | ledger Edge 4 gap 行 | lane_96 §3.3 适用域 | 开放 |
| L10 | K 的 d≥4 层 = Π5（死区 42 例） | ledger Π5 (:685-686) | lane_11 §5.2 | 开放 |
| L11 | 266.3(so1) + C239.4 + 差分板 μ-充分性 + 类算术族 ⟹ (E) 侧（机器口径）= Π8 | ledger Bridge (:650-671) | lane_256/239/260/266 系 | 全部开放（登记「two-ended bridge」） |
| L12 | Π2 ⟹ Π3（单向；converse 被 super-tight 阻挡） | ledger 冗余注记一 (:695-700) | lane_19 T19.0 | — |
| L13 | Π4 ⟸ Π6∧Π7（经 L05+L06） | ledger 冗余注记二 (:701-703) | 组合 | — |
| L14 | Π8 路线在 Π6 存活时冗余 | ledger 冗余注记三 (:704-706) | 组合 | — |
| L15 | 266.3(so1) ∧ Π1..Π8 ⟹ Gallai（装配步本身） | thm:gallaimodulo (:712-730) | rem:moduloassembly 逐边读法 | 见 L01-L14 |

### B. 链内工具件（自身为承重蕴含/引理）

| # | 件 | 宿主 | 强度档 |
|---|---|---|---|
| L16 | lem:LB1（2\|D\|≥odd；D(v)≡deg(v) mod 2；混合分解版） | sec1-3:240-256 | folklore 自足 |
| L17 | lem:T1（吸收成本 = ⌈(d−μ*)/2⌉，操作类语义） | sec6-10:360-384 | 完全证明（操作类内） |
| L18 | prop:buried (i)(ii)(iii) | sec6-10:400-421 | 完全证明 |
| L19 | prop:Nequiv 第一句（\|E\|≥2k²+1 ⟺ 奇半团） | sec6-10:484-490 | 完全证明 |
| L20 | prop:Nequiv 第二句（T ⟺ B 双向等价断言） | sec6-10:490-495 | **断点 W-A330-1** |
| L21 | lem:walecki（划分 + 类对应） | sec1-3:360-396 | 完全证明 |
| L22 | T96.1（M-路径实现，升序版） | lane_96 §3.1 | 完全证明（排列版已被 T98.2 证伪——勘误在案） |
| L23 | T96.3（3f<k ⟹ (R) 自动） | lane_96 §3.3 | 完全证明 |
| L24 | L102.1（平移引理） | lane_102 §2 | 完全证明 |
| L25 | L102.6（单调性 + f=k−1 规范化） | lane_102 §2 | 完全证明 |
| L26 | T102.1/102.2/102.3/102.4（构造族） | lane_102 §3 | 完全证明 |
| L27 | T102.7（窗口障碍） | lane_102 §3.6 | 完全证明 |
| L28 | T17.5（紧奇阶偶点 ≥3，承 Π1） | lane_17:77-85 | 完全证明（承 Lovász） |
| L29 | T19.0/T19.1（N(k)⟺T(k)；m=2k² 层⟺Ham 划分） | lane_19 §1-2 | 完全证明 |
| L30 | 引理 260.A（k=3 可行 ⟺ 双足迹 val≤β） | lane_260 §3.1 | 完全证明（V2 攻击存活） |
| L31 | W1a.1（k=3 抽象定理 ⟺ β=1 档可行） | deep_W1a §3.2 | 完全证明 + 44,044 锚 |
| L32 | 命题 256.A（μ-判据 (a) 必要 (b) (H1)(H2)⟹全 μ-不等式 (c) 一般板反例） | lane_256 §3.4（含 (H2) 守卫 REVISE） | (a)(b) 严格、(c) 证书 |

### C. 底座

| # | 件 | 说明 |
|---|---|---|
| L33 | 266.3(so1) 强度注册 | thm:machM 三档（机器闭合/纸面候选/零外推宣称）+ so1 收窄=保守方向（sec6-10:717-724 自带澄清；与 STATE ⑤ so1 正典一致） |
| L34 | Π1（Lovász 1968 全奇支） | UNVERIFIED-external 承重件；五源陈述一致（EXTERNAL_P1）；本棒离线重构 = 骨架级（§4.9） |

---

## 2. 从零重推导：逐条判定（不看原证明先推，再对拍）

**总判定：34 条中 31 条独立重推成立；3 条为断点/表述问题（L20、L04 的登记面、Π3 叙述面），无一条蕴含方向错误。** 以下只列有关键内容的条目；「对拍」指本棒独立机检（§3）。

- **L01（T11.2）重推 ✓**。情形 1（存在偶度非孤立 x）：K 直接给 |D|≤⌈n/2⌉。情形 2（全奇）：握手引理 ⟹ n 偶；Π1 给 p+c≤n/2；混合分解上 L16(iii) 的模 2 账仍成立（圈对每点度贡献恒偶）⟹ 每奇点（全部 n 点）至少是一条路径的端点 ⟹ 2p ≥ n ⟹ p ≥ n/2；联立 ⟹ p=n/2、c=0 ⟹ p(G)≤n/2=⌈n/2⌉。**用法方向自足核验完成；承重外部件 = Π1 本体**。
- **L02（T17.6）重推 ✓**。紧 H（nH=2k+1, p=k+1），m≤2k²+k。情形 m≥2k²+1 ⟺ 补边 ≤k−1 ⟺ 半团 ⟹ SC-PH 逐字给出 μ*≥2；情形 m≤2k² ⟹ BP-odd 给 p≤k 与紧性矛盾 ⟹ 空。无洞。注意：T17.9 的双向等价已由 lane_19 T19.0 + W4c 修复降为条件等价（本重推确认降级正确）。
- **L03（T19.5）重推 ✓**。k≤3 支承批 K3 全普查（本棒机检 3 重跑确认：geng 2/21/853 图，m<2k²+1 域 p≤k 零反例，与 lane_19 计数一致）；k≥4 支 = N* 逆否直接给半团。**归纳接口澄清**：T11.4 情形 B 紧分支的排空实际用到 Gallai(n−2)（w₁ 叶 ⟹ H=G−x 含孤立点 w₁ ⟹ pn(H)=pn(H′)、H′ 有 n−2 点；p(H)=n/2 ⟹ pn(H′)=n/2>(n−2)/2=⌈(n−2)/2⌉ 违反 Gallai(n−2) ⟹ 空）——即 J 须按「对一切 ≤n−1 点」的强归纳读法；lane_11 文本记作 J(n−1)。数学无洞（强归纳惯例），但接口层数未在 paper 成文（并入 W-A330-2）。
- **L05（T20.2）重推 ✓ + 机检 2 端到端对拍**。构造 D={Q_ρ=C_ρ−e_ρ}∪{M}：件数 k+1；恰划分由「割边集 = F_ψ⊔E(M) 每类恰一」+ Walecki 划分；宿主引理（M-内点双宿主、割边端点圈件宿主）与路由四情形逐一对齐。**对拍中自揪 2 个实现层 bug（环切割自环、角色/顶点空间混叠），修复后 550/550 实例（k=5,6，f=0..k−1）验证+μ≥2 全过**。
- **L06（T96.2）重推 ✓**。(A)：条件 (3) 由「同一条边只有一个类」+ C_M=R_F^c 直接；条件 (4) 由 f+L=k 个互异类取遍 Z_k + 边-圈对应（L21）。(B)：情形 1（w₂∈FV）类互异直接；情形 2 需 ∃j≥1 使 m_j∉ψ(FV)——**T96.1 的互异性自动保证 m_j≠m₀（j≥1），原证明无须显式排除、无洞**（本棒机检 2 首版曾在此处自己写错，非原证明问题）。lane_96 §9 自报不确定性 2（类集大小核对）在 T96.2(A) 证明内已闭合（C_M 补集构造内建）。
- **L07（T102 族）重推 ✓ + 机检 4**。T102.1 双候选计数：自由候选 ≥ 2(k−m)−t ≥ 2k−3f+3−c ≥ 1（假设 3f+c≤2k+2），候选单射性由半坐标式 r≡a_x+a_y+ε_xε_y；T102.2 双壳打包的类计算（κ=0 无折返、κ=1 mod 2k 后同类）与角色不交逐行核；T102.7 的 ⌊·/2⌋ 计数（⌈m/2⌉+1 ≤ m−1）。**机检 4：121 型计数与 lane_102 V 批精确一致（3/7/15/31/65）；116 型构造直覆盖 + 5 条件外（≤ lane_102 的 23 型，方向更强）；L102.1 与 T102.7 全穷举零失败**。
- **L12（Π2⟹Π3）重推 ✓**。BP-odd 逆否于紧图：p=k+1>k ⟹ m≥2k²+1。单向性确认（与 W-A330-1 呼应）。
- **L16（LB1）重推 ✓**：deg_P(v)∈{0,1,2}、=1 ⟺ v 是端点；求和取模。混合分解版（圈贡献偶度）✓。机检 5 对拍（n≤5 全图 LB1(i)）。
- **L17（lem:T1）重推 ✓**：(≥) 方向「单路径吸双 spike 围圈非法」+ 新路径含 ≤2 spike ⟹ 下界；(≤) 匹配吸收+配对构造。操作类限定语（rem:T1scope）与 lane_11 T11.1 升级警告一致。
- **L18（prop:buried）重推 ✓ + 机检 5**：n≤5 全图全部偶点实例 2,342 组，(i) β≥deg/2+1、(ii) p=odd/2 ⟹ 无 D(x)≥2 分解、(iii) β≤pn+1，零失败。
- **L21（Walecki）+ L22（T96.1）重推 ✓ + 机检 1**：180,070 起点×类集实例零失败（划分性、类对应、(B1)(B2)、递推互异+类序列）。T96.1 升序证明的指标区间与 D∈[1,k−1] 界逐行核成立；排列版需「配对沿递增」条件（T98.2 勘误口径）——原报告注记已如实。
- **L23（T96.3）重推 ✓**：c↦2c+1−m₀ 单射（偶数像）；坏值 ≤2f（每角色至多坏一类）；k−f>2f ⟺ k>3f。
- **L28（T17.5）重推 ✓**：e 奇 + e=1 ⟹ odd=2k ⟹ Lovász p+c≤k 与端点账 2p≥2k 联立 ⟹ p=k 纯路径 ⟹ pn≤k 与紧矛盾。承 Π1。
- **L29（T19.0/T19.1）重推 ✓**：补边算术逐字；m=2k² 层 LB2 取等 ⟹ 全件 Ham。
- **L30（260.A）重推 ✓**：键像平移双射 c₂=c₁−δ₁₂、C₃ 取补集的逐条块族约束核验；「Fᵢ₃ 取 P 内部分即可」的注记正确（C₃⊆P）。
- **L31（W1a.1）重推 ✓ + 机检 5**：容量和 3p−|T∩P|≥p−1 ⟹ 贪心上增可达极大档；子集继承。N=6 全域 5,880 (H1)(H2) 实例零矛盾。
- **L32（256.A）重推 ✓**：(a) 可行块族限制到 S 色给出饱和 d(S) 行的匹配 ⟹ μ(S)≥d(S)；(b) |S|=1 整对角线匹配（(H1)）、|S|≥2 邻域⊇(R−t_{v₀})∖{0} ⟹ Hall 缺口 ≤1 ⟹ μ≥p−1≥n（(H2)）；(c) 2×2 反例违反差分规则（差分板中对角边必同色）——归约逻辑自洽。(H2) 守卫（REVISE R1，Z₁₄ 反例）语义确认。
- **L33（266.3(so1) 注册）✓**：prop:2663cand 全域候选与 thm:gallaimodulo 的 so1 切片使用之间，paper :717-724 自带「收窄=保守方向」澄清；与 STATE ⑤ so1 正典、deep_V2 §5 口径 2 一致。机器锚（β=2 档 4,309,308 + N=14 3,297,762 全空间扫）覆盖 so1 ⊂ 全域 ✓。
- **L08/L09/L10/L11（开放前提的登记）✓**：与 lane_171/GAP-96b/死区 42 例/lane_256 §3.4 落款逐条一致；Π8 冗余性（L14）诚实；「no so0-side account is registered separately in Section 6」字面核实为真。

---

## 3. 独立机检清单（全部本棒从零实现、零 import 战役代码；净域 /tmp/deepA33x/）

| # | 脚本 | 域与内容 | 命令 | 结果 |
|---|---|---|---|---|
| M1 | a330_walecki_t961.py | Walecki 划分+类对应+(B1)(B2)（k=2..10）；T96.1 全枚举（k=2..12，180,070 起点×类集实例） | `python3 a330_walecki_t961.py`（0.33s） | **fails=0** |
| M2 | a330_t962_e2e.py | T96.2+T20.2 端到端管线：solve_E→T96.1→路由→骨架构造→恰划分+简单性+μ≥2（k=5,6，f=0..k−1，550 实例） | `python3 a330_t962_e2e.py`（0.06s） | **fails=0** |
| M3 | a330_k3tight.py | k≤3 紧图普查：geng -c 2/21/853 图，m<2k²+1 域 p≤k 判定 | `python3 a330_k3tight.py`（1.0s） | **反例 0**（计数与 lane_19 批 K3 一致） |
| M4 | a330_t102.py | (E) 森林域 121 型构造覆盖 + L102.1 平移穷举 + T102.7 窗口障碍穷举 | `python3 a330_t102.py`（0.27s） | **计数精确一致；L102.1/T102.7 fails=0** |
| M5 | a330_misc.py | prop:buried(i)(ii)(iii)+LB1(i)（n≤5 全图 2,342 偶点实例）；猜想 K 下探（n≤5 零违反）；W1a.1 N=6 全域 5,880 实例 | `python3 a330_misc.py`（16.6s） | **全部零失败** |
| M6 | a330_cut.py | 割点支：连通域（geng -c）deg=2 割点实例 β≤⌈n/2⌉（n≤7，106 实例） | `python3 a330_cut.py`（0.21s） | **违反 0** |

**机检自身勘误记录（默认自己有错的纪律实录，全部修复后重跑才算数）**：
1. M1/M2 首版环切割把圈序列首尾 Inf 相接产出自环假边——修复为环旋转构造；
2. M2 首版角色/顶点空间混叠 + 起点自由情形 m₀ 指派缺失——修复；
3. M3/M6 首版 graph6 解码位序反（graph6 上三角为**列主序**，本棒初写为行主序）——**M3 第一版「全过」因此无效，修复后重跑的版本才是有效验证**；与 networkx 官方解析逐图对拍一致后才采信；
4. M6 首版割点判定条件方向写反 + beta 的 seen 字典跨 k 循环未重置——修复；
5. M6 曾以无连通过滤的标定域跑出 60 例「K 违反」，逐例核验全部为**不连通图**（K 只对连通 G 陈述）——假警报，未据此写任何正典改动，连通域重跑归零。此条为本棒「假 RED 警报如实 discharge、未写 STOP」的留痕。

---

## 4. 断点判定（全部 verbatim）

**无实质断点**（没有任何一条洞影响蕴含方向或前提真实性）。坐实 **3 处表述/登记层断点**：

### W-A330-1（minor·表述层·同节自相矛盾）：prop:Nequiv 第二句的「equivalent」过强

- **位置**：paper/sec6-10.tex:487-490（陈述）+ :495（证明）。
- **verbatim**：`:490`「Consequently, the statement ``every tight connected graph on $2k+1$ vertices is an odd semi-clique'' is equivalent to ``every connected graph on $2k+1$ vertices with $|E|\le2k^2$ satisfies $\pn\le k$''.」；`:495`「The second statement is its contrapositive form.」
- **性质**：「紧⟹半团」（T）的逆否只给「|E|≤2k² ⟹ pn≠k+1」；由此推「pn≤k」必须排除 super-tight（pn≥k+2）图，即需要 **Gallai(2k+1)**——而 §7 开篇自述「deliberately conditional: nothing here assumes Gallai's conjecture」（:349）。同节 ：695-698 冗余注记自己写明「Π2 implies Π3 — one implication, not an equivalence (the converse is blocked by the possible ``super-tight'' $p\ge k+2$ graphs, which would be a Gallai event rather than a pair-hosting event)」——**同一小节两处口径直接冲突**。无条件成立的方向是 B⟹T；T⟹B 携带 Gallai(2k+1)。
- **波及面**：**装配不承重错误方向**——thm:reduction 用 T 形式前提（Π3/conj:N 直接是「紧⟹半团」），ledger 注记用 BP-odd⟹N 单向；paper 内无任何推导经过「T⟹B」。故为纯陈述层缺陷。
- **修复候选**：① :490 改为「the second statement implies the first; the converse requires Gallai(2k+1)」并同步改 :495 证明行；②或按 lane_19 T19.0 的无损形态重述（该形态已被 W4c 修复 6/7 审计确认）。campaign 侧（lane_17:343 REVISE R1、lane_19:41）已坐实同一问题并修复，paper 正文未同步——属转录滞后。

### W-A330-2（minor·登记层·前提清单低估残域）：Π5 未覆盖 deg=2 链内部的割点支；「every case is settled except one」超前

- **位置**：paper/sec6-10.tex:685-686（Π5 陈述）、:741-742（rem:moduloassembly）、:532-536（§7.4 remark）；对照 lane_11 §4.3/§6 遗留 4、lane_17 §3 五支表分支 5。
- **verbatim**：`:685-686`「\item \emph{(open)} the surviving layers of Conjecture~$K$: the $d\ge4$ layers not covered by the degree-two chain (dead zone, $42$ recorded instances);」；`:533-536`「every case is settled except one: when $G-x$ is tight on an odd number of vertices and its optimal decompositions host the two neighbours of $x$ only on a common path.」
- **性质**：deg=2 层的组装（T11.4）除 C3 紧奇阶分支（由 PH 对经 L04 闭合）外，**割点支（G−x 不连通）只有计算级闭合**（lane_11 批 L 1870 例 0 违反；lane_17 五支表分支 5 自记「计算级闭合（1870 例 0 违反），定理化待做」）。paper 的 Π5 只登记 d≥4 层，rem:moduloassembly 声称「Edge 2 … close the degree-two layer of K; Π5 supplies the remaining layers of K」——按 paper 自己的审计标准（每条边带验证级），deg=2 层内的割点支缺口未入账，「every case is settled except one」对割点支超前。另：情形 B 紧分支的强归纳接口（J 需读到 Gallai(n−2)，见 §2 L03 条）未成文。
- **本棒补充（降低修复成本）**：割点支其实可以 10 行定理化（modulo 强归纳 J）：x 割点 ⟹ G−x 恰两分量 H₁⊔H₂（n₁+n₂=n−1 一奇一偶）。双非叶：两条 spike 各接各分量宿主路径（宿主由 LB3/归纳 K(Hᵢ,wᵢ) 保证）⟹ |D|=|D₁|+|D₂| ≤ ⌈n₁/2⌉+⌈n₂/2⌉ = n/2 = B 且 D(x)=2 ✓；单叶（w₁ 叶 ⟹ H₁={w₁} 单点）：xw₁ 单边 + xw₂ 吸收 ⟹ ≤ ⌈n₂/2⌉+1 = B ✓；双叶 ⟹ G=P₃，β=2=B ✓。**机检 6（连通域 n≤7 全部 106 个 deg=2 割点实例 β≤⌈n/2⌉ 零违反）与该构造方向一致**。
- **波及面**：thm:gallaimodulo 的前提完备性声明；不改变任何已证蕴含，修复后链不变。
- **修复候选**：①把上述 10 行组装写成引理（登记定理级）；②或 Π5 重述为「d≥4 死区 + deg=2 割点支」；③或在 Edge 2 的 Gap 行增列割点支验证级。

### W-A330-3（minor·叙述层·勘前口径残留）：Π3 支撑叙述的「19% short」与 appendix 分层记账结论方向不一致

- **位置**：paper/sec6-10.tex:543-545（conj:N 后 remark）与 :681-683（Π3 三行式）；对照 paper/appendix.tex:200-204 与 lane_19 REVISE R2。
- **verbatim**：`:681-683`「(theorem at $k\le3$; computational at $k=4,5$ --- with the $k=4$ pipeline domain of $210{,}864$ graphs running about $19\%$ short of the accepted census total $261{,}080$ (OEIS A001349), the bookkeeping discrepancy registered in Appendix~\ref{app:comp}; open at $k\ge6$)」
- **性质**：lane_19 REVISE R2（deep_W3b §1 geng 实测）已坐实：全域 261,080 = m≤15 DP 层 50,216 + m≥16 witness 层 210,864，**内部自洽、k=4 为完全裁决**；appendix.tex:200-204 也已按此口径写（「The difference, 50,216, equals exactly the size of the archived low-edge layer … rather than a demonstrated coverage gap」）。但正文两处仍按勘前口径把 210,864 描述为「19% short / discrepancy」——按字面读会得出「k=4 有 19% 域未扫」的错误弱化读法，与 appendix 自己的结论方向相反。
- **波及面**：Π3 证据叙述的强度评估（误导低估）；Π3 陈述本身（「computational at k=4,5」）与 k=4 完全裁决的事实不受影响。
- **修复候选**：正文两处改写为「the archived pipeline records the m≥16 subdomain (210,864) alongside the low-edge DP layer (50,216); the two sum to the census total 261,080, so the k=4 adjudication covers the full census domain」。

---

## 5. 八前提（Π1..Π8）表述真实性核验

| 前提 | paper 陈述位置 | 与数学内容一致性 | 判定 |
|---|---|---|---|
| Π1 | :674-676 | 「the all-odd branch of Theorem lovasz as used in thm:Kgallai」——与 T11.2 情形 2 的实际用法逐字一致；UNVERIFIED-external 落款如实 | ✓（本体承重见 §4.9） |
| Π2 | :677-679 | BP-odd 陈述与 lane_17 T17.6 定义一致；「odd-order, tightness-special case of Question 1.1 of BP19」的定位准确（Q1.1 例外类=奇半团 ⟺ m≥2k²+1） | ✓ |
| Π3 | :680-683 | 陈述「N(k≥4) at k≥4」T 形式正确；k≤3 定理/k=4,5 计算级/k≥6 开放的档位与勘后口径一致；但支撑叙述「19% short」残留勘前口径（**W-A330-3**） | ✓陈录/△叙述 |
| Π4 | :684 | 与 conj:SCPH 一致（μ*≥2 ⟺ ≤k+1 件分解中 w₁,w₂ 异件端点；lane_20 注记 0.1 的「非孤立自动满足」在半团域成立，min 度 ≥k+1≥2） | ✓ |
| Π5 | :685-686 | 陈述为「d≥4 层」——**低估 deg=2 层内部割点支残域**（**W-A330-2**） | △ |
| Π6 | :687-689 | (E) 一般可解性 + C165.1 开放 + 机器背书口径与 Edge 5 一致（C192.1 ⛔ 2,880 证书、「树+圈」口号半假的勘误口径已带入） | ✓ |
| Π7 | :690 | (R) 3f≥k 域 [GAP-96b] 与 lane_96 §3.3 适用域一致 | ✓ |
| Π8 | :691-692 | C239.4 + 差分板 μ-充分性抽象定理 + (E) 类算术族纸面层——与 lane_256 §3.4 落款（(H2) 守卫后）及 lane_239 状态一致；「bridge, open」档位诚实 | ✓ |
| 合取使用 | :712-730 | 前件=266.3(so1)∧Π1..Π8；Π2/Π8 冗余已登记（:694-708）；强度声明段（:747-757）「every one of the eight conjuncts … open conjecture or unverified external step」全称核实为真 | ✓ |

无偷换量词/域：Π1-Π8 的量词域（连通、奇阶、k 范围、3f≥k）逐一与各自 lane 原件对齐；so1 收窄在 thm:gallaimodulo 的 gloss 内自带澄清且方向保守。

---

## 6. Π1（Lovász 全奇支）离线证明重构——骨架级，卡点如实定位

按任务书对 EXTERNAL_P1 §五遗留动作的执行结果：

1. **陈述层**：EXTERNAL_P1 五源引文逐字复读一致（Bryant 2019 / Bonamy–Perrett 2016 / Anto–Basavaraju 2023 / Montgomery 2022 / MO #97683：均口径「⌊n/2⌋ paths and cycles」）。paper thm:lovasz 陈述（sec1-3:276-279）与该口径一致。
2. **重构尝试记录**：本棒从零推了两条路线——
   - **偶点删除归纳 + 端点控制强化陈述**：叶/孤立点情形自足闭合（含 n 奇叶情形的「(n+1)/2−1」件数账）；**卡点 = 无叶无孤立图中偶度点 x 的 d 条 spike 回插**——宿主预算不受 L16 控制的邻居（G-奇点在 G′ 中偶度、D′(w) 可为 0）需要「双候选/吸收配对」机制，其 simplicity 控制（挂接路径与宿主路径顶点重叠 ⟹ 闭 walk ⟹ 拆圈增件）无法在不引入 Fan 型引擎的情况下闭合；
   - **全奇子定理直攻（最长圈剥离 + 挂接吸收）**：剥圈保奇性成立，但拆出的路径两端挂接回分量分解时同样撞 simplicity 墙。
3. **定位**：两条路线的卡点与 paper rem:T1scope 自记的三堵墙（Lovász-style reinsertion gap / parity wall / **simplicity wall of Fan's Lemma fan6**）同构——这恰是旁证：Lovász 定理的完整证明正是战役「端点控制」困难的源头，Π1 的 UNVERIFIED-external 承重定位诚实且不可离线廉价清偿。
4. **裁定（诚实档位）**：Π1 离线重构达到**骨架级**（全奇支的用法方向——端点计数 ⟹ p=n/2 纯路径——已自足重推+机检对拍；分解存在性本体承五源一致的 58 年经典 + 全部后续 Gallai 文献承重）。完整逐行重构未达成，**如实登记**；逐页对读仍需终审在场执行（EXTERNAL_P1 遗留动作第一项保持 open）。

---

## 7. 信心分级汇总

| 级 | 条目 | 依据 |
|---|---|---|
| 高（纸面重推+独立机检双验） | L05, L06, L21, L22, L23, L24, L26, L27, L18, L31, M3 支撑的 L03-k≤3 支 | §2+§3 |
| 高（纸面重推+机器行为方向一致） | L01, L03, L04(构造面), L16, L19, L29, L30 | §2+机检 5/6 |
| 中高（短证明纯逻辑重推，未单独立机检） | L02, L07(定理部分), L12, L13, L14, L15, L17, L20(第一句), L25, L28, L32, L33 | §2 |
| 登记态（开放前提，重验=登记一致性） | L08, L09, L10, L11 | §5 |
| 承外部（骨架级重构） | L34（Π1） | §6 |

---

## 8. 六不宣称照录（FRONTIER REVISE-71 + 承前）

不宣称 T-μ-k2 已证／K₈@28 已定理化／𝓔 三点为正典全域刻画／Kₙ@T(n−1) 规律已证／[P4′] 纸面成立／A322.L 纸面全证；承前六不维持。本棒全程未宣称：猜想 K 已证、SC-PH/GAP-20a′/(E)/(R) 已证、266.3(so1) 纸面已证、Gallai 任何逼近意义上的进展；won≠定理。

## 9. 纪律留痕

- 全程离线；零联网。正典零写：STATE.md / FRONTIER.md / main_submission.tex 及卫星 / lean / delivery_v24_final / STOP 全程只读未触碰。
- 写盘仅两处：本报告（经 /tmp/deepA33x/deep_A330_kverify.md + os.replace 原子落盘）与净域 /tmp/deepA33x/（a330_ 前缀 8 个脚本 + 日志）。
- 单命令 ≤60s 纪律：M5/M6 两次超预算运行移入后台并如实留痕（9m21s / 0.2s），无前台超时。
- 假警报处置：M6 无连通过滤版曾产 60 例假「K 违反」，逐例核验为不连通图后 discharge，未写 STOP、未入任何正典。

## 10. 深度平面结论

verdict = **won**（保守读法 partial 偏 won：若终审要求「断点=任何缺陷」，则按 3 处 minor 表述断点记 partial——本棒按任务书「断点比 PASS 更有价值」的语义，将 3 处断点 verbatim 全量交付，链本体 31/34 条独立重推成立、6 组机检零失败、无实质数学洞，判 won）。

- **链的本体**：K 线全部承重蕴含（T11.2 / T17.6 / T19.5 / T20.2 / T96.1-3 / T102 族 / Walecki / 260.A / W1a.1 / 256.A）从零重推成立；机检 180,070 + 550 + 876 图 + 121 型 + 2,342 + 5,880 + 106 实例零失败。
- **断点三件（全 minor、全在 paper 表述/登记层）**：W-A330-1（prop:Nequiv「equivalent」过强+同节自相矛盾）、W-A330-2（Π5 漏 deg=2 割点支+「every case is settled except one」超前）、W-A330-3（Π3「19% short」勘前口径残留）。修复候选均给出，成本为小时级文字手术，零数学风险。
- **Π1**：离线重构骨架级（卡点=simplicity 控制，与战役三堵墙同构）；完整重构维持终审在场义务。

*报告完（deep_A330_kverify，2026-10-10）。机检脚本与全部中间输出在 /tmp/deepA33x/。*

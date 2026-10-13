import Front583.K4nMain
import Front583.T272

/-!
# front583 / lane_57：T27.3 一般上界构造的形式化（对一切 k ≥ 6，即奇 n ≥ 13）

把 lane_27 T27.3（闭环式构造：n=7 gadget 四条 7-路 + k−3 条偶循环 8-路）
以一般 k 形式化，补上 `pNumK4n_eq_half_of_le`（K4nMain.lean）缺失的唯一前提
`pNumK4n n ≤ (n+1)/2`，闭合「对一切奇 n ≥ 3，p(K_{4,n}) = (n+1)/2」。

**构造**（lane_27 报告 §4 / src/lane27_k4odd.py closed_form 的逐字镜像）：
n = 2k+1，k ≥ 6。B 侧拆为 S = b₀..b₆（7 个核心 B）∪ R（m = 2k−6 个环 B，
r(i) = b_{7+i mod m}）。

- 四条 gadget 路（7 边，只用 S）：
  g1 = a₀ s₀ a₁ s₁ a₂ s₂ a₃ s₃ 等（§2 常量，与 lane_27 G1..G4 一致）；
- k−3 条环路（8 边，只用 R）：
  Q_t = r(2t) a₀ r(2t+1) a₁ r(2t+2) a₂ r(2t+3) a₃ r(2t+4)，t = 0..k−4。

**编码要点**：顶点函数 `gv k i : Fin (2*k+5)`（截断式，min 内建）；
所有路径先在 Nat 值级定义，经 `map (gv k)` 升到 Fin 级；
三件套镜像引理（eInB / distinctB / chainOk 的 map-gv 迁移）把全部有限检查
（gadget 的 decide 格）与算术论证（环路的 mod 计数）都化到 Nat 级。
全部逐例事实（gadget 覆盖格 4×7、gadget 两两不交格 4×4×4×7）由 decide 机检，
一般算术事实（五连续下标 mod m 互异、mod-2 唯一性给环路两两不交、
鸽笼式覆盖查找）由 omega + 自制 mod 两块引理支撑。

**主结果**：
- `generalDecomp_valid`：k ≥ 6 时 generalDecomp k 是 K_{4,2k+1} 的路分解；
- `generalDecomp_len`：路数 = k+1；
- `pNumK4n_ge13`：p(K_{4,2k+1}) = k+1（k ≥ 6，即奇 n ≥ 13）；
- `pNumK4n_odd_all`：**主定理**——对一切奇 n ≥ 3，pNumK4n n = (n+1)/2
  （n ≤ 11 走 K4nMain.pNumK4n_odd_le17 逐例，n ≥ 13 走一般构造）。
-/

namespace Front583

/-! ## §0 基建：gv 顶点函数与镜像引理 -/

/-- 值 i 的 Fin (2*k+5) 顶点：截断到合法范围（界由镜像引理的 all-假设承担）。 -/
def gv (k i : Nat) : Fin (2 * k + 5) := ⟨min i (2 * k + 4), by omega⟩

theorem gv_val (k i : Nat) : (gv k i).val = min i (2 * k + 4) := rfl

theorem gv_eq_self (k i : Nat) (h : i < 2 * k + 5) : (gv k i).val = i :=
  Nat.min_eq_left (by omega)

theorem gv_eq (k a b : Nat) (ha : a < 2 * k + 5) (hb : b < 2 * k + 5) :
    (gv k a = gv k b) ↔ a = b := by
  constructor
  · intro hc
    have hv := congrArg Fin.val hc
    rwa [gv_eq_self k a ha, gv_eq_self k b hb] at hv
  · intro hc
    rw [hc]

theorem decide_gv_eq (k i : Nat) (h : i < 2 * k + 5) (x : Fin (2 * k + 5)) :
    decide (gv k i = x) = decide (i = x.val) := by
  have key : (gv k i = x) ↔ (i = x.val) := by
    constructor
    · intro hc
      have hv := congrArg Fin.val hc
      rwa [gv_eq_self k i h] at hv
    · intro hc
      refine Fin.val_inj.mp ?_
      show min i (2 * k + 4) = x.val
      rw [hc]
      exact Nat.min_eq_left (by omega)
  by_cases hc : i = x.val
  · rw [key.mpr hc]
    simp [hc]
  · rw [decide_eq_false (fun hh => hc (key.mp hh)), decide_eq_false hc]

theorem decide_gv_gv (k a b : Nat) (ha : a < 2 * k + 5) (hb : b < 2 * k + 5) :
    decide (gv k a = gv k b) = decide (a = b) := by
  by_cases hc : a = b
  · simp [hc]
  · rw [decide_eq_false (fun hh => hc ((gv_eq k a b ha hb).mp hh))]
    rw [decide_eq_false hc]

/-- 任一 Fin 顶点等于其值处的 gv。 -/
theorem eq_gv_self (k : Nat) (x : Fin (2 * k + 5)) : x = gv k x.val :=
  Fin.val_inj.mp (by rw [gv_eq_self k x.val x.isLt])

theorem memB_map_gv (k : Nat) {i : Nat} (hi : i < 2 * k + 5) : ∀ (L : List Nat),
    ((L.all fun j => decide (j < 2 * k + 5)) = true) →
    memB (gv k i) (L.map (gv k)) = memB i L := by
  intro L
  induction L with
  | nil => intro _; rfl
  | cons j t ih =>
      intro h
      have hj : j < 2 * k + 5 := decide_eq_true_iff.mp ((List.all_eq_true.mp h) j (by simp))
      have ht : ((t.all fun j => decide (j < 2 * k + 5)) = true) := by
        refine List.all_eq_true.mpr fun a ha => ?_
        exact (List.all_eq_true.mp h) a (by simp [ha])
      show (decide (gv k i = gv k j) || memB (gv k i) (t.map (gv k))) = _
      rw [decide_gv_gv k i j hi hj, ih ht]
      rfl

theorem distinctB_map_gv (k : Nat) : ∀ (L : List Nat),
    ((L.all fun j => decide (j < 2 * k + 5)) = true) →
    distinctB (L.map (gv k)) = distinctB L := by
  intro L
  induction L with
  | nil => intro _; rfl
  | cons a t ih =>
      intro h
      have ha : a < 2 * k + 5 := decide_eq_true_iff.mp ((List.all_eq_true.mp h) a (by simp))
      have ht : ((t.all fun j => decide (j < 2 * k + 5)) = true) := by
        refine List.all_eq_true.mpr fun b hb => ?_
        exact (List.all_eq_true.mp h) b (by simp [hb])
      show ((!memB (gv k a) (t.map (gv k)) && distinctB (t.map (gv k)))
        = (!memB a t && distinctB t))
      rw [memB_map_gv k ha t ht, ih ht]

/-- Nat 级邻接的 Bool 镜像（K4nAdj 的 val 层）。 -/
def adjBN (a b : Nat) : Bool := (a < 4 && 4 ≤ b) || (b < 4 && 4 ≤ a)

theorem adjBN_AB (a b : Nat) (ha : a < 4) (hb : 4 ≤ b) : adjBN a b = true := by
  simp [adjBN, ha, hb]

theorem adjBN_BA (a b : Nat) (ha : a < 4) (hb : 4 ≤ b) : adjBN b a = true := by
  simp [adjBN, ha, hb]

theorem chainOk_map_gv (k : Nat) : ∀ (L : List Nat),
    ((L.all fun j => decide (j < 2 * k + 5)) = true) →
    chainOk (fun (u v : Fin (2 * k + 5)) => adjBN u.val v.val) (L.map (gv k))
      = chainOk adjBN L
  | [], _ => rfl
  | [_], _ => rfl
  | a :: b :: r, h => by
      have ha : a < 2 * k + 5 := decide_eq_true_iff.mp ((List.all_eq_true.mp h) a (by simp))
      have hb : b < 2 * k + 5 := decide_eq_true_iff.mp ((List.all_eq_true.mp h) b (by simp))
      have hr : (((b :: r).all fun j => decide (j < 2 * k + 5)) = true) := by
        refine List.all_eq_true.mpr fun c hc => ?_
        exact (List.all_eq_true.mp h) c (by simp [hc])
      show (adjBN (gv k a).val (gv k b).val && chainOk _ ((b :: r).map (gv k))) = _
      rw [gv_eq_self k a ha, gv_eq_self k b hb]
      exact congrArg _ (chainOk_map_gv k (b :: r) hr)

theorem eInB_map_gv (k : Nat) : ∀ (L : List Nat),
    ((L.all fun j => decide (j < 2 * k + 5)) = true) →
    ∀ (x y : Fin (2 * k + 5)), eInB (L.map (gv k)) x y = eInB L x.val y.val
  | [], _, _, _ => rfl
  | [_], _, _, _ => rfl
  | a :: b :: r, h, x, y => by
      have hr : (((b :: r).all fun j => decide (j < 2 * k + 5)) = true) := by
        refine List.all_eq_true.mpr fun c hc => ?_
        exact (List.all_eq_true.mp h) c (by simp [hc])
      have ha : a < 2 * k + 5 := decide_eq_true_iff.mp ((List.all_eq_true.mp h) a (by simp))
      have hb : b < 2 * k + 5 := decide_eq_true_iff.mp ((List.all_eq_true.mp h) b (by simp))
      show (((decide (gv k a = x) && decide (gv k b = y)) ||
        (decide (gv k a = y) && decide (gv k b = x))) ||
        eInB ((b :: r).map (gv k)) x y) = _
      rw [decide_gv_eq k a ha x, decide_gv_eq k b hb y, decide_gv_eq k a ha y,
        decide_gv_eq k b hb x, eInB_map_gv k (b :: r) hr x y]
      rfl

/-- EIn 的换向。 -/
theorem EIn_swap {V : Type} : ∀ (l : List V) (x y : V), EIn l x y → EIn l y x
  | [], _, _, h => h.elim
  | [_], _, _, h => h.elim
  | u :: v :: r, x, y, h => by
      rcases h with h | h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inl h
      · exact Or.inr (Or.inr (EIn_swap (v :: r) x y h))

/-- eInB（Nat 级）给出相邻对成员身份。 -/
theorem eInB_mem_pairs {a b : Nat} : ∀ (L : List Nat),
    eInB L a b = true → ((a, b) ∈ pairsOf L ∨ (b, a) ∈ pairsOf L) := by
  intro L h
  exact EIn_mem_pairsOf L (eInB_true L h)

/-- 相邻对成员身份给出 eInB（Nat 级）。 -/
theorem pairs_mem_eInB {a b : Nat} : ∀ (L : List Nat),
    ((a, b) ∈ pairsOf L ∨ (b, a) ∈ pairsOf L) → eInB L a b = true := by
  intro L h
  rcases h with h | h
  · exact EIn_true_eInB _ (pairsOf_pair_EIn L a b h)
  · exact EIn_true_eInB _ (EIn_swap L b a (pairsOf_pair_EIn L b a h))

/-- EIn 经 map gv 提升（Nat 级 → Fin 级）。 -/
theorem EIn_map_gv (k : Nat) : ∀ (L : List Nat),
    ((L.all fun j => decide (j < 2 * k + 5)) = true) →
    ∀ (a b : Nat), EIn L a b →
      EIn (L.map (gv k)) (gv k a) (gv k b)
  | [], _, _, _, h => h.elim
  | [_], _, _, _, h => h.elim
  | u :: v :: r, hbd, a, b, h => by
      have hr : (((v :: r).all fun j => decide (j < 2 * k + 5)) = true) := by
        refine List.all_eq_true.mpr fun c hc => ?_
        exact (List.all_eq_true.mp hbd) c (by simp [hc])
      have hu : u < 2 * k + 5 := decide_eq_true_iff.mp ((List.all_eq_true.mp hbd) u (by simp))
      have hv : v < 2 * k + 5 := decide_eq_true_iff.mp ((List.all_eq_true.mp hbd) v (by simp))
      rcases h with h | h | h
      · refine Or.inl ⟨?_, ?_⟩
        · exact (gv_eq k u a hu (by omega)).mpr h.1
        · exact (gv_eq k v b hv (by omega)).mpr h.2
      · refine Or.inr (Or.inl ⟨?_, ?_⟩)
        · exact (gv_eq k u b hu (by omega)).mpr h.1
        · exact (gv_eq k v a hv (by omega)).mpr h.2
      · exact Or.inr (Or.inr (EIn_map_gv k (v :: r) hr a b h))

/-- mod 两块引理：m ≤ x < 2m 时 x % m = x − m。 -/
theorem mod_two_block (m x : Nat) (hm : 0 < m) (h1 : m ≤ x) (h2 : x < m + m) :
    x % m = x - m := by
  have key := Nat.div_add_mod x m
  have hq2 : x / m < 2 := by
    refine Nat.div_lt_of_lt_mul ?_
    omega
  rcases Nat.eq_zero_or_pos (x / m) with h0 | hp
  · rw [h0, Nat.mul_zero] at key
    have hlt : x % m < m := Nat.mod_lt x hm
    omega
  · have h1' : x / m = 1 := by omega
    rw [h1', Nat.mul_one] at key
    omega

/-! ## §1 构造定义（Nat 值级 + Fin 级） -/

/-- gadget G1 = a₀ s₀ a₁ s₁ a₂ s₂ a₃ s₃（lane_27 §4 G1）。 -/
def gN1 : List Nat := [0, 4, 1, 5, 2, 6, 3, 7]

/-- gadget G2 = a₁ s₂ a₀ s₃ a₂ s₀ a₃ s₁。 -/
def gN2 : List Nat := [1, 6, 0, 7, 2, 4, 3, 5]

/-- gadget G3 = a₂ s₄ a₁ s₅ a₃ s₆ a₀ s₁。 -/
def gN3 : List Nat := [2, 8, 1, 9, 3, 10, 0, 5]

/-- gadget G4 = a₃ s₄ a₀ s₅ a₂ s₆ a₁ s₃。 -/
def gN4 : List Nat := [3, 8, 0, 9, 2, 10, 1, 7]

/-- gadget 选择器（用于一般化陈述）。 -/
def gsel (i : Nat) : List Nat :=
  match i with
  | 0 => gN1
  | 1 => gN2
  | 2 => gN3
  | _ => gN4

/-- 环 B 的个数：m = 2k−6（k ≥ 6 时为正偶数）。 -/
def mR (k : Nat) : Nat := 2 * k - 6

/-- 环路 Q_t 的值序列（lane_27 closed_form 的逐字镜像）。 -/
def qN (k t : Nat) : List Nat :=
  [11 + (2 * t + 0) % mR k, 0, 11 + (2 * t + 1) % mR k, 1,
    11 + (2 * t + 2) % mR k, 2, 11 + (2 * t + 3) % mR k, 3,
    11 + (2 * t + 4) % mR k]

/-- gadget 组（Nat 级）。 -/
def gNlist : List (List Nat) := [gN1, gN2, gN3, gN4]

/-- 环路组（Nat 级）：t = 0..k−4 共 k−3 条。 -/
def ringN (k : Nat) : List (List Nat) := (List.range (k - 3)).map (qN k)

/-- 全部分解（Nat 级）。 -/
def allN (k : Nat) : List (List Nat) := gNlist ++ ringN k

/-- 值级路径升到 Fin (2*k+5)。 -/
def gvL (k : Nat) (L : List Nat) : List (Fin (2 * k + 5)) := L.map (gv k)

/-- gadget 组（Fin 级）。 -/
def GsF (k : Nat) : List (List (Fin (2 * k + 5))) := gNlist.map (gvL k)

/-- 环路组（Fin 级）。 -/
def ringsF (k : Nat) : List (List (Fin (2 * k + 5))) := ringN k |>.map (gvL k)

/-- **一般上界构造（T27.3）**：k ≥ 6 时为 K_{4,2k+1} 的 k+1 条路分解。 -/
def generalDecomp (k : Nat) : List (List (Fin (2 * k + 5))) := GsF k ++ ringsF k

/-! ## §2 gadget 有限事实（Nat 级 decide 机检） -/

theorem gN1_props : distinctB gN1 = true ∧ chainOk adjBN gN1 = true := by decide
theorem gN2_props : distinctB gN2 = true ∧ chainOk adjBN gN2 = true := by decide
theorem gN3_props : distinctB gN3 = true ∧ chainOk adjBN gN3 = true := by decide
theorem gN4_props : distinctB gN4 = true ∧ chainOk adjBN gN4 = true := by decide

theorem gsel_props (i : Nat) (hi : i < 4) :
    distinctB (gsel i) = true ∧ chainOk adjBN (gsel i) = true := by
  rcases i with _ | _ | _ | _ <;> simp [gsel] at hi ⊢ <;>
    exact gN1_props <;> exact gN2_props <;> exact gN3_props <;> exact gN4_props

/-- gadget 值全部 ≤ 10。 -/
theorem gsel_le10 (i : Nat) (hi : i < 4) :
    ((gsel i).all fun v => decide (v ≤ 10)) = true := by
  rcases i with _ | _ | _ | _ <;> simp [gsel] at hi ⊢ <;> decide

/-- gadget 值全部落在 Fin (2*k+5) 范围内。 -/
theorem gsel_bounds (k i : Nat) (hk : 3 ≤ k) (hi : i < 4) :
    ((gsel i).all fun j => decide (j < 2 * k + 5)) = true := by
  refine List.all_eq_true.mpr fun v hv => ?_
  have h10 := decide_eq_true_iff.mp
    ((List.all_eq_true.mp (gsel_le10 i hi)) v hv)
  exact decide_eq_true_iff.mpr (by omega)

/-- gadget 相邻对的形状：一端 A（<4）、另一端 S（4..10）。 -/
theorem gsel_pair_bound_all (i : Nat) (hi : i < 4) :
    ((pairsOf (gsel i)).all fun p =>
      decide (p.1 < 4 ∧ 4 ≤ p.2 ∧ p.2 < 11 ∨ p.2 < 4 ∧ 4 ≤ p.1 ∧ p.1 < 11)) = true := by
  have h1 : ((pairsOf gN1).all fun p =>
      decide (p.1 < 4 ∧ 4 ≤ p.2 ∧ p.2 < 11 ∨ p.2 < 4 ∧ 4 ≤ p.1 ∧ p.1 < 11)) = true := by
    decide
  have h2 : ((pairsOf gN2).all fun p =>
      decide (p.1 < 4 ∧ 4 ≤ p.2 ∧ p.2 < 11 ∨ p.2 < 4 ∧ 4 ≤ p.1 ∧ p.1 < 11)) = true := by
    decide
  have h3 : ((pairsOf gN3).all fun p =>
      decide (p.1 < 4 ∧ 4 ≤ p.2 ∧ p.2 < 11 ∨ p.2 < 4 ∧ 4 ≤ p.1 ∧ p.1 < 11)) = true := by
    decide
  have h4 : ((pairsOf gN4).all fun p =>
      decide (p.1 < 4 ∧ 4 ≤ p.2 ∧ p.2 < 11 ∨ p.2 < 4 ∧ 4 ≤ p.1 ∧ p.1 < 11)) = true := by
    decide
  rcases i with _ | _ | _ | _
  · simpa [gsel] using h1
  · simpa [gsel] using h2
  · simpa [gsel] using h3
  · simpa [gsel] using h4

theorem gsel_pair_bound (i : Nat) (hi : i < 4) {a b : Nat}
    (h : eInB (gsel i) a b = true) :
    (a < 4 ∧ 4 ≤ b ∧ b < 11) ∨ (b < 4 ∧ 4 ≤ a ∧ a < 11) := by
  rcases eInB_mem_pairs (gsel i) h with hm | hm
  · exact decide_eq_true_iff.mp
      ((List.all_eq_true.mp (gsel_pair_bound_all i hi)) (a, b) hm)
  · rcases decide_eq_true_iff.mp
      ((List.all_eq_true.mp (gsel_pair_bound_all i hi)) (b, a) hm) with h | h
    · exact Or.inr h
    · exact Or.inl h

/-- **gadget 覆盖格**：每个 (c, j<7)（即 A×S 边）被某条 gadget 使用。 -/
theorem gCover_all :
    ((List.range 4).all fun c => (List.range 7).all fun j =>
      (eInB (gsel 0) c (4 + j) || eInB (gsel 1) c (4 + j)
        || eInB (gsel 2) c (4 + j) || eInB (gsel 3) c (4 + j))) = true := by
  decide

/-- **gadget 两两不交格**：i≠j 的两条 gadget 无公共边。 -/
theorem gDisj_all :
    ((List.range 4).all fun i => (List.range 4).all fun j =>
      (decide (i = j) || (List.range 4).all fun c => (List.range 7).all fun b =>
        !(eInB (gsel i) c (4 + b) && eInB (gsel j) c (4 + b)))) = true := by
  decide

/-! ## §3 环路算术（mod 计数核心） -/

theorem mR_pos (k : Nat) (hk : 6 ≤ k) : 0 < mR k := by
  show 0 < 2 * k - 6
  omega

/-- 环值不超过上界：11 + (2t+d) mod m < 2k+5。 -/
theorem qN_elem_bd (k t d : Nat) (hk : 6 ≤ k) :
    11 + (2 * t + d) % mR k < 2 * k + 5 := by
  have hm : (2 * t + d) % (2 * k - 6) < 2 * k - 6 := Nat.mod_lt _ (by omega)
  show 11 + (2 * t + d) % (2 * k - 6) < 2 * k + 5
  omega

/-- (m + i) % m = i（i < m）。 -/
theorem mod_add_self (m i : Nat) (h : i < m) : (m + i) % m = i := by
  rw [Nat.add_mod, Nat.mod_self, Nat.zero_add, Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt h]

/-- **五连续下标互异**：m = 2k−6 ≥ 6，t ≤ k−4 时 2t+c (c=0..4) 的 mod 两两不同。
    用途：Q_t 的 5 个环 B 互异、同一路内边不重复。 -/
theorem five_distinct (k t : Nat) (hk : 6 ≤ k) (ht : t ≤ k - 4) :
    ∀ (i j : Nat), i < 5 → j < 5 → i ≠ j →
      (2 * t + i) % mR k ≠ (2 * t + j) % mR k := by
  intro i j hi hj hne heq
  have hm := mR_pos k hk
  have hmr : mR k = 2 * k - 6 := rfl
  have hge : 6 ≤ mR k := by rw [hmr]; omega
  have hb : ∀ d : Nat, d < 5 → 2 * t + d < mR k + mR k := by
    intro d hd
    omega
  have hlt1 : (2 * t + i) % mR k < mR k := Nat.mod_lt _ hm
  have hlt2 : (2 * t + j) % mR k < mR k := Nat.mod_lt _ hm
  have hml1 : (2 * t + i) % mR k ≤ 2 * t + i := Nat.mod_le _ _
  have hml2 : (2 * t + j) % mR k ≤ 2 * t + j := Nat.mod_le _ _
  rcases Nat.lt_or_ge i j with hlt | hgej
  · -- i < j：x = 2t+i < y = 2t+j
    have hjlt : j < i + 5 := by omega
    have hxy : 2 * t + i < 2 * t + j := by omega
    by_cases hx : mR k ≤ 2 * t + i
    · have hy : mR k ≤ 2 * t + j := by omega
      have hx2 := mod_two_block (mR k) (2 * t + i) hm hx (hb i hi)
      have hy2 := mod_two_block (mR k) (2 * t + j) hm hy (hb j hj)
      rw [hx2, hy2] at heq
      omega
    · by_cases hy : mR k ≤ 2 * t + j
      · have hx2 := mod_two_block (mR k) (2 * t + j) hm hy (hb j hj)
        rw [hx2, Nat.mod_eq_of_lt (by omega)] at heq
        omega
      · rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at heq
        omega
  · -- j < i：y < x
    have hlt : j < i := by omega
    have hyx : 2 * t + j < 2 * t + i := by omega
    by_cases hy : mR k ≤ 2 * t + j
    · have hi2 : mR k ≤ 2 * t + i := by omega
      have hy2 := mod_two_block (mR k) (2 * t + j) hm hy (hb j hj)
      have hx2 := mod_two_block (mR k) (2 * t + i) hm hi2 (hb i hi)
      rw [hy2, hx2] at heq
      omega
    · by_cases hx : mR k ≤ 2 * t + i
      · have hy2 := mod_two_block (mR k) (2 * t + i) hm hx (hb i hi)
        rw [hy2, Nat.mod_eq_of_lt (by omega)] at heq
        omega
      · rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at heq
        omega

/-- qN 值全部落在 Fin (2*k+5) 范围内。 -/
theorem qN_bounds (k t : Nat) (hk : 6 ≤ k) (ht : t ≤ k - 4) :
    ((qN k t).all fun j => decide (j < 2 * k + 5)) = true := by
  refine List.all_eq_true.mpr ?_
  intro v hv
  simp only [qN, List.mem_cons] at hv
  rcases hv with rfl | hv
  · exact decide_eq_true_iff.mpr (qN_elem_bd k t 0 hk)
  rcases hv with rfl | hv
  · exact decide_eq_true_iff.mpr (by omega)
  rcases hv with rfl | hv
  · exact decide_eq_true_iff.mpr (qN_elem_bd k t 1 hk)
  rcases hv with rfl | hv
  · exact decide_eq_true_iff.mpr (by omega)
  rcases hv with rfl | hv
  · exact decide_eq_true_iff.mpr (qN_elem_bd k t 2 hk)
  rcases hv with rfl | hv
  · exact decide_eq_true_iff.mpr (by omega)
  rcases hv with rfl | hv
  · exact decide_eq_true_iff.mpr (qN_elem_bd k t 3 hk)
  rcases hv with rfl | hv
  · exact decide_eq_true_iff.mpr (by omega)
  rcases hv with rfl | hv
  · exact decide_eq_true_iff.mpr (qN_elem_bd k t 4 hk)
  · exact absurd hv (by simp)

/-- memB 的 cons 展开（头部不等 + 尾部不在）。 -/
theorem memB_cons_ne {a b : Nat} {t : List Nat} (hne : a ≠ b) (h : memB a t = false) :
    memB a (b :: t) = false := by
  show (decide (a = b) || memB a t) = false
  rw [decide_eq_false hne, h]
  rfl

/-- distinctB 的 cons 构造。 -/
theorem distinctB_cons {a : Nat} {t : List Nat} (h1 : memB a t = false)
    (h2 : distinctB t = true) : distinctB (a :: t) = true := by
  show ((!memB a t && distinctB t) = true)
  rw [h1, h2]
  rfl

/-- qN 的顶点互异（A 侧 4 个互异且与环 B 分离；5 个环 B 由 five_distinct 分离）。
    记 w_d = 11 + (2t+d) % mR k，则 qN k t = [w0, 0, w1, 1, w2, 2, w3, 3, w4]，
    从右往左逐个 cons 构造 distinctB（本段由 gen_sec3_v5.py 程序化生成）。 -/
theorem qN_distinct (k t : Nat) (hk : 6 ≤ k) (ht : t ≤ k - 4) :
    distinctB (qN k t) = true := by
  have h5 := five_distinct k t hk ht
  have hneBB : ∀ (i j : Nat), i < 5 → j < 5 → i ≠ j →
      (11 + (2 * t + i) % mR k) ≠ (11 + (2 * t + j) % mR k) := by
    intro i j hi hj hne heq
    have h5ij := h5 i j hi hj hne
    exact hne (by omega)
  have D1 : distinctB [(11 + (2 * t + 4) % mR k)] = true := rfl
  have M2 : memB 3 ([(11 + (2 * t + 4) % mR k)]) = false :=
    memB_cons_ne (by omega) (rfl)
  have D2 : distinctB (3 :: [(11 + (2 * t + 4) % mR k)]) = true :=
    distinctB_cons M2 D1
  have M3 : memB (11 + (2 * t + 3) % mR k) (3 :: [(11 + (2 * t + 4) % mR k)]) = false :=
    memB_cons_ne (by omega) (memB_cons_ne (hneBB 3 4 (by omega) (by omega) (by decide)) (rfl))
  have D3 : distinctB ((11 + (2 * t + 3) % mR k) :: 3 :: [(11 + (2 * t + 4) % mR k)]) = true :=
    distinctB_cons M3 D2
  have M4 : memB 2 ((11 + (2 * t + 3) % mR k) :: 3 :: [(11 + (2 * t + 4) % mR k)]) = false :=
    memB_cons_ne (by omega) (memB_cons_ne (by omega) (memB_cons_ne (by omega) (rfl)))
  have D4 : distinctB (2 :: (11 + (2 * t + 3) % mR k) :: 3 :: [(11 + (2 * t + 4) % mR k)]) = true :=
    distinctB_cons M4 D3
  have M5 : memB (11 + (2 * t + 2) % mR k) (2 :: (11 + (2 * t + 3) % mR k) :: 3 :: [(11 + (2 * t + 4) % mR k)]) = false :=
    memB_cons_ne (by omega) (memB_cons_ne (hneBB 2 3 (by omega) (by omega) (by decide)) (memB_cons_ne (by omega) (memB_cons_ne (hneBB 2 4 (by omega) (by omega) (by decide)) (rfl))))
  have D5 : distinctB ((11 + (2 * t + 2) % mR k) :: 2 :: (11 + (2 * t + 3) % mR k) :: 3 :: [(11 + (2 * t + 4) % mR k)]) = true :=
    distinctB_cons M5 D4
  have M6 : memB 1 ((11 + (2 * t + 2) % mR k) :: 2 :: (11 + (2 * t + 3) % mR k) :: 3 :: [(11 + (2 * t + 4) % mR k)]) = false :=
    memB_cons_ne (by omega) (memB_cons_ne (by omega) (memB_cons_ne (by omega) (memB_cons_ne (by omega) (memB_cons_ne (by omega) (rfl)))))
  have D6 : distinctB (1 :: (11 + (2 * t + 2) % mR k) :: 2 :: (11 + (2 * t + 3) % mR k) :: 3 :: [(11 + (2 * t + 4) % mR k)]) = true :=
    distinctB_cons M6 D5
  have M7 : memB (11 + (2 * t + 1) % mR k) (1 :: (11 + (2 * t + 2) % mR k) :: 2 :: (11 + (2 * t + 3) % mR k) :: 3 :: [(11 + (2 * t + 4) % mR k)]) = false :=
    memB_cons_ne (by omega) (memB_cons_ne (hneBB 1 2 (by omega) (by omega) (by decide)) (memB_cons_ne (by omega) (memB_cons_ne (hneBB 1 3 (by omega) (by omega) (by decide)) (memB_cons_ne (by omega) (memB_cons_ne (hneBB 1 4 (by omega) (by omega) (by decide)) (rfl))))))
  have D7 : distinctB ((11 + (2 * t + 1) % mR k) :: 1 :: (11 + (2 * t + 2) % mR k) :: 2 :: (11 + (2 * t + 3) % mR k) :: 3 :: [(11 + (2 * t + 4) % mR k)]) = true :=
    distinctB_cons M7 D6
  have M8 : memB 0 ((11 + (2 * t + 1) % mR k) :: 1 :: (11 + (2 * t + 2) % mR k) :: 2 :: (11 + (2 * t + 3) % mR k) :: 3 :: [(11 + (2 * t + 4) % mR k)]) = false :=
    memB_cons_ne (by omega) (memB_cons_ne (by omega) (memB_cons_ne (by omega) (memB_cons_ne (by omega) (memB_cons_ne (by omega) (memB_cons_ne (by omega) (memB_cons_ne (by omega) (rfl)))))))
  have D8 : distinctB (0 :: (11 + (2 * t + 1) % mR k) :: 1 :: (11 + (2 * t + 2) % mR k) :: 2 :: (11 + (2 * t + 3) % mR k) :: 3 :: [(11 + (2 * t + 4) % mR k)]) = true :=
    distinctB_cons M8 D7
  have M9 : memB (11 + (2 * t + 0) % mR k) (0 :: (11 + (2 * t + 1) % mR k) :: 1 :: (11 + (2 * t + 2) % mR k) :: 2 :: (11 + (2 * t + 3) % mR k) :: 3 :: [(11 + (2 * t + 4) % mR k)]) = false :=
    memB_cons_ne (by omega) (memB_cons_ne (hneBB 0 1 (by omega) (by omega) (by decide)) (memB_cons_ne (by omega) (memB_cons_ne (hneBB 0 2 (by omega) (by omega) (by decide)) (memB_cons_ne (by omega) (memB_cons_ne (hneBB 0 3 (by omega) (by omega) (by decide)) (memB_cons_ne (by omega) (memB_cons_ne (hneBB 0 4 (by omega) (by omega) (by decide)) (rfl))))))))
  have D9 : distinctB ((11 + (2 * t + 0) % mR k) :: 0 :: (11 + (2 * t + 1) % mR k) :: 1 :: (11 + (2 * t + 2) % mR k) :: 2 :: (11 + (2 * t + 3) % mR k) :: 3 :: [(11 + (2 * t + 4) % mR k)]) = true :=
    distinctB_cons M9 D8
  exact D9

/-- qN 的链条件：相邻对全部是合法二部相邻（B-A 与 A-B 交替）。 -/
theorem qN_chain (k t : Nat) : chainOk adjBN (qN k t) = true := by
  have hge : ∀ (d : Nat), 4 ≤ 11 + (2 * t + d) % mR k := fun d => by omega
  have h1 : adjBN (11 + (2 * t + 0) % mR k) 0 = true := adjBN_BA _ _ (by omega) (hge 0)
  have h2 : adjBN 0 (11 + (2 * t + 1) % mR k) = true := adjBN_AB _ _ (by omega) (hge 1)
  have h3 : adjBN (11 + (2 * t + 1) % mR k) 1 = true := adjBN_BA _ _ (by omega) (hge 1)
  have h4 : adjBN 1 (11 + (2 * t + 2) % mR k) = true := adjBN_AB _ _ (by omega) (hge 2)
  have h5 : adjBN (11 + (2 * t + 2) % mR k) 2 = true := adjBN_BA _ _ (by omega) (hge 2)
  have h6 : adjBN 2 (11 + (2 * t + 3) % mR k) = true := adjBN_AB _ _ (by omega) (hge 3)
  have h7 : adjBN (11 + (2 * t + 3) % mR k) 3 = true := adjBN_BA _ _ (by omega) (hge 3)
  have h8 : adjBN 3 (11 + (2 * t + 4) % mR k) = true := adjBN_AB _ _ (by omega) (hge 4)
  simp only [qN, chainOk, h1, h2, h3, h4, h5, h6, h7, h8, Bool.true_and]

/-- qN 的相邻对表（显式展开）。 -/
theorem qN_pairs_of (k t : Nat) :
    pairsOf (qN k t) =
      [((11 + (2 * t + 0) % mR k), 0), (0, (11 + (2 * t + 1) % mR k)), ((11 + (2 * t + 1) % mR k), 1), (1, (11 + (2 * t + 2) % mR k)), ((11 + (2 * t + 2) % mR k), 2), (2, (11 + (2 * t + 3) % mR k)), ((11 + (2 * t + 3) % mR k), 3), (3, (11 + (2 * t + 4) % mR k))] := rfl

/-- **环路的边形状**：eInB (qN k t) a b = true 给出：恰一端 A（<4）、另一端 ≥4，
    且 B 端值 = 11+(2t+A端+σ)%mR k（σ<2）。 -/
theorem qN_pair_shape {k t a b : Nat}
    (h : eInB (qN k t) a b = true) :
    (a < 4 ∧ 4 ≤ b ∧ (b = 11 + (2 * t + a) % mR k ∨ b = 11 + (2 * t + a + 1) % mR k)) ∨
      (b < 4 ∧ 4 ≤ a ∧ (a = 11 + (2 * t + b) % mR k ∨ a = 11 + (2 * t + b + 1) % mR k)) := by
  have key : ∀ (u v : Nat), (u, v) ∈ pairsOf (qN k t) →
      (u < 4 ∧ 4 ≤ v ∧ (v = 11 + (2 * t + u) % mR k ∨ v = 11 + (2 * t + u + 1) % mR k)) ∨
        (v < 4 ∧ 4 ≤ u ∧ (u = 11 + (2 * t + v) % mR k ∨ u = 11 + (2 * t + v + 1) % mR k)) := by
    intro u v hu
    rw [qN_pairs_of] at hu
    rcases List.mem_cons.mp hu with hp | hu
    · obtain ⟨rfl, rfl⟩ := Prod.mk.injEq _ _ _ _ |>.mp hp
      exact Or.inr ⟨by omega, by omega, Or.inl rfl⟩
    rcases List.mem_cons.mp hu with hp | hu
    · obtain ⟨rfl, rfl⟩ := Prod.mk.injEq _ _ _ _ |>.mp hp
      exact Or.inl ⟨by omega, by omega, Or.inr rfl⟩
    rcases List.mem_cons.mp hu with hp | hu
    · obtain ⟨rfl, rfl⟩ := Prod.mk.injEq _ _ _ _ |>.mp hp
      exact Or.inr ⟨by omega, by omega, Or.inl rfl⟩
    rcases List.mem_cons.mp hu with hp | hu
    · obtain ⟨rfl, rfl⟩ := Prod.mk.injEq _ _ _ _ |>.mp hp
      exact Or.inl ⟨by omega, by omega, Or.inr rfl⟩
    rcases List.mem_cons.mp hu with hp | hu
    · obtain ⟨rfl, rfl⟩ := Prod.mk.injEq _ _ _ _ |>.mp hp
      exact Or.inr ⟨by omega, by omega, Or.inl rfl⟩
    rcases List.mem_cons.mp hu with hp | hu
    · obtain ⟨rfl, rfl⟩ := Prod.mk.injEq _ _ _ _ |>.mp hp
      exact Or.inl ⟨by omega, by omega, Or.inr rfl⟩
    rcases List.mem_cons.mp hu with hp | hu
    · obtain ⟨rfl, rfl⟩ := Prod.mk.injEq _ _ _ _ |>.mp hp
      exact Or.inr ⟨by omega, by omega, Or.inl rfl⟩
    rcases List.mem_cons.mp hu with hp | hu
    · obtain ⟨rfl, rfl⟩ := Prod.mk.injEq _ _ _ _ |>.mp hp
      exact Or.inl ⟨by omega, by omega, Or.inr rfl⟩
    · exact absurd hu (by simp)
  rcases eInB_mem_pairs (qN k t) h with hm | hm
  · exact key a b hm
  · rcases key b a hm with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · exact Or.inr ⟨h1, h2, h3⟩
    · exact Or.inl ⟨h1, h2, h3⟩

/-- **环路内的 EIn 构造**：给定 c < 4、σ < 2，(c, 11+(2t+c+σ) mod m) 是 Q_t 的一条边
    （σ=0 时该边在 pairsOf 中为 (w_c, c)（位置 2c），σ=1 时为 (c, w_{c+1})（位置 2c+1））。 -/
theorem qN_EIn (k t c σ : Nat) (hc : c < 4) (hσ : σ < 2) :
    EIn (qN k t) c (11 + (2 * t + c + σ) % mR k) := by
  have hc4 : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 := by omega
  have hσ2 : σ = 0 ∨ σ = 1 := by omega
  have key : (c, 11 + (2 * t + c + σ) % mR k) ∈ pairsOf (qN k t) ∨
      (11 + (2 * t + c + σ) % mR k, c) ∈ pairsOf (qN k t) := by
    rw [qN_pairs_of]
    rcases hc4 with rfl | rfl | rfl | rfl
    · -- c = 0
      rcases hσ2 with rfl | rfl
      · exact Or.inr (List.mem_cons.mpr (Or.inl rfl))
      · exact Or.inl (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))
    · -- c = 1
      rcases hσ2 with rfl | rfl
      · exact Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))
      · exact Or.inl (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))
    · -- c = 2
      rcases hσ2 with rfl | rfl
      · exact Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))
      · exact Or.inl (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))
    · -- c = 3
      rcases hσ2 with rfl | rfl
      · exact Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))
      · exact Or.inl (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))
  rcases key with hk | hk
  · exact pairsOf_pair_EIn _ _ _ hk
  · exact EIn_swap _ _ _ (pairsOf_pair_EIn _ _ _ hk)

/-- 任何自然数 n 可拆成 2t+σ（σ<2）——ring_cover_find 的奇偶分解件。 -/
theorem exists_two_split (n : Nat) : ∃ t σ, σ < 2 ∧ 2 * t + σ = n :=
  ⟨n / 2, n % 2, Nat.mod_lt n (by omega), Nat.div_add_mod n 2⟩

/-- **环覆盖查找**：对任意 c < 4 与环下标 i < m，存在 t ≤ k−4、σ < 2 使
    (2t+c+σ) mod m = i（T27.3 审计第 2 步的鸽笼方向：mod 2 唯一性）。 -/
theorem ring_cover_find (k c i : Nat) (hk : 6 ≤ k) (hc : c < 4) (hi : i < mR k) :
    ∃ (t σ : Nat), t ≤ k - 4 ∧ σ < 2 ∧ (2 * t + c + σ) % mR k = i := by
  have hmR : mR k = 2 * k - 6 := rfl
  by_cases hci : c ≤ i
  · -- 直接块：2t+σ = i−c，则 2t+c+σ = i < m，取模即自身
    obtain ⟨t, σ, hσ, hts⟩ := exists_two_split (i - c)
    refine ⟨t, σ, ?_, hσ, ?_⟩
    · omega
    · have he : 2 * t + c + σ = i := by omega
      rw [he, Nat.mod_eq_of_lt hi]
  · -- 回绕块：2t+σ = m+i−c ∈ (0, m)，则 2t+c+σ = m+i ≡ i (mod m)
    obtain ⟨t, σ, hσ, hts⟩ := exists_two_split (mR k + i - c)
    have hm : 0 < mR k := mR_pos k hk
    have hlt : mR k + i - c < mR k := by omega
    refine ⟨t, σ, ?_, hσ, ?_⟩
    · omega
    · have he : 2 * t + c + σ = mR k + i := by omega
      rw [he, mod_add_self (mR k) i hi]

/-! ## §4 路数：generalDecomp_len -/

theorem gNlist_len : (gNlist : List (List Nat)).length = 4 := rfl

theorem GsF_len (k : Nat) : (GsF k).length = 4 := by
  show (gNlist.map (gvL k)).length = 4
  rw [List.length_map, gNlist_len]

theorem ringN_len (k : Nat) : (ringN k).length = k - 3 := by
  show ((List.range (k - 3)).map (qN k)).length = k - 3
  rw [List.length_map, List.length_range]

theorem ringsF_len (k : Nat) : (ringsF k).length = k - 3 := by
  show ((ringN k).map (gvL k)).length = k - 3
  rw [List.length_map]
  exact ringN_len k

/-- **一般构造路数（generalDecomp_len）**：k ≥ 3 时 generalDecomp k 恰有
    k+1 条路 = 4 条 gadget + (k−3) 条环路。 -/
theorem generalDecomp_len (k : Nat) (hk : 3 ≤ k) : (generalDecomp k).length = k + 1 := by
  show (GsF k ++ ringsF k).length = k + 1
  rw [List.length_append, GsF_len, ringsF_len]
  omega

/-! ## §5 每条元素是合法路径（IsPath 的组装） -/

theorem adjBN_K4nAdj {n : Nat} {u v : Fin (n + 4)} (h : adjBN u.val v.val = true) :
    K4nAdj n u v := by
  simp only [adjBN, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_iff] at h
  exact h

theorem gsel_len (i : Nat) (hi : i < 4) : 2 ≤ (gsel i).length := by
  rcases i with _ | _ | _ | _ <;> simp [gsel] <;> decide

theorem qN_len (k t : Nat) : (qN k t).length = 9 := rfl

/-- Nat 级三件套（界 + distinctB + chainOk）经 map (gv k) 升级为 IsPath。 -/
theorem isPath_gvL (k : Nat) (L : List Nat)
    (hb : ((L.all fun j => decide (j < 2 * k + 5)) = true))
    (hd : distinctB L = true) (hc : chainOk adjBN L = true) (hl : 2 ≤ L.length) :
    IsPath (K4nAdj (2 * k + 1)) (gvL k L) := by
  have hdb : distinctB (gvL k L) = true := (distinctB_map_gv k L hb).trans hd
  refine ⟨?_, distinctB_sound _ hdb, ?_⟩
  · show 2 ≤ (L.map (gv k)).length
    rwa [List.length_map]
  · apply chainOk_sound (K4nAdj (2 * k + 1))
      (fun (u v : Fin (2 * k + 5)) => adjBN u.val v.val)
    · intro u v hab
      exact adjBN_K4nAdj hab
    · show chainOk (fun u v : Fin (2 * k + 5) => adjBN u.val v.val)
        (L.map (gv k)) = true
      rw [chainOk_map_gv k L hb]
      exact hc

theorem gsel_path (k i : Nat) (hk : 3 ≤ k) (hi : i < 4) :
    IsPath (K4nAdj (2 * k + 1)) (gvL k (gsel i)) :=
  isPath_gvL k (gsel i) (gsel_bounds k i hk hi) (gsel_props i hi).1 (gsel_props i hi).2
    (gsel_len i hi)

theorem qN_path (k t : Nat) (hk : 6 ≤ k) (ht : t ≤ k - 4) :
    IsPath (K4nAdj (2 * k + 1)) (gvL k (qN k t)) :=
  isPath_gvL k (qN k t) (qN_bounds k t hk ht) (qN_distinct k t hk ht) (qN_chain k t)
    (by rw [qN_len]; decide)

theorem gsel_mem_gNlist (i : Nat) (hi : i < 4) : gsel i ∈ gNlist := by
  rcases i with _ | _ | _ | _ <;> simp [gNlist, gsel]

theorem mem_GsF (k : Nat) (P : List (Fin (2 * k + 5))) (h : P ∈ GsF k) :
    ∃ i : Nat, i < 4 ∧ P = gvL k (gsel i) := by
  obtain ⟨L, hL, hPL⟩ := List.mem_map.1 h
  simp only [gNlist, List.mem_cons] at hL
  rcases hL with rfl | rfl | rfl | rfl | h0
  · exact ⟨0, by decide, hPL.symm⟩
  · exact ⟨1, by decide, hPL.symm⟩
  · exact ⟨2, by decide, hPL.symm⟩
  · exact ⟨3, by decide, hPL.symm⟩
  · exact absurd h0 (by simp)

theorem mem_ringsF (k : Nat) (P : List (Fin (2 * k + 5))) (h : P ∈ ringsF k) :
    ∃ t : Nat, t ≤ k - 4 ∧ P = gvL k (qN k t) := by
  obtain ⟨L, hL, hPL⟩ := List.mem_map.1 h
  obtain ⟨t, ht, hLq⟩ := List.mem_map.1 hL
  have htr : t < k - 3 := List.mem_range.mp ht
  refine ⟨t, by omega, ?_⟩
  rw [hLq]
  exact hPL.symm

/-- generalDecomp k 的每条元素都是 K_{4,2k+1} 的合法路径。 -/
theorem generalDecomp_paths (k : Nat) (hk : 6 ≤ k) :
    ∀ P ∈ generalDecomp k, IsPath (K4nAdj (2 * k + 1)) P := by
  intro P hP
  rcases List.mem_append.1 hP with hPg | hPr
  · obtain ⟨i, hi, rfl⟩ := mem_GsF k P hPg
    exact gsel_path k i (by omega) hi
  · obtain ⟨t, ht, rfl⟩ := mem_ringsF k P hPr
    exact qN_path k t hk ht

/-! ## §6 覆盖：IsCover 的组装 -/

/-- Bool 四选一：A || (B || (C || D)) = true 给出某分支为 true。 -/
theorem bool_or_chain4 {A B C D : Bool} (h : (A || B || C || D) = true) :
    A = true ∨ B = true ∨ C = true ∨ D = true := by
  cases A <;> cases B <;> cases C <;> cases D <;> simp_all

/-- Bool 二选一的负向：A = false 时 A || B = true 给出 B = true。 -/
theorem bool_or_two {A B : Bool} (h : (A || B) = true) (ha : A = false) : B = true := by
  rw [ha, Bool.false_or] at h
  exact h

/-- gadget 覆盖查找：c < 4、b < 7 时某条 gadget 含边 {c, 4+b}（gCover_all 的查表版）。 -/
theorem gCover_lookup (c b : Nat) (hc : c < 4) (hb : b < 7) :
    ∃ i : Nat, i < 4 ∧ eInB (gsel i) c (4 + b) = true := by
  have h1 := (List.all_eq_true.mp gCover_all) c (List.mem_range.mpr hc)
  have h2 := (List.all_eq_true.mp h1) b (List.mem_range.mpr hb)
  rcases bool_or_chain4 h2 with h | h | h | h
  · exact ⟨0, by omega, h⟩
  · exact ⟨1, by omega, h⟩
  · exact ⟨2, by omega, h⟩
  · exact ⟨3, by omega, h⟩

/-- gadget 两两不交查找：i ≠ j 的两条 gadget 无公共 A×S 边（gDisj_all 的查表版）。 -/
theorem gDisj_lookup {i j c b : Nat} (hi : i < 4) (hj : j < 4) (hne : i ≠ j)
    (hc : c < 4) (hb : b < 7)
    (h1 : eInB (gsel i) c (4 + b) = true) (h2 : eInB (gsel j) c (4 + b) = true) : False := by
  have hr1 := (List.all_eq_true.mp gDisj_all) i (List.mem_range.mpr hi)
  have hr2 := (List.all_eq_true.mp hr1) j (List.mem_range.mpr hj)
  have hd : decide (i = j) = false := decide_eq_false hne
  have hB := bool_or_two hr2 hd
  have h4 := (List.all_eq_true.mp hB) c (List.mem_range.mpr hc)
  have hall := (List.all_eq_true.mp h4) b (List.mem_range.mpr hb)
  rw [h1, h2] at hall
  simp at hall

/-- gv k i 在 i 落于顶点范围内时等于值为 i 的 Fin 顶点。 -/
theorem gv_of_val {k : Nat} {x : Fin (2 * k + 5)} {i : Nat} (hb : i < 2 * k + 5)
    (hi : x.val = i) : gv k i = x :=
  Fin.val_inj.mp (by rw [gv_eq_self k i hb]; exact hi.symm)

theorem gsel_in_decomp (k i : Nat) (hi : i < 4) :
    gvL k (gsel i) ∈ generalDecomp k := by
  refine List.mem_append.mpr (Or.inl ?_)
  exact List.mem_map.mpr ⟨gsel i, gsel_mem_gNlist i hi, rfl⟩

theorem qN_in_decomp (k : Nat) (hk4 : 4 ≤ k) (t : Nat) (ht : t ≤ k - 4) :
    gvL k (qN k t) ∈ generalDecomp k := by
  have htr : t < k - 3 := by omega
  refine List.mem_append.mpr (Or.inr ?_)
  exact List.mem_map.mpr ⟨qN k t,
    List.mem_map.mpr ⟨t, List.mem_range.mpr htr, rfl⟩, rfl⟩

/-- A 侧出发的边（x 值 < 4 ≤ y 值）必被某条路使用：y 在 S（值 4..10）走 gadget，
    y 在 R（值 11..2k+4）走环路（ring_cover_find 鸽笼）。 -/
theorem cover_A (k : Nat) (hk : 6 ≤ k) (x y : Fin (2 * k + 5))
    (hx : x.val < 4) (hy : 4 ≤ y.val) : ∃ P ∈ generalDecomp k, EIn P x y := by
  have hyb : y.val < 2 * k + 5 := y.isLt
  have hx1 : gv k x.val = x := Fin.val_inj.mp (by rw [gv_eq_self k x.val (by omega)])
  have hb4 : 4 + (y.val - 4) < 2 * k + 5 := by omega
  have hy1 : gv k (4 + (y.val - 4)) = y := by
    refine Fin.val_inj.mp ?_
    rw [gv_eq_self k (4 + (y.val - 4)) hb4]
    omega
  rcases Nat.lt_or_ge (y.val - 4) 7 with hjs | hjr
  · -- S 情形：核心 B，走 gadget
    obtain ⟨i, hi4, he⟩ := gCover_lookup x.val (y.val - 4) hx hjs
    have hbd : ((gsel i).all fun j => decide (j < 2 * k + 5)) = true :=
      gsel_bounds k i (by omega) hi4
    refine ⟨gvL k (gsel i), gsel_in_decomp k i hi4, ?_⟩
    have hE : EIn ((gsel i).map (gv k)) (gv k x.val) (gv k (4 + (y.val - 4))) :=
      EIn_map_gv k (gsel i) hbd x.val (4 + (y.val - 4)) (eInB_true _ he)
    rwa [hx1, hy1] at hE
  · -- R 情形：环 B，走环路
    have him : y.val - 11 < mR k := by show y.val - 11 < 2 * k - 6; omega
    obtain ⟨t, σ, ht, hσ, hmod⟩ := ring_cover_find k x.val (y.val - 11) hk hx him
    have hbd : ((qN k t).all fun j => decide (j < 2 * k + 5)) = true := qN_bounds k t hk ht
    have heq : (4 + (y.val - 4) : Nat) = 11 + (2 * t + x.val + σ) % mR k := by omega
    refine ⟨gvL k (qN k t), qN_in_decomp k (by omega) t ht, ?_⟩
    have hE0 : EIn (qN k t) x.val (4 + (y.val - 4)) := by
      have hE1 : EIn (qN k t) x.val (11 + (2 * t + x.val + σ) % mR k) :=
        qN_EIn k t x.val σ hx hσ
      rwa [← heq] at hE1
    have hE : EIn ((qN k t).map (gv k)) (gv k x.val) (gv k (4 + (y.val - 4))) :=
      EIn_map_gv k (qN k t) hbd x.val (4 + (y.val - 4)) hE0
    rwa [hx1, hy1] at hE

/-- **generalDecomp 覆盖**。 -/
theorem generalDecomp_cover (k : Nat) (hk : 6 ≤ k) :
    IsCover (K4nAdj (2 * k + 1)) (generalDecomp k) := by
  intro x y hxy
  rcases hxy with ⟨hx, hy⟩ | ⟨hy, hx⟩
  · exact cover_A k hk x y hx hy
  · obtain ⟨P, hP, hE⟩ := cover_A k hk y x hy hx
    exact ⟨P, hP, EIn_swap P y x hE⟩

/-! ## §7 两两边不交：IsEdgeDisjoint 的组装 -/

theorem eInB_gvL (k : Nat) {L : List Nat}
    (hb : ((L.all fun j => decide (j < 2 * k + 5)) = true))
    (x y : Fin (2 * k + 5)) :
    eInB (gvL k L) x y = eInB L x.val y.val :=
  eInB_map_gv k L hb x y

/-- eInB 的换向（Bool 级）。 -/
theorem eInB_swap {V : Type} [DecidableEq V] : ∀ (L : List V) (a b : V),
    eInB L a b = true → eInB L b a = true
  | [], _, _, h => by simp [eInB] at h
  | [_], _, _, h => by simp [eInB] at h
  | u :: v :: r, _a, _b, h => by
      simp only [eInB, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_iff] at h ⊢
      rcases h with (h | h) | h
      · exact Or.inl (Or.inr ⟨h.1, h.2⟩)
      · exact Or.inl (Or.inl ⟨h.1, h.2⟩)
      · exact Or.inr (eInB_swap (v :: r) _a _b h)

/-- **mod-2 唯一性**：t, t' ≤ k−4（k ≥ 6）、σ, σ' < 2 时，
    (2t+c+σ) 与 (2t'+c+σ') 模 m（= 2k−6）同余仅当 t = t' 且 σ = σ'。 -/
theorem mod_uniq (k t t' σ σ' c : Nat) (hk : 6 ≤ k) (ht : t ≤ k - 4) (ht' : t' ≤ k - 4)
    (hσ : σ < 2) (hσ' : σ' < 2) (hc : c < 4)
    (heq : (2 * t + c + σ) % mR k = (2 * t' + c + σ') % mR k) :
    t = t' ∧ σ = σ' := by
  have hmR : mR k = 2 * k - 6 := rfl
  have hm : 0 < mR k := mR_pos k hk
  have h1 : 2 * t + c + σ < mR k + mR k := by omega
  have h2 : 2 * t' + c + σ' < mR k + mR k := by omega
  by_cases hm1 : mR k ≤ 2 * t + c + σ
  · by_cases hm2 : mR k ≤ 2 * t' + c + σ'
    · rw [mod_two_block _ _ hm hm1 h1, mod_two_block _ _ hm hm2 h2] at heq
      omega
    · rw [mod_two_block _ _ hm hm1 h1, Nat.mod_eq_of_lt (by omega)] at heq
      omega
  · by_cases hm2 : mR k ≤ 2 * t' + c + σ'
    · rw [Nat.mod_eq_of_lt (by omega), mod_two_block _ _ hm hm2 h2] at heq
      omega
    · rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at heq
      omega

/-- 两条不同环路无公共边（Nat 级）：同一 A 端的 B 值由 mod-2 唯一性锁定 t。 -/
theorem ring_ring_disj (k t t' : Nat) (hk : 6 ≤ k) (ht : t ≤ k - 4) (ht' : t' ≤ k - 4)
    (hne : t ≠ t') (a b : Nat)
    (h1 : eInB (qN k t) a b = true) (h2 : eInB (qN k t') a b = true) : False := by
  have key : ∀ (u v w z : Nat), u < 4 → v < 4 →
      (w = 11 + (2 * t + u) % mR k ∨ w = 11 + (2 * t + u + 1) % mR k) →
      (z = 11 + (2 * t' + v) % mR k ∨ z = 11 + (2 * t' + v + 1) % mR k) →
      u = v → w = z → False := by
    intro u v w z hu hv hw hz huv hwz
    obtain ⟨σ, hσ, hw'⟩ : ∃ σ, σ < 2 ∧ w = 11 + (2 * t + u + σ) % mR k := by
      rcases hw with h | h
      · exact ⟨0, by omega, by rw [h, Nat.add_zero]⟩
      · exact ⟨1, by omega, h⟩
    obtain ⟨σ', hσ', hz'⟩ : ∃ σ', σ' < 2 ∧ z = 11 + (2 * t' + v + σ') % mR k := by
      rcases hz with h | h
      · exact ⟨0, by omega, by rw [h, Nat.add_zero]⟩
      · exact ⟨1, by omega, h⟩
    have hX : w - 11 = (2 * t + u + σ) % mR k := by omega
    rw [huv] at hX
    have hY : z - 11 = (2 * t' + v + σ') % mR k := by omega
    have hmod : (2 * t + v + σ) % mR k = (2 * t' + v + σ') % mR k := by omega
    exact hne (mod_uniq k t t' σ σ' v hk ht ht' hσ hσ' hv hmod).1
  rcases qN_pair_shape h1 with ⟨ha, hba, hbv⟩ | ⟨hb, haa, hav⟩ <;>
    rcases qN_pair_shape h2 with ⟨ha', hba', hbv'⟩ | ⟨hb', haa', hav'⟩
  · exact key a a b b ha ha' hbv hbv' rfl rfl
  · omega
  · omega
  · exact key b b a a hb hb' hav hav' rfl rfl

/-- 环路与 gadget 无公共边（Nat 级）：gadget 边的 B 端 < 11，环路边的 B 端 ≥ 11。 -/
theorem ring_gadget_disj (k t i : Nat) (hk : 6 ≤ k) (ht : t ≤ k - 4) (hi : i < 4)
    (a b : Nat) (h1 : eInB (qN k t) a b = true) (h2 : eInB (gsel i) a b = true) : False := by
  rcases qN_pair_shape h1 with ⟨ha, hba, hbv⟩ | ⟨hb, haa, hav⟩ <;>
    rcases gsel_pair_bound i hi h2 with ⟨g1, g2, g3⟩ | ⟨g1, g2, g3⟩
  · omega
  · omega
  · omega
  · omega

/-- 两条不同 gadget 无公共边（Nat 级，gDisj_lookup 的换向完备版）。 -/
theorem gg_disj (k i j : Nat) (hk : 3 ≤ k) (hi : i < 4) (hj : j < 4) (hne : i ≠ j)
    (a b : Nat) (h1 : eInB (gsel i) a b = true) (h2 : eInB (gsel j) a b = true) : False := by
  rcases gsel_pair_bound i hi h1 with ⟨p1, q1, r1⟩ | ⟨p1, q1, r1⟩ <;>
    rcases gsel_pair_bound j hj h2 with ⟨p2, q2, r2⟩ | ⟨p2, q2, r2⟩
  · have hb7 : b - 4 < 7 := by omega
    have hb4 : 4 + (b - 4) = b := by omega
    rw [← hb4] at h1 h2
    exact gDisj_lookup hi hj hne p1 hb7 h1 h2
  · omega
  · omega
  · have ha7 : a - 4 < 7 := by omega
    have ha4 : 4 + (a - 4) = a := by omega
    rw [← ha4] at h1 h2
    exact gDisj_lookup hj hi (fun h => hne h.symm) p2 ha7
      (eInB_swap (gsel j) (4 + (a - 4)) b h2) (eInB_swap (gsel i) (4 + (a - 4)) b h1)

/-- **generalDecomp 两两边不交**：gadget×gadget 用覆盖格，gadget×环用值域分离
    （B 端 < 11 对 ≥ 11），环×环用 mod-2 唯一性。 -/
theorem generalDecomp_disj (k : Nat) (hk : 6 ≤ k) :
    IsEdgeDisjoint (generalDecomp k) := by
  intro P hP Q hQ hne x y hc
  obtain ⟨hc1, hc2⟩ := hc
  have e1 : eInB P x y = true := EIn_true_eInB P hc1
  have e2 : eInB Q x y = true := EIn_true_eInB Q hc2
  rcases List.mem_append.1 hP with hPg | hPr <;>
    rcases List.mem_append.1 hQ with hQg | hQr
  · -- gadget × gadget
    obtain ⟨i, hi, hPi⟩ := mem_GsF k P hPg
    obtain ⟨j, hj, hQj⟩ := mem_GsF k Q hQg
    have hij : i ≠ j := by
      intro h
      apply hne
      rw [hPi, hQj, h]
    exact gg_disj k i j (by omega) hi hj hij x.val y.val
      (by rw [hPi] at e1; rw [eInB_gvL k (gsel_bounds k i (by omega) hi) x y] at e1; exact e1)
      (by rw [hQj] at e2; rw [eInB_gvL k (gsel_bounds k j (by omega) hj) x y] at e2; exact e2)
  · -- gadget × 环
    obtain ⟨i, hi, hPi⟩ := mem_GsF k P hPg
    obtain ⟨t, ht, hQj⟩ := mem_ringsF k Q hQr
    exact ring_gadget_disj k t i hk ht hi x.val y.val
      (by rw [hQj] at e2; rw [eInB_gvL k (qN_bounds k t hk ht) x y] at e2; exact e2)
      (by rw [hPi] at e1; rw [eInB_gvL k (gsel_bounds k i (by omega) hi) x y] at e1; exact e1)
  · -- 环 × gadget
    obtain ⟨t, ht, hPi⟩ := mem_ringsF k P hPr
    obtain ⟨i, hi, hQj⟩ := mem_GsF k Q hQg
    exact ring_gadget_disj k t i hk ht hi x.val y.val
      (by rw [hPi] at e1; rw [eInB_gvL k (qN_bounds k t hk ht) x y] at e1; exact e1)
      (by rw [hQj] at e2; rw [eInB_gvL k (gsel_bounds k i (by omega) hi) x y] at e2; exact e2)
  · -- 环 × 环
    obtain ⟨t, ht, hPi⟩ := mem_ringsF k P hPr
    obtain ⟨t', ht', hQj⟩ := mem_ringsF k Q hQr
    have htt : t ≠ t' := by
      intro h
      apply hne
      rw [hPi, hQj, h]
    exact ring_ring_disj k t t' hk ht ht' htt x.val y.val
      (by rw [hPi] at e1; rw [eInB_gvL k (qN_bounds k t hk ht) x y] at e1; exact e1)
      (by rw [hQj] at e2; rw [eInB_gvL k (qN_bounds k t' hk ht') x y] at e2; exact e2)

/-! ## §8 组装：generalDecomp_valid 与主定理 -/

/-- **generalDecomp_valid（T27.3 主结果）**：k ≥ 6 时 generalDecomp k 是 K_{4,2k+1}
    的路分解（顶点类型 Fin (2k+5) 恰为 K_{4,2k+1} 的 (2k+1)+4 个顶点）。 -/
theorem generalDecomp_valid (k : Nat) (hk : 6 ≤ k) :
    IsPathDecomp (K4nAdj (2 * k + 1)) (generalDecomp k) :=
  ⟨generalDecomp_paths k hk, generalDecomp_cover k hk, generalDecomp_disj k hk⟩

/-- **p(K_{4,2k+1}) = k+1（k ≥ 6）**：一般构造上界 + T27.1 下界夹逼。 -/
theorem pNumK4n_ge13 (k : Nat) (hk : 6 ≤ k) : pNumK4n (2 * k + 1) = k + 1 := by
  have hup : pNumK4n (2 * k + 1) ≤ k + 1 :=
    pNumK4n_min (2 * k + 1) (k + 1)
      ⟨generalDecomp k, generalDecomp_valid k hk, generalDecomp_len k (by omega)⟩
  have hge := pNumK4n_ge_half (2 * k + 1) (by omega)
  omega

/-- 上界部件：奇 n ≥ 3 时 p(K_{4,n}) ≤ (n+1)/2（n ≤ 11 走逐例，n ≥ 13 走一般构造）。 -/
theorem pNumK4n_odd_le (n : Nat) (hn : 3 ≤ n) (hodd : ∃ j, n = 2 * j + 1) :
    pNumK4n n ≤ (n + 1) / 2 := by
  obtain ⟨j, hj⟩ := hodd
  have hmod : n % 2 = 1 := by omega
  rcases Nat.lt_or_ge n 13 with h13 | h13
  · have h := pNumK4n_odd_le17 n hn (by omega) hmod
    omega
  · have hk6 : 6 ≤ j := by omega
    have h := pNumK4n_ge13 j hk6
    rw [hj]
    omega

/-- **主定理（lane_27 T27.5 的 Lean 闭合）**：对一切奇 n ≥ 3，pNumK4n n = (n+1)/2，
    即 p(K_{4,n}) = ⌈n/2⌉。经 pNumK4n_eq_half_of_le 组装（下界 + 本构造上界）。 -/
theorem pNumK4n_odd_all (n : Nat) (hn : 3 ≤ n) (hodd : ∃ j, n = 2 * j + 1) :
    pNumK4n n = (n + 1) / 2 :=
  pNumK4n_eq_half_of_le n hn hodd (pNumK4n_odd_le n hn hodd)

/-- 方向反转演示：逐例值成为主定理 corollary。 -/
theorem cor_pNumK4n_5 : pNumK4n 5 = 3 := pNumK4n_odd_all 5 (by decide) ⟨2, rfl⟩

/-- 方向反转演示：n = 13（K4nOddBig 的逐例定理现可由主定理推出）。 -/
theorem cor_pNumK4n_13 : pNumK4n 13 = 7 := pNumK4n_odd_all 13 (by decide) ⟨6, rfl⟩

/-- 方向反转演示：**n = 19 是本 lane 新闭合的值**（此前仅有 k ≤ 8 即 n ≤ 17 的逐例）。 -/
theorem cor_pNumK4n_19 : pNumK4n 19 = 10 := pNumK4n_odd_all 19 (by decide) ⟨9, rfl⟩

end Front583

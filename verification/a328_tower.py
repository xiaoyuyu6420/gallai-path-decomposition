#!/usr/bin/env python3
"""a328_tower.py — layered necessary-condition ("tower") solver for the odd-clique
placement problem K_n @ k (layer k carries K_{2k+1}; sharpness means the C(n,2)
image-edge classes hit every residue of Z_k exactly once).

This file is the machine-account generator for the layered-arithmetic results
quoted in the paper (sec-classification.tex): per-layer residue-profile sieves,
Fourier/character equations, and the order-2 feasibility table. The verbatim
copy pinned by SHA-256 in verification/artifact_manifest.json lives at
verification/snapshot/artifacts/deepA32x/a328_tower.py; verification/checks.py
does not re-execute it — it only re-checks the arithmetic of the JSON outputs
(census ledger and o2-table accounting).

The original module docstring (verbatim, in Chinese) follows.
"""
import itertools
import json
import sys
import numpy as np

CAP = 20_000_000  # per-layer candidate-pair cap（超限如实记 truncated）


def lift_count(P, d0, d1):
    """profile P 从 d0 提升到 d1 的提升个数（不枚举）。"""
    p = d1 // d0
    r = 1
    for a in range(d0):
        j = P[a]
        # comps(j, p) 个数 = C(j+p-1, p-1)
        c = 1
        for t in range(1, p):
            c = c * (j + t) // t
        r *= c
        if r > CAP:
            return r
    return r


def lifts_from(surv_pairs, d0, d1, cap):
    """从 surv_pairs 提升到 d1；超 cap 返回 (None, True)。"""
    cand = []
    trunc = False
    for (C, M) in surv_pairs:
        for C2 in lifts(C, d0, d1):
            for M2 in lifts(M, d0, d1):
                cand.append((C2, M2))
                if len(cand) > cap:
                    return None, True
    return cand, False


def divisors(k):
    return [d for d in range(2, k + 1) if k % d == 0]


def comps(s, parts):
    """非负和 s 拆 parts 份，字典序。"""
    if parts == 1:
        yield (s,)
        return
    if parts == 0:
        if s == 0:
            yield ()
        return
    for x in range(s + 1):
        for rest in comps(s - x, parts - 1):
            yield (x,) + rest


def fresh_pairs(d, n, mode, e=None, o=None):
    """首层（模 d）新枚举 profile 对。reg: 固定 (e,o)，e≥1，C₀≥1；inf: e+o=n−1 无约束。"""
    if mode == "reg":
        for x in comps(e - 1, d):
            C = (x[0] + 1,) + x[1:]
            for M in comps(o, d):
                yield (C, M)
    else:  # inf: m = n-1 有限点
        m = n - 1
        for j in range(m + 1):
            for C in comps(j, d):
                for M in comps(m - j, d):
                    yield (C, M)


def lifts(P, d0, d1):
    """profile P（模 d₀）到模 d₁=d₀·p 的全部提升。"""
    p = d1 // d0
    per = [list(comps(P[a], p)) for a in range(d0)]
    for combo in itertools.product(*per):
        Q = [0] * d1
        for a in range(d0):
            for t in range(p):
                Q[a + t * d0] += combo[a][t]
        yield tuple(Q)


def check_pairs(pairs, d, k, mode, block=60_000):
    """count-eq 向量筛。pairs: [(C,M)] at modulus d.  返回幸存 [(C,M)]。"""
    tgt = k // d
    out = []
    if not pairs:
        return out
    for s0 in range(0, len(pairs), block):
        blk = pairs[s0:s0 + block]
        CA = np.array([p[0] for p in blk], dtype=np.int64)
        MA = np.array([p[1] for p in blk], dtype=np.int64)
        P, dd = CA.shape
        N = np.zeros((P, dd), dtype=np.int64)
        for a in range(dd):
            ca = CA[:, a]
            ma = MA[:, a]
            N[:, (2 * a) % dd] += ca * (ca - 1) // 2
            N[:, (2 * a + 1) % dd] += ma * (ma - 1) // 2
            for b in range(a + 1, dd):
                N[:, (a + b) % dd] += ca * CA[:, b]
                N[:, (a + b + 1) % dd] += ma * MA[:, b]
        for a in range(dd):
            for b in range(dd):
                N[:, (a + b) % dd] += CA[:, a] * MA[:, b]
        if mode == "inf":
            for a in range(dd):
                N[:, (2 * a) % dd] += CA[:, a]
                N[:, (2 * a + 1) % dd] += MA[:, a]
        good = (N == tgt).all(axis=1)
        for idx in np.nonzero(good)[0]:
            out.append(pairs[s0 + int(idx)])
    return out


def spf(d):
    p = 2
    while p * p <= d:
        if d % p == 0:
            return p
        p += 1
    return d


def collect(gen, cap=None):
    out = []
    for x in gen:
        out.append(x)
        if cap and len(out) > cap:
            return out, True
    return out, False


def run_regime(k, n, mode, e, o, verbose=False):
    """对 (mode,e,o) 跑塔。素层新枚举；合数层 d 从【枚举量最小的非空幸存除子】提升
    （柔性除子：任何 d₀|d 且 surv[d₀] 非空皆可，完备性由「通过者必是某 d₀-幸存者的
    提升」承载）。任一层幸存空 ⟹ 死于该层；枚举超 CAP ⟹ truncated（该层及之后的
    判决无效，如实标记）。"""
    layers = divisors(k)
    surv = {}
    hist = []
    truncated = False
    dead_at = None
    for d in layers:
        cand = None
        trunc_f = False
        src = None
        divs0 = [d0 for d0 in range(2, d) if d % d0 == 0 and surv.get(d0)]
        if divs0:
            # 成本升序：按首对提升量的估计排序（lift_count 带早退），小者先试
            def est(d0):
                C0, M0 = surv[d0][0]
                return lift_count(C0, d0, d) * lift_count(M0, d0, d)
            for d0 in sorted(divs0, key=est):
                c, tr = lifts_from(surv[d0], d0, d, CAP)
                if c is not None:
                    cand, src = c, d0
                    trunc_f = False
                    break
                trunc_f = True
            if cand is None:
                cand, trunc_f = None, True
        else:
            cand, trunc_f = collect(fresh_pairs(d, n, mode, e, o), CAP)
        if cand is None:
            truncated = True
            hist.append({"d": d, "cand": -1, "surv": -1, "note": "CAP-truncated",
                         "src": src})
            break  # 截断非死亡：该 (mode,regime) 判决无效（inconclusive）
        truncated = truncated or trunc_f
        cur = check_pairs(cand, d, k, mode)
        surv[d] = cur
        hist.append({"d": d, "cand": len(cand), "surv": len(cur), "src": src})
        if verbose:
            print(f"  layer d={d} (src={src}): cand={len(cand)} surv={len(cur)}", file=sys.stderr)
        if not cur:
            dead_at = d
            break
    if dead_at or truncated:
        n_surv = 0
        sample = []
    else:
        final = surv[layers[-1]]
        n_surv = len(final)
        sample = [tuple(map(list, p)) for p in final[:5]]
    return {"mode": mode, "e": e, "o": o, "k": k, "n": n,
            "layers": hist, "dead_at": dead_at, "truncated": truncated,
            "n_surv": n_surv, "surv_sample": sample}


def sieve_primes(n):
    """[L1] 筛素数：奇 p | n−1（2-齿按 [E9] 自动满足，不排除）。"""
    ps, m = [], n - 1
    p = 2
    while p * p <= m:
        if m % p == 0:
            if p != 2:
                ps.append(p)
            while m % p == 0:
                m //= p
        p += 1
    if m > 1 and m != 2:
        ps.append(m)
    return sorted(set(ps))


def regime_allowed(n, e, ps):
    q = e * (n - e)
    return all(q % p == 0 for p in ps)


def order2_feasible(n, e):
    """k=C(n,2) 偶时 regime(e,n−e) 的 order-2 必要条件
    x_E² + 2 x_E x_O − x_O² = e − o （x_E≡e, x_O≡o mod 2, |x_E|≤e, |x_O|≤o）
    的可解性。True=可行 / False=不可行（纸面死）/ None=k 奇无二阶特征。"""
    if (n * (n - 1)) % 4 != 0:
        return None  # k 奇：无二阶特征
    o = n - e
    D = e - o
    for xe in range(-e, e + 1):
        if (xe - e) % 2:
            continue
        for xo in range(-o, o + 1):
            if (xo - o) % 2:
                continue
            if xe * xe + 2 * xe * xo - xo * xo == D:
                return True
    return False


def math_isqrt(t):
    x = int(t ** 0.5)
    while x * x > t:
        x -= 1
    while (x + 1) * (x + 1) <= t:
        x += 1
    return x


def tower_n(n, regimes_only_allowed=True, verbose=False):
    """对层 k=C(n,2) 的全部 regime + ∞ 跑塔。"""
    k = n * (n - 1) // 2
    ps = sieve_primes(n)
    rows = []
    for e in range(1, n + 1):
        o = n - e
        allowed = regime_allowed(n, e, ps)
        if regimes_only_allowed and not allowed:
            rows.append({"mode": "reg", "e": e, "o": o, "k": k, "n": n,
                         "sieve": "elim", "q": e * o,
                         "dead_at": "sieve", "layers": [], "truncated": False,
                         "n_surv": 0, "surv_sample": []})
            continue
        r = run_regime(k, n, "reg", e, o, verbose)
        r["sieve"] = "allow" if allowed else "elim"
        r["q"] = e * o
        rows.append(r)
    # ∞ 模式
    ri = run_regime(k, n, "inf", 0, n - 1, verbose)
    ri["sieve"] = "allow"
    ri["q"] = None
    rows.append(ri)
    return {"n": n, "k": k, "sieve_primes": ps, "rows": rows,
            "dead_all": all(r["dead_at"] is not None for r in rows)}


def layer_survs(k, n, mode, e, o, upto_d):
    """跑到模 upto_d 为止的幸存对（锚点用；链规则与 run_regime 一致）。"""
    layers = divisors(k)
    surv = {}
    for d in layers:
        d0 = d // spf(d)
        if d0 == 1:
            cand, _ = collect(fresh_pairs(d, n, mode, e, o), CAP)
        else:
            if not surv.get(d0):
                return []
            cand = [(C2, M2) for (C, M) in surv[d0]
                    for C2 in lifts(C, d0, d) for M2 in lifts(M, d0, d)]
        cur = check_pairs(cand, d, k, mode)
        if d == upto_d:
            return cur
        if not cur:
            return []
        surv[d] = cur
    return surv.get(upto_d, [])


def main():
    out = {"anchors": {}, "towers": {}, "o2table": {}}
    # ---- 锚点（上账前置；对 A324/A325 已审计机账）----
    out["anchors"]["k36_q0_layer3_survs"] = [tuple(map(list, p)) for p in layer_survs(36, 9, "reg", 9, 0, 3)]
    out["anchors"]["k36_q0_layer4"] = run_regime(36, 9, "reg", 9, 0)["layers"]
    out["anchors"]["k36_q0_dead_at"] = run_regime(36, 9, "reg", 9, 0)["dead_at"]
    out["anchors"]["k36_q0_layer9_survs"] = [tuple(map(list, p)) for p in layer_survs(36, 9, "reg", 9, 0, 9)]
    out["anchors"]["k15_q0_layer3_survs"] = [tuple(map(list, p)) for p in layer_survs(15, 6, "reg", 6, 0, 3)]
    out["anchors"]["k15_q0_layer5_survs"] = [tuple(map(list, p)) for p in layer_survs(15, 6, "reg", 6, 0, 5)]
    out["anchors"]["k15_q0_final"] = run_regime(15, 6, "reg", 6, 0)
    out["anchors"]["k21_q0_final"] = run_regime(21, 7, "reg", 7, 0)

    # ---- 正控（hit 承载 regime/模式必须幸存：dead_at 必须为 None）----
    for (kk, nn, ee) in [(10, 5, 2), (10, 5, 3), (6, 4, 3), (6, 4, 1), (3, 3, 1), (3, 3, 2), (3, 3, 3)]:
        out["anchors"][f"ctl_k{kk}_n{nn}_e{ee}"] = run_regime(kk, nn, "reg", ee, nn - ee)
    for (kk, nn) in [(3, 3), (6, 4)]:
        out["anchors"][f"ctl_inf_k{kk}_n{nn}"] = run_regime(kk, nn, "inf", 0, nn - 1)
    # 预期死亡观察项（census 0 命中，非正控）：inf@k=10（A314 (甲4) 五点数据之一）
    out["anchors"]["obs_inf_k10_n5_expected_dead"] = run_regime(10, 5, "inf", 0, 4)

    ctl_bad = []
    for key, a in out["anchors"].items():
        if key.startswith("ctl_") and a["dead_at"] is not None:
            ctl_bad.append((key, a["dead_at"]))
    if ctl_bad:
        print("CONTROL FAIL (tower over-kills a hit-carrying regime):", ctl_bad, file=sys.stderr)
        sys.exit(1)

    # ---- 主塔 n=6..14（全部 regime 含筛排除侧+∞）----
    for n in range(6, 15):
        out["towers"][str(n)] = tower_n(n, regimes_only_allowed=False)
        rows = out["towers"][str(n)]["rows"]
        alive = [(r["mode"], r["e"], r["o"], r["n_surv"]) for r in rows if r["dead_at"] is None]
        deadlayer = {(r["mode"], r["e"], r["o"]): r["dead_at"] for r in rows}
        print(f"n={n} k={n*(n-1)//2} alive={alive}", file=sys.stderr)
        print(f"   dead_at={deadlayer}", file=sys.stderr)

    # ---- order-2 可解表 + 筛表 n=6..60 ----
    for n in range(6, 61):
        ps = sieve_primes(n)
        rows = []
        for e in range(1, n + 1):
            o = n - e
            rows.append({"e": e, "o": o, "q": e * o,
                         "sieve": regime_allowed(n, e, ps),
                         "o2": order2_feasible(n, e)})
        killed = all((not r["sieve"]) or (r["o2"] is False) for r in rows)
        out["o2table"][str(n)] = {"sieve_primes": ps, "k_parity": ("even" if (n * (n - 1)) % 4 == 0 else "odd"),
                                  "rows": rows, "all_noninf_killed_by_sieve_o2": killed}
    fully = [n for n in range(6, 61) if out["o2table"][str(n)]["all_noninf_killed_by_sieve_o2"]]
    print("o2-fully-killed n (6..60):", fully, file=sys.stderr)
    with open("/tmp/deepA32x/a328_tower_out.json", "w") as f:
        json.dump(out, f, ensure_ascii=False, indent=1)
    print("WROTE a328_tower_out.json", file=sys.stderr)


if __name__ == "__main__":
    main()

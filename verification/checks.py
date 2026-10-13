"""Independent, bounded mathematical checks. No project research code is imported."""
from collections import Counter
from itertools import combinations
from math import comb
from pathlib import Path
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parent / 'snapshot'
OUT = Path(__file__).resolve().parent


def add(a, b):
    return a[0] + b[0], a[1] + b[1]


def mul(a, b):
    # Exact arithmetic in Z[omega], omega^2 + omega + 1 = 0.
    x, y = a
    u, v = b
    return x * u - y * v, x * v + y * u - y * v


def psi(a):
    return ((1, 0), (0, 1), (-1, -1))[a % 3]


def psum(values):
    result = (0, 0)
    for a in values:
        result = add(result, psi(a))
    return result


def inf_fourier():
    k = 3
    finite = [1, 3]
    classes = [y % k for y in finite]
    classes += [(a + b) // 2 % k for a, b in combinations(finite, 2)]
    odd_half = [(y - 1) // 2 for y in finite]
    internal = psum([(a + b) // 2 % k for a, b in combinations(finite, 2)])
    old_rho = mul(psi(1), psum(odd_half))
    new_rho = mul(psi(1), psum([2 * w for w in odd_half]))
    assert sorted(classes) == list(range(k))
    assert add(internal, new_rho) == (0, 0)
    assert add(internal, old_rho) != (0, 0)
    return dict(k=k, vertices=["inf"] + finite, classes=classes,
                printed_sum=add(internal, old_rho), corrected_sum=add(internal, new_rho))


def block_vs_vertex():
    # Even subgraph is K_{1,5}. Add a private leaf to each of its six vertices.
    edges = [(0, i) for i in range(1, 6)]
    edges += [(i, i + 6) for i in range(6)]
    degree = Counter(v for edge in edges for v in edge)
    even = {v for v in range(12) if degree[v] % 2 == 0}
    ev_edges = [edge for edge in edges if set(edge) <= even]
    ev_degree = Counter(v for edge in ev_edges for v in edge)
    assert even == set(range(6)) and len(ev_edges) == 5
    assert max(ev_degree.values()) == 5
    # EV is a tree, so its edge-blocks all have maximum degree one.
    return dict(edges=edges, even_vertices=sorted(even), ev_max_degree=5,
                block_max_degree=1, high_vertex=0)


def ring_construct():
    checked = 0
    for h in range(1, 15):
        for m in range(2 * h + 2, 2 * h + 42, 2):
            paths = []
            for t in range(m // 2):
                p = [("B", 2 * t % m)]
                for c in range(2 * h):
                    p.extend([("A", c), ("B", (2 * t + c + 1) % m)])
                assert len(p) == len(set(p))
                paths.append(p)
            used = Counter(tuple(sorted((a, b))) for p in paths for a, b in zip(p, p[1:]))
            expected = {(("A", a), ("B", b)) for a in range(2 * h) for b in range(m)}
            assert set(used) == expected and set(used.values()) == {1}
            checked += 1
    return dict(parameter_pairs=checked, failures=0)


def k4_construct():
    seeds = [[0, 4, 1, 5, 2, 6, 3, 7], [1, 6, 0, 7, 2, 4, 3, 5],
             [2, 8, 1, 9, 3, 10, 0, 5], [3, 8, 0, 9, 2, 10, 1, 7]]
    # Independently reconstruct T273's seed-plus-ring construction.
    for k in range(6, 101):
        m = 2 * k - 6
        paths = list(seeds)
        for t in range(m // 2):
            p = [11 + 2 * t % m]
            for c in range(4):
                p.extend([c, 11 + (2 * t + c + 1) % m])
            paths.append(p)
        used = Counter(tuple(sorted((a, b))) for p in paths for a, b in zip(p, p[1:]))
        assert len(paths) == k + 1
        assert all(len(p) == len(set(p)) for p in paths)
        assert set(used) == {(a, b) for a in range(4) for b in range(4, 2 * k + 5)}
        assert set(used.values()) == {1}
    return dict(k_min=6, k_max=100, parameter_values=95, failures=0)


def infinite_family_noninf():
    # Independently check the stated elementary congruence and order-two obstruction.
    primes = [p for p in range(7, 1000) if p % 4 == 3 and all(p % d for d in range(2, int(p ** .5) + 1))]
    for p in primes:
        n = p + 1
        assert n * (n - 1) // 2 % 2 == 0
        allowed = [e for e in range(1, n + 1) if e * (n - e) % p == 0]
        assert allowed == [1, p, n]
        assert int(n ** .5) ** 2 != n
    return dict(primes_checked=len(primes), largest_prime=primes[-1],
                scope="non-infinity only", failures=0)


def odd_clique_engine():
    checked = 0
    for j in range(1, 122, 2):
        infinity = 2 * j
        if j == 1:
            paths = [[0, 1]]
            prescribed = {(0, 2), (1, 2)}
        else:
            beta = (j + 1) // 2
            centers = {j - 1: 2 * j - 1, beta - 1: beta - 1}
            for i in range(3, j + 1):
                k = i - 3 if i <= beta + 1 else i - 2
                y = beta + i - 3
                centers[k] = (2 * k - y) % (2 * j)
            prescribed, paths = set(), []
            for k in range(j):
                finite = [(k + (1 if s % 2 else -1) * ((s + 1) // 2)) % (2 * j) for s in range(2 * j)]
                cycle = [infinity] + finite + [infinity]
                graph = {v: set() for v in range(2 * j + 1)}
                center = centers[k]
                for a, b in zip(cycle, cycle[1:]):
                    edge = tuple(sorted((a, b)))
                    if center in edge:
                        prescribed.add(edge)
                    else:
                        graph[a].add(b); graph[b].add(a)
                ends = [v for v, adj in graph.items() if len(adj) == 1]
                assert len(ends) == 2
                p = [ends[0]]
                while graph[p[-1]] - set(p):
                    p.append(next(iter(graph[p[-1]] - set(p))))
                assert len(p) == 2 * j
                paths.append(p)
            degree = Counter(v for edge in prescribed for v in edge)
            assert len(prescribed) == 2 * j and len(degree) == 2 * j + 1
            assert sorted(degree.values()) == [1, 1] + [2] * (2 * j - 1)
            # Connectivity plus the degree profile verifies that the corners form a Hamilton path.
            reached = {next(iter(degree))}
            while True:
                grown = reached | {v for edge in prescribed if set(edge) & reached for v in edge}
                if grown == reached:
                    break
                reached = grown
            assert len(reached) == 2 * j + 1
        used = Counter(tuple(sorted((a, b))) for p in paths for a, b in zip(p, p[1:]))
        assert all(len(p) == len(set(p)) and len(p) - 1 == 2 * j - 1 for p in paths)
        assert set(used) == set(combinations(range(2 * j + 1), 2)) - prescribed
        assert set(used.values()) == {1}
        checked += 1
    return dict(odd_j_values=checked, largest_j=121, failures=0,
                scope="j odd; this does not verify even j")


def census_ledger():
    # Arithmetic and artifact consistency only; this does not rerun the census.
    folder = OUT / 'snapshot/artifacts/deepA32x'
    rows = []
    for e, o in [(2, 7), (7, 2), (3, 6), (4, 5), (6, 3), (5, 4)]:
        path = folder / f'a328_k36_reg{e}{o}.json'
        data = json.loads(path.read_text())
        assert data['ncfg'] == comb(35, e - 1) * comb(36, o)
        assert data['nhits'] == 0
        assert sum(data['hist'].values()) == data['ncfg']
        rows.append(data['ncfg'])
    return dict(six_line_configurations=sum(rows), all_noninf=comb(71, 8),
                infinity=comb(36, 8) * 2 ** 8,
                total=comb(71, 8) + comb(36, 8) * 2 ** 8,
                verification="ledger arithmetic only; no full census rerun")


def noninf_table_accounting():
    data = json.loads((OUT / 'snapshot/artifacts/deepA32x/a328_o2table.json').read_text())
    numbers = data['_summary']['full_kill_n_6_to_200']
    from_rows = [int(n) for n, row in data.items()
                 if n.isdigit() and row['all_noninf_killed_by_sieve_o2']]
    assert numbers == from_rows
    def prime(p):
        return p >= 2 and all(p % d for d in range(2, int(p ** .5) + 1))
    primes = [n for n in numbers if prime(n - 1)]
    composites = [n for n in numbers if not prime(n - 1)]
    assert len(numbers) == 28 and len(primes) == 23
    assert composites == [112, 116, 124, 160, 188]
    return dict(full_kill_points=28, prime_previous_points=23,
                composite_previous_points=composites,
                verification='artifact accounting; does not rerun all table feasibility searches')


def lean_placeholders():
    result = []
    for file in sorted((ROOT / 'front583/lean/Front583').glob('*.lean')):
        depth = 0
        for no, line in enumerate(file.read_text().splitlines(), 1):
            stripped, i = '', 0
            while i < len(line):
                if line[i:i + 2] == '/-':
                    depth += 1; i += 2
                elif depth and line[i:i + 2] == '-/':
                    depth -= 1; i += 2
                elif depth:
                    i += 1
                elif line[i:i + 2] == '--':
                    break
                else:
                    stripped += line[i]; i += 1
            if re.search(r'\b(sorry|admit|axiom)\b', stripped):
                result.append(dict(path=str(file.relative_to(ROOT)), line=no, code=stripped.strip()))
    return result


def snapshot_integrity():
    rows = json.loads((OUT / 'manifest.json').read_text())
    for r in rows:
        assert hashlib.sha256((OUT / 'snapshot' / r['path']).read_bytes()).hexdigest() == r['sha256']
    artifacts = json.loads((OUT / 'artifact_manifest.json').read_text())
    for r in artifacts:
        assert hashlib.sha256((OUT / r['snapshot_path']).read_bytes()).hexdigest() == r['sha256']
    return dict(files=len(rows), live_changed=[r['path'] for r in rows if hashlib.sha256((ROOT / r['path']).read_bytes()).hexdigest() != r['sha256']])


if __name__ == '__main__':
    results = {}
    for name, check in [('infinity_fourier', inf_fourier), ('block_vs_vertex', block_vs_vertex),
                        ('ring_construction', ring_construct), ('k4_construction', k4_construct),
                        ('noninf_infinite_family', infinite_family_noninf), ('odd_clique_engine', odd_clique_engine),
                        ('census_ledger', census_ledger),
                        ('noninf_table_accounting', noninf_table_accounting),
                        ('lean_placeholders', lean_placeholders), ('snapshot_integrity', snapshot_integrity)]:
        try:
            results[name] = dict(status='PASS', result=check())
        except Exception as exc:
            results[name] = dict(status='ERROR', error=repr(exc))
    (OUT / 'check_results.json').write_text(json.dumps(results, indent=2, ensure_ascii=False) + '\n')
    print(json.dumps(results, indent=2, ensure_ascii=False))
    if any(r['status'] != 'PASS' for r in results.values()):
        raise SystemExit(1)

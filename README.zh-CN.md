# S(4) = 44 —— Lean 4 中的可验证穷举搜索（中文说明）

[English README](README.md)

本仓库用 **Lean 4.33.1（不需要 Mathlib）** 完整机器核验了经典结论：

> **S(4) = 44**：`{1,…,44}` 可以用 4 种颜色染色而不出现单色 `x+y=z`；
> 而 `{1,…,45}` 无论怎么染都一定会出现。

```lean
-- S4.lean
theorem no_good_four_45 : ¬ ∃ t : List (Fin 4), t.length = 45 ∧ Good t
theorem four_colors_exact :
    (∃ t : List (Fin 4), t.length = 44 ∧ Good t) ∧ Forcing 4 45
```

下界是显式着色（Baumert–Golomb 1965，本仓库用内核 `decide` 重新检查）。
上界是**可验证的穷举搜索**：搜索算法、它的规格（specification）、以及用来压缩搜索空间的
对称性约化，全部是 Lean 里的定理；唯一不经过内核的步骤是三个 `native_decide` 对搜索树
不相交分支的封闭求值。

**如果你是想审计而不是阅读**：先看 [docs/RIGOR.md](docs/RIGOR.md)——它把"内核检查了什么"、
"除内核外还信任什么（三次封闭求值）"、"哪些只是交叉验证（证据而非证明）"分开写清楚了。

### 定理索引

| 文件 | 定理 | 内容 |
|---|---|---|
| `Statement.lean` | `S4_statement` | `{1,…,44}` 可染、`{1,…,45}` 不可染（最易读的表述） |
| `Statement.lean` | `S4_all_shorter` | 任意 `N ≤ 44` 都可染 |
| `S4.lean` | `no_good_four_45` | `∀ l, l.length = 45 → ¬ Good l` |
| `S4.lean` | `four_colors_exact` | `(∃ l, l.length = 44 ∧ Good l) ∧ Forcing 4 45` |
| `Schur.lean` | `search_spec` | 搜索恰好在"合法着色"上成功（可靠性+完备性） |
| `RuleB.lean` | `searchB_spec` | 受限搜索恰好在满足 `Ok23` 的合法着色上成功 |
| `Symmetry.lean` | `exists_good_first_two` | 12 重对称约化 |
| `RuleB.lean` | `exists_good_first_two_ok23` | 24 重对称约化 |
| `Verify.lean` | — | 打印以上所有定理的公理/信任基 |

## 约定

| 约定 | 定义 | 值 |
|---|---|---|
| `S(4)`（OEIS [A045652](https://oeis.org/A045652)） | 使 `{1,…,N}` 存在"无单色 `x+y=z`"4-着色的最大 `N` | **44** |
| `S'(4)`（OEIS [A030126](https://oeis.org/A030126)） | 使**任意** 4-着色都出现单色解的最小 `N` | **45** |

两者在这里都证明了（即 `four_colors_exact`）。

## 证明路线

![证明流水线](docs/figures/pipeline.svg)

1. **`Schur.lean`**：`Good`（要避免的性质）、可计算判定 `checkGood` 及其**可靠性与完备性**
   （`checkGood l = true ↔ Good l`）、增量可行性 `extendOk`、回溯搜索 `search`，
   以及它的规格定理
   `search_spec : search r n l = true ↔ ∃ t, t.length = n ∧ Good (l ++ t)`；
   顺带定出 `S(1)=1, S(2)=4, S(3)=13`。
2. **`Symmetry.lean`（12 重约化，已证明）**：`1+1=2` 迫使前两个颜色不同，于是某个颜色置换
   把它们送到 `0,1`（`exists_good_first_two`）。置换表用 12 个显式置换做有限查表，
   查表的正确性由**内核** `decide` 验证（不用 `native_decide`）；重标记不变性
   `good_map_iff` 对单射 `f` 已证。
3. **`RuleB.lean`（再 12 重，已证明）**：此时颜色 `2,3` 可互换，故可假设"颜色 3 不在颜色 2
   之前出现"（`Ok23`，`ok23_disj`）；受限搜索 `searchB` 同样带规格定理 `searchB_spec`。
4. **`BranchB0/1/2.lean`（三段穷举）**：`[0,1]` 前缀之下剩 **220 859 322** 个状态；
   按第 3 个整数的颜色（只能是 `0,1,2`）切成三个互不相交的分支，各自一个
   `native_decide`，三个文件可并行编译。
5. **`S4.lean`（组装）**：已证明的组合引理 `searchB_false_of_three` 把三段结果合并成
   `no_good_four_45`，再配上 `[1,44]` 的显式着色（内核 `decide` 复验）得到
   `four_colors_exact`。

## 穷举到底有多大

![搜索树规模](docs/figures/reductions.svg)

| 约化 | 状态数 | 倍数 | 是否在 Lean 中验证 |
|---|---:|---:|---|
| 无 | 5 300 623 637 | 1× | — |
| 固定 `c(1)=0` | 1 325 155 910 | 4× | — |
| 固定前两色为 `0,1` | 441 718 638 | 12× | 约化已证明 |
| **+ 换位 `(2 3)`** | **220 859 322** | **24×** | **约化已证明，树被验证** |

一个很好的自检：搜索树最深非空层恰好有 **273** 个状态，而 273 正是文献公布的
`{1,…,44}` 合法 4-着色数（Eliahou 2016）。

![搜索树剖面](docs/figures/tree_profile.svg)

## 信任基

![信任基](docs/figures/trust_base.svg)

`Verify.lean` 打印的结果：

```
'Schur.four_colors_exact' depends on axioms: [propext, Classical.choice, Quot.sound,
    branchB0._native.native_decide.ax_1_1,
    branchB1._native.native_decide.ax_1_1,
    branchB2._native.native_decide.ax_1_1]
```

即：除了 Lean 逻辑的标准公理，唯一被信任的是"编译器忠实地求值了这三个封闭的
`Bool` 表达式"。搜索算法的正确性、两条对称性约化、组合引理、`[1,44]` 着色的检查，
全部在内核中完成。没有外部 SAT 求解器、没有 LRAT/DRAT 证书、没有外部数据文件。

## 复现

```bash
lake build Schur Symmetry RuleB          # 内核部分（很快）
lake build S4 Verify                     # 含三段穷举（数分钟到半小时，取决于机器）
# 或者显式并行跑三段：
pwsh -File scripts/build_all.ps1
```

实测（开发机，16 逻辑核）：内核部分约 10 秒；三段穷举分别为 588 s / 1183 s / 959 s，
并行后墙上时间约 20 分钟；组装与信任基检查约 3 秒（见 `bench/branch_timings.txt`）。

独立的非 Lean 交叉检查（JavaScript / Python）：

```bash
node bench/measure.js AB 45 --profile    # 220 859 322 个状态 + 逐层剖面
node bench/branches.js 45                # 47 033 043 / 95 553 318 / 78 272 958
node bench/reference_search.js 4 45      # 穷举：44 有 273 个着色，45 有 0 个
python3 bench/verify_coloring.py bench/data/c4_44.txt
python3 scripts/make_figures.py          # 重新生成 docs/figures/*.svg
```

## 明确不声称的东西

* **不是新数学**：`S(4)=44` 是 1965 年 Baumert–Golomb 的结果；这里新的是**形式化**——
  搜索是被证明的算法，而不是被信任的程序。
* **三次 `native_decide` 不是内核归约**：它们信任 Lean 编译器（这是社区通行做法，
  也是它们会出现在 `#print axioms` 里的原因）；但它们所服务的规格定理是内核检查过的。
  这条信任边界的失效模式、以及如何消除它（证书 + 已验证检查器），见
  [docs/RIGOR.md](docs/RIGOR.md)。
* **不涉及 `S(6)`**：`S(6)` 是著名的公开问题（只知道 `536 ≤ S(6) ≤ 1927`），本仓库只做 `S(4)`。
* "任意 14 个连续整数必须用满 4 色"这条看起来很像 `S(3)=13` 的推论，但它**是错的**：
  把窗口平移到 `[1,14]` 不保持 `a+b=c`。`bench/window_check.js` 在 `[1,44]` 的合法 4-着色里
  找到了 344 个反例（例如窗口 `[15,28]` 只用了 3 色）。因此该规则**没有**被使用——
  详见 [docs/OPTIMIZATION.md](docs/OPTIMIZATION.md)。

## 目录结构

```
Schur.lean          定义、checkGood、search + search_spec、S(1),S(2),S(3)
SchurData.lean      显式着色（生成；每个都被独立暴力验证 + Lean 验证）
Fin4.lean           Fin 4 的元素必为 0,1,2,3 之一
Symmetry.lean       12 重对称约化（内核检查）
RuleB.lean          24 重对称约化 + 受限搜索 searchB（内核检查）
BranchB0/1/2.lean   三段穷举（native_decide）
S4.lean             no_good_four_45、four_colors_exact（S(4)=44）
Statement.lean      用显式长度重述的结论（最易读）
Verify.lean         信任基报告
docs/               PROOF.md（证明过程）、RIGOR.md（严谨性审计）、OPTIMIZATION.md（优化分析）、figures/
bench/              独立的 JavaScript / Python 交叉检查
scripts/            构建脚本与图表生成器
```

## 参考文献

* L. Baumert, S. Golomb, *Backtrack programming*, J. ACM 12 (1965) 516–524.
* M. J. H. Heule, *Schur Number Five*, AAAI 2018（`S(5)=160`，以及更高 `S(k)` 的上界讨论）。
* S. Eliahou, *Les nombres de Schur, des centenaires pleins d'avenir*, Images des
  Mathématiques (2016)（273 个 `[1,44]` 四着色）。
* OEIS [A045652](https://oeis.org/A045652)、[A030126](https://oeis.org/A030126)。

## 许可

[MIT](LICENSE)。

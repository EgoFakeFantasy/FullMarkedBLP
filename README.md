# 普通完整标记 BLP：自然截断良序的 Lean 形式化

主稿 `full_marked_blp_natural_cutoff_wellorder.md` 的定理 4.1、5.1 已完成。
本项目采用主稿改造后的普通 E/M_star 生成系统；BLP 原仓库仅作为原型参考。

公开仓库：[EgoFakeFantasy/FullMarkedBLP](https://github.com/EgoFakeFantasy/FullMarkedBLP)。
原型参考：[QiRenrui/basic-laver-pattern](https://github.com/QiRenrui/basic-laver-pattern)，
参考提交 `3c4c96a4d9039b154995aa44d4895ec66ac5f579`。

## 最终定理

文件：[FullMarkedBLP/ShortKeyWellOrder.lean](FullMarkedBLP/ShortKeyWellOrder.lean)

```lean
theorem rankI2_full_marked_blp_natural_cutoff_wellorder (i2 : RankI2.{u}) :
    WellFounded (fun child parent : GeneratedPattern => Step parent.val child.val) ∧
    IsWellOrder GeneratedPattern GeneratedKeyLT ∧
    Function.Injective (fun a : GeneratedPattern => shortKey a.val) ∧
    (∀ a b : GeneratedPattern,
      shortKey b.val ≤ shortKey a.val ↔ Reachable a.val b.val)
```

`GeneratedPattern` 就是从主稿五行根出发、经原始 `Step` 有限次生成的全部
字面项；没有另加语义过滤。`GeneratedKeyLT` 是原稿逐行、逐条目的字典序，
真前缀较小。行键是 `(core.drop step).reverse ++ core.take 1`。
键忽略 marks，但最终单射性针对包含 marks 的整个字面项。

## 证明路径

| 阶段 | 已证明的内容 | 主要入口 |
|---|---|---|
| 语法 | 普通行型、正确一基复制筛选、cut、固定辅助行 E、完整 M_star 扫描 | Syntax、MarkedCopy、Expansion、Scan |
| 局部语义 | 自然截断、准确 trace、全部旧/新边、Sat、合法性、完整同端点有限见证保持 | FullRankRealization |
| Steel 基础 | 实际 application、临界点不可达性、Kunen 共尾性、同域有界 application 良基 | RankSteelWellFounded |
| I2 起点 | 有限公式表达、反射、相容根族、全部共同端点见证、原始五行根实现 | RankI2Root |
| 展开良基 | 主稿定理 4.1，所有实际生成状态上的反向 Step 良基 | rankI2_generatedStep_wellFounded |
| 比较桥 | 同父子项前缀嵌套、全域可达性比较、每个实际操作严格降低短键 | GeneratedReachability、MStarShortKey |
| 最终良序 | 比较等价于可达性、短键单射、主稿定理 5.1 | ShortKeyWellOrder |

首复制行的条目像避开父最小项，因而其键严格变小。native 首行保持完整
短键，后续扫描不改更早行。E 的第一辅助行给出严格下降，所有后续参数
保留该行。可达性比较使用已经证明的展开良基性作归纳，不预设短键单射。

## 验证与复现

Lean 与 Mathlib：v4.30.0。安装 Lean 的 elan 工具链管理器后，首次获取：

```text
git clone https://github.com/EgoFakeFantasy/FullMarkedBLP.git
cd FullMarkedBLP
lake exe cache get
```

然后在项目目录运行：

```text
lake build
lake env lean CheckMainTheorem.lean
lake env lean Audit.lean
```

`lean-toolchain` 固定 Lean 版本，`lake-manifest.json` 固定全部依赖提交。
本机 `.lake` 缓存不随源码上传。GitHub Actions 使用
[Lean 官方 lean-action](https://github.com/leanprover/lean-action) 构建项目，
并扫描证明缺口、运行最终定理检查与公理依赖审计。

2026-09-10 验收结果：

- 全量构建通过：1500 项。
- `CheckMainTheorem.lean` 通过：将生成域、短键与可达关系展开后核对最终类型。
- 编译环境审计通过：4067 个定理常量，包含编译器生成的辅助定理。
- 公理依赖仅为 Lean 标准的 `propext`、`Classical.choice`、`Quot.sound`。
- 源码中没有 `sorry`、`admit`、`unsafe`、`native_decide` 或自定义 `axiom` / `constant`；构建没有错误或 PANIC。

核验记录：[build-latest.txt](build-latest.txt)、[audit-latest.txt](audit-latest.txt)、
[main-theorem-check.txt](main-theorem-check.txt)。

## 证明保持精简

原始发布提交 `b006cc0` 的 514 个 Lean 文件共 33,501 行。
本轮完成后为 32,502 行，净减 999 行（2.98%）；
非空行从 30,205 减至 29,269，净减 936 行。
统计仅包含版本控制中的 Lean 源码，不包含依赖、缓存和外部候选文件。

公共事件组装、native 几何事实、精确端点推论和行实现分层代替重复证明；
保留原有数学声明及解释性接口。五个存在定理按命名规范整体迁移。
与原版对照的 2,116 个语义对象，包括类型、宇宙参数和非定理定义体，均保持一致；
原有结构字段与最终定理前提也在检查范围内。原有 18 条提示没有增加。

逐轮减行和验收见 [REFACTORING.md](REFACTORING.md)，代换依据与保留理由见
[SEMANTIC_REVIEW.md](SEMANTIC_REVIEW.md)，命名迁移见 [ProofNaming.md](ProofNaming.md)。

## 精确范围

I2 采用文献中的非平凡 Σ₂ 初等秩嵌入表述，定义于 RankSecondOrder.lean。
其与全局类嵌入 `j : V → M` 表述的等价性不在本项目的形式化范围。
最终定理没有额外的 root、Steel、可表达性或比较下降前提。

起点使用原稿完全相同的五行字面根，并构造足够的真实语义见证；没有把
原型中的 `g_(11)` 精确数值估计作为结论。详细说明见
[I2_FOUNDATION.md](I2_FOUNDATION.md) 和 [STATUS.md](STATUS.md)。

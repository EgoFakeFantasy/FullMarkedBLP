# Proof naming convention

本项目参考 [PCF 的规范](https://github.com/EgoFakeFantasy/PCFAlephOmega4/blob/main/ProofNaming.md)
和 [BMS 的规范](https://github.com/EgoFakeFantasy/BMS-Well-Ordering-Lean/blob/main/ProofNaming.md)。
共同原则是按数学意义命名、避免实现历史名称、按完整接口迁移、不增加兼容包装。

BLP 使用 Mathlib 的宿主数学对象；有限公式也是宿主中的数据与满足关系，
没有 BMS/YesMetaZFC 的三层推导判断架构。因此采用 PCF 的命名方式，
不额外添加 `_l`、`_m`、`_d` 层后缀。

- 文件、类型、结构、主要谓词采用 `UpperCamelCase`。
- 构造和计算函数采用 `lowerCamelCase`。
- 定理名用下划线连接数学子句；`shortKey`、`mStar`、`rankI2` 等稳定领域词保持整体。
- `_of_` 表示充分条件，`_iff_` 表示等价，`_eq_`、`_lt_`、`_le_` 表示关系方向。
- 构造性存在定理优先使用 `exists_`；不在声明名重复命名空间。
- 局部数学对象使用 `a`、`r`、`theta`、`lambda` 等短名称；证明假设使用
  `hValid`、`hSat`、`hStep` 等简短语义名。已清楚的数学符号无需为统一外观而改写。
- 不用 `final`、`proved`、`v2`、`tmp`、`helper` 等表示开发历史。
  `old`/`new` 若表示操作中继承的行与插入的行，属于数学区分；必要时改成
  `before`、`inherited`、`inserted`，不能只按关键词删除。
- 公开语义接口保留说明结论与真实前提的 docstring。不可通过压缩变量名、
  删除解释或堆叠不透明 tactic 来制造减行。
- 每次按完整接口更新名称、调用点与文档，验证后不保留旧名兼容别名。

## 本轮存在定理迁移

| 原名 | 当前名称 |
|---|---|
| `rankCoherentRoots_of_reflection` | `exists_rankCoherentRoots_of_reflection` |
| `rankCoherentRoots_of_sigmaTwo_and_definability` | `exists_rankCoherentRoots_of_sigmaTwo_and_definability` |
| `rankCoherentRoots_of_sigmaTwo_and_lowRank_definability` | `exists_rankCoherentRoots_of_sigmaTwo_and_lowRank_definability` |
| `rankCoherentRoots_of_sigmaTwo` | `exists_rankCoherentRoots_of_sigmaTwo` |
| `rankI2_full_root` | `exists_full_root_of_rankI2` |

其他清楚的领域名称和局部数学符号保留；主定理名称保持稳定。

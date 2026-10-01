# 原证明、Jacobi 新证明与 Lean 的对应

## 命题和模型没有替换

`Wong/MainStatement.lean` 与原已核验主命题文件逐字相同。`mainClaim` 量化任意观察维数 `m`、任意全局光滑漂移和观察函数，并使用这些函数实际生成的 `estimationAlgebra f h`。它要求有限维、齐次线性秩二和 `QuadraticFree`，推出 `WongConstant f`。

`QuadraticFree` 排除的是总次数恰为二的任意多项式乘法算子，不仅是齐次二次多项式。`linearRank` 是齐次一次乘法函数对应系数空间的维数。`WongConstant` 是存在实常矩阵，对全部空间点逐项相等。未将任何定义改成较弱命题或直接写成待证结论。

新证明在同一模型上替换 `normalized_slope_zero_of_constant_heads` 的证明体，原声明的参数、假设和结论不变。完整上层定理先证明所需的常数主系数，再调用该内部引理，因此常数主系数不是主定理新增的假设。

## 逐步对应

| 论文步骤 | Lean 实现 | 说明 |
|---|---|---|
| `D_i=∂_i−f_i`、`L_0`、乘法算子与实际 Lie 代数 | `Wong.SmoothModel.MainStatement` 文件内的定义 | 算子作用在真正的全局光滑函数空间上 |
| `x_1,x_2,D_1,D_2,1∈E` 与函数空间约束 | `CoordinateGenerators`、`Ocone`、`RankStructure` 等保留模块 | 由原假设推出，不作为新的未证公理 |
| 仿射 Wong 结构 | `PublishedAffineInput.shi_yau_affinity` 及 `shi_yau_affine_structure` | 本项目闭包中为内部证明的 theorem；其文献陈述另见输入核查报告 |
| 正交归一化到 `w=bx_2+b_0` | `VisibleRotation.normalized_visible_model` | 从非零斜率反设推导；没有预先假设目标斜率消失 |
| 主符号刚性，所需两个系数为常数 | `VisibleElimination.normalized_heads_constant` | 包含纯方向阶数增长和混合主符号阶数增长 |
| `w` 对第二坐标仿射 | `jacobi_visible_multiplier` | 实际乘法算子等式 |
| `[D_2,J_11]−[D_1,J_12]=−2bw` | `Wong.JacobiVisible.first_identity`；实际模型内 `hfirst` | 仅 Jacobi、斜对称性、线性和基本交换子 |
| 双坐标交换子等于 `2[D_2,J_11]` 和 `2[D_2,J_12]` | `normalized_slope_zero_by_jacobi` 内 `hhead01`、`hhead11` | 没有调用旧 `head01`、`head11` 的 η 系数公式 |
| 再交换得到 `−2b²·1=0` | `Wong.JacobiVisible.second_identity`；实际模型内 `hlast` | 使用真实恒等算子；作用于常数函数并在原点取值，得到实数等式 |
| 实数平方为零推出 `b=0` | 实际模型证明最后的 `nlinarith` | 基于实数有序域性质，不是额外数学公理 |
| 去除归一化 | `VisibleHeads.visible_slopes_zero` | 得到原仿射参数的两个可见斜率同时为零 |
| 接入原主定理 | `SectorIHiddenBridge` → `MainProof.main_theorem` | 上层证明陈述未修改，继续处理其余 Wong 分量 |

表中部分名称是文件名或定理的所在模块提示；完整命名和实际依赖以源文件及 `verification/proof-routes.log` 为准。

## 约定差异的核对

- Lean 指标 `0,1,2` 对应论文 `1,2,3`。
- Lean 的 `δ i A` 是 `[A,x_i]`。论文混合双交换子的两个坐标次序与某些 Lean 表达式相反，但坐标乘法算子相互交换，Jacobi 恒等式给出 `[[A,x_1],x_2]=[[A,x_2],x_1]`。
- 论文的 `H_0,H_1` 减去常数项；Lean 使用未减常数的 `[L_0,D_i]`。中心常数与任何算子交换，故所有 `J`、`X`、`Y` 及所用等式不变。
- 论文的 `D_2²` 系数由双交换子提取时出现因子 `2`，混合 `D_1D_2` 系数没有该额外因子。Lean 直接核对双交换子等式，避免将系数归一化混淆。

## 不能从零占位符单独推出的事

`sorry=0` 和正常公理依赖只保证所写形式命题的证明被 Lean 接受。它们本身不保证该形式命题就是原问题。本项目另外保留原始命题文件哈希、核查真实算子定义和文献前提、提供逐步对应，并检查实际证明项确实经过新的 Jacobi 核心。数学前提出处见 `published_input_audit.md`。

本文新收尾没有新增前提，但仍使用原有主符号刚性；不应据此声称得到一个完全独立于原阶数增长机制的新理论证明。

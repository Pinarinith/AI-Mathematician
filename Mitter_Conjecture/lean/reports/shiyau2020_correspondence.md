# Shi–Yau 2020 原文与 Lean 对应审计

> 最终状态补充：2026-09-29 17:31:25 UTC，本轮165个本地模块全量重编、1659个定理/引理公理审计及准确类型/证明路线审计全部通过。以下记录保留撰写时的审查范围；其中“最终待验收”描述属于历史状态。当前正式结果见 `final_acceptance.md` 与 `../verification/acceptance.json`。

审计对象：J. Shi and S. S.-T. Yau, *Finite dimensional estimation algebras with state dimension 3 and rank 2, Mitter conjecture*, International Journal of Control 93(9), 2177–2186. DOI: https://doi.org/10.1080/00207179.2018.1550268 。页码均为期刊页码。

本报告区分原文命题、所选形式证明路线和构建验收。源码对应核对本身不等于 Lean 编译通过；最终通过状态应以本工程从冻结源码完整重编后的验收记录为准。开发缓存和旧工程的编译产物不能充当本工程的最终证书。

## 1. 主要命题的范围

| 原文 | Lean 命题及证明 | 范围核对 |
|---|---|---|
| Theorem 1.2, p.2178；Theorem 3.10, p.2184 | `ShiYau2020MitterClaim`；`shiYau2020_mitter_theorem` | 对任意观测维数 `m`、真实全局光滑漂移 `f` 与观测 `h`，只以实际估计代数有限维及线性秩 2 为前提，推出每个实际乘法函数元为总次数至多 1 的多项式。没有 `QuadraticFree` 前提。 |
| Theorem 3.7, p.2182 | `ShiYau2020QuadraticClaim`；`shiYau2020_quadratic_theorem` | 增加一个实际总次数恰为 2 的多项式乘法元存在的前提，结论为 Wong 矩阵恒定且各观测函数仿射。 |
| Theorem 1.1, p.2178 | `ShiYau2020WongQuadraticClaim`；`shiYau2020_wong_quadratic_theorem` | 为上一结论的 Wong 恒定部分；单独保留与引言文字精确对应的目标。 |

`ShiYau2020ModelReduction.lean` 中这些 `Claim` 是待证明命题的定义，不是公理。`FunctionElementsAffine` 用次数 `≤ 1` 表示仿射，包含常数与零函数；原文引言的 “degree one” 按正文 Theorem 3.10 的仿射含义理解。

真实模型使用 `estimationAlgebra f h`，即由过滤算子 `L0 f h` 和观测乘法算子生成的 Lie 子代数；不是任意抽象、可以自由指定势函数的微分算子空间。势函数 `eta f h` 保留原模型的漂移、散度与观测平方关系。对随机过程存在性、DMZ 方程解或算法误差的结论不包含在这些命题中。

## 2. 原文依赖与所选形式路线

| 原文环节 | 当前源码入口 | 对应与差别 |
|---|---|---|
| §2 基本交换子、函数元次数界和 Euler 工具，p.2178 | `MainStatement`、函数多项式与阶数模块、`SmoothCoordinateEuler` 等 | 复用实际模型上的内部定理。文献署名不等于外加公理；最终必须核查这些依赖也在已验证闭包中。 |
| 2020 Theorem 2.8 的无可见–隐藏混合二次项，以及前篇 Wong 仿射结构 | `FunctionQuadraticRankConstraints`；`PublishedAffineInput.shi_yau_affine_structure` | 前篇可见仿射性为 Shi–Yau 2017 Theorem 3.4（p.4233），混合分量仿射性为其 Theorem 3.10（pp.4243–4245）。所选路线使用内部证明给出的仿射结构，不把文献结果另设为公理；没有预先调用本次待证的 2020 函数元仿射结论。 |
| Lemma 3.1 五分支分类，p.2179 | `QuadraticFunctionClassification`、`QuadraticFunctionCaseSplit.actual_quadratic_function_cases` | 从真实二次函数元推出某个真实平移及可见平面正交旋转后的模型满足 A、B2、B1、C1、C2 之一；有限维、秩和可见坐标成员身份均随模型变换传递。 |
| Lemma 3.4：A；Lemma 3.5：B；Lemma 3.6：C，pp.2179–2182 | `HiddenRadialEtaConclusion`、`PlaneRadialWongRigidity`、`B2EtaAnalysis`、`C1Constancy`、`C2Complete` | 分别证明各分支所需实际 Wong/势函数刚性。形式证明允许重新组织交换子和分析论证，不主张逐行照译原文。 |
| Lemmas 3.8–3.9 的势函数控制，pp.2182–2184 | `HiddenRadialEtaConclusion`、`B2EtaAnalysis`、`C1EtaWords`、`C1EtaConclusion`、`ConstantWongHiddenIndependentEtaClosure` | 保留全局光滑性，使用 Euler 核刚性、实际阶数增长、积分/Riccati 不等式和精确 Lie 闭包。C1 可见 Hessian 恒定并不先假定隐藏势函数为多项式。 |
| Theorem 3.10 的分支排除，p.2184 | `classification_model_functionElementsAffine`；`classification_model_case_not_functionElementsAffine`；`shiYau2020_adapted_mitter_theorem` | 各分支均推出所有实际函数元仿射，再与该分支的真实二次成员矛盾；最后消去临时适配坐标。 |

主定理的形式证明顺序是：独立五分支排除二次函数元 → Theorem 3.10 → Theorem 3.7 → Theorem 1.1。原文先证明 3.7，再利用其后果证明 3.10。形式证明在已经独立证明 3.10 后，直接从“不存在实际二次函数元”消去 3.7 的前提，得到其完整蕴涵。这是有效的替代推导，不能宣传成复现原文 3.7 的逐行证明。用于五分支的刚性引理本身不能以最终 3.7 或 3.10 为前提。

C1 的实际链条为：由可见径向二次成员构造 `c1RadialZ`，交换子给出每个可见 `∂ᵢη` 的可见 Euler 乘法元；函数元次数界与正 Euler 移位核刚性推出可见四阶导和隐藏方向的可见 Hessian 导数消失。因此可见三阶导为常数。接着对真实 `eta f h` 的平移测试积分使用 Riccati 约束，先消去观测的二次部分，再消去势函数的可见三次部分，得到 `c1_eta_visible_hessians_constant`。这里 `HiddenIndependentFunctionSpace` 来自 C1 分类分支，而非主定理的新增前提。

## 3. 退化与坐标情况

- **隐藏二阶导全为零**：由全函数空间条件推出真实隐藏方向独立，再处理可见二次型；不是未经证明地删去线性隐藏尾项。
- **隐藏二阶导不全为零**：保留 `d x₃² + g x₃`，对 `d ≠ 0` 的情形通过真实模型平移消去中心，之后做投影和可见旋转。
- **可见二次型退化**：分类明确区分整个二次函数空间均奇异与存在非奇异成员；奇异分支传递的是整个空间条件，不仅是任选一个二次元的行列式为零。C2 包含实际单平方成员及全函数空间限制。
- **隐藏平方分支**：A 包含整个可见 Hessian 消失的限制；若还有非零可见二次型，则继续分为 B2 或 B1，而不将它误归 A。
- **两种 B2 坐标位置**：`x₂²+x₃²` 通过真实可见四分之一旋转转换到统一的 `x₁²+x₃²` 分支；对应模型不丢失有限维与秩条件。
- **混合常曲率**：共享结论 `functionElementsAffine_of_constant_wong_hidden_independent_visible_hessians` 内部区分 `ω₁₃ ≠ 0`、`ω₁₃ = 0, ω₂₃ ≠ 0`、两者均为零。前两者证明全局二次势函数，最后一种允许任意隐藏剖面并建立可见闭包；没有另加非零曲率假设。
- **返回原坐标**：`shiYau2020MitterClaim_iff_adapted` 从原线性秩取得适配坐标，并通过真正的算子/函数拉回等价传递仿射结论；最终命题不要求用户预先指定适配坐标。

## 4. 与已有 quadratic-free 主定理的独立性

源级检查显示 `ShiYau2020MainProof` 直接使用五分支定理及坐标等价，不调用已有 quadratic-free 主定理的证明。其依赖中出现 `MainStatement` 的 `mainClaim` 定义、适配命题等价式或条件性归约引理，并不等于假设该主定理成立。`QuadraticFree` 在 `quadraticFree_iff_functionElementsAffine` 处是**正在证明的中间目标**，不是 2020 最终定理的输入假设。

最终验收必须查实际证明项依赖闭包，确认不依赖原 conditional main 的已证明常数，也不依赖任何外加的 2020 结论或文献公理。只搜索源文件中的 `mainClaim` 字样或只查看 import 图不足以完成这一检查。

## 5. 验收边界

接受范围是上述 2020 主要数学定理，以及所选证明路线实际需要的全部依赖。必须使用冻结源码完整重编，所有相关声明无 `sorryAx`，无新增数学公理，仅允许 `propext`、`Classical.choice`、`Quot.sound` 这些基础依赖，并记录源码及产物哈希。辅助引理是否与原文逐条同名，不作为完成标准；其数学作用及替代路线须如实披露。

不包含论文中的 EKF/PF 数值实验、图表复现、鲁棒 DMZ 解的滤波器构造或随机过程理论。这些若将来需要验证，应另行定义命题与验收标准。

## 6. C1 开发编译记录

两个 C1 模块均已通过本轮开发编译；本节不代替最终完整重编验收。

| 模块 | 开发状态 | 日志 | 源码 SHA-256 |
|---|---|---|---|
| `C1EtaWords` | 通过 | `development/Wong-C1EtaWords-20260929T214745.log` | `cd3f14b9ec6165cebfa152ae6407e1946ef979825c2c8e8340b1bdcb3b056e44` |
| `C1EtaConclusion` | 通过 | `development/Wong-C1EtaConclusion-20260929T215129.log` | `8fb463d597015566cdd4d4cd85bf7a3e803d1a4ce46929f4764cd4efbbd0cdca` |

`C1EtaWords.lean` 仅修复 `c1RadialZ_lie_D` 末尾的证明策略：先用 `abel_nf` 规整加法，再以 `ext u x` 及 `Module.End.mul_apply` 逐点核对负单位算子的作用。所有定义和定理签名保持原样。`C1EtaConclusion.lean` 与原始源码相同，未修改。

成功日志显示 `c1_eta_visibleEuler_partial_member_of_constant_wong`、`c1_eta_visible_third_partials_constant`、`c1_eta_visible_directional_third_constant` 和最终 `c1_eta_visible_hessians_constant` 的公理依赖仅为 `propext`、`Classical.choice`、`Quot.sound`，没有 `sorryAx`。日志仍含无害的未使用 simp 参数和弃用名称提示，因此不称为“零警告”。开发依赖含预置缓存，最终认证仍须使用完整源码重编及完整证明项闭包审计。


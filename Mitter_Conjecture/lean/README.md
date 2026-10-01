# Wong 主定理与 Shi–Yau 形式化核对

本版本把公开的 `mainClaim` 和 `main_theorem` 改为论文的完整陈述：三维全局光滑过滤模型，估计代数有限维、线性秩为二，即推出 Wong 矩阵恒定。公开主定理没有 `QuadraticFree` 前提。

本次完整验证已通过：165 个本地模块全部从源码重编，1,661 个定理／引理的公理依赖、公开定理展开类型及实际证明依赖均通过检查。验收完成于 2026-10-01 07:49:16 UTC，证据见 `verification/acceptance.json`。

## 定理入口

- `Wong/MainStatement.lean`：模型定义、仅含有限维和秩二条件的 `mainClaim`。
- `Wong/MainProof.lean`：最终 `main_theorem`，以及从有限维和秩二推出 `QuadraticFree` 的 `quadraticFree_of_finiteDimensional_rank_two`。
- `Wong/ShiYau2020MainProof.lean`：独立证明 Shi–Yau 2020 的函数元素仿射定理 `shiYau2020_mitter_theorem`。
- `Wong/PublishedAffineInput.lean`：内部证明 Shi–Yau 2017 的 Wong 仿射结构定理。
- `Wong/UnconditionalMainProof.lean`：保留 `unconditional_main_theorem` 作为最终主定理的兼容名称。

原先带 `QuadraticFree` 的命题明确改名为 `QuadraticFreeMainClaim`，对应 `quadraticFree_main_theorem`，仅作消去斜率时的中间结果。最终证明先通过 Shi–Yau 2020 结果得出全部函数元素仿射，继而得到 `QuadraticFree`，再应用该中间结果。

## 与原文的对应

核对范围是 Shi–Yau 2017 的 Theorems 3.4/3.10，以及 2020 的 Theorems 1.1/1.2/3.7/3.10 和这些结论依赖的结构证明。这里不声称形式化了两篇文章中的全部数值实验和滤波器构造。

模型保留真实过滤生成元、势函数与漂移及观测的关系、全局光滑性，以及原文的齐次线性秩定义。Lean 坐标 `0,1,2` 对应论文坐标 `1,2,3`。

2020 年函数元素仿射定理通过实际二次函数元素的五种穷尽分类来反证，未预设 `QuadraticFree` 或分类分支。它的证明不依赖我们的主恒定定理。2020 年二次函数条件下的恒定结论由已证明的函数元素仿射性推出；这一证明顺序与原文不同，但命题范围相同。

## 验证方式

完整本地源码重编与全部审计：

```sh
./check.sh --clean --jobs 4
```

`--jobs` 只并行编译依赖已经通过检查的模块；每个 Lean 进程仍使用 `-j1`。最终导入路径仅使用本轮 `.lake/verified` 工件和固定第三方依赖。

`ProofRouteAudit.lean` 检查公开命题及主定理的展开类型，明确要求只有有限维和秩二；同时追踪实际证明项，要求主定理调用独立的 Shi–Yau 2020 定理，并排除循环依赖。`AxiomAudit.lean` 检查本地全部源码定理和引理的传递公理。

`frozen-statements.json` 和验证脚本中的声明哈希已经按本次公开接口修改更新；这是一项明确的命题修订，不能使用旧验收证书。

只读核对成功证书、源码、工件和交付清单：

```sh
python3 validate-package.py
```

完整验证通过后，才可用 `python3 validate-package.py --manifest` 刷新交付清单。

## 信任范围

编译器固定为 Lean 4.35.0-rc2；本地 Wong 模块全部从源码重新编译。允许的基础公理仅为 `propext`、`Classical.choice`、`Quot.sound`。检查拒绝 `sorry`、额外数学公理及列明的绕过内核检查入口。

Mathlib 及其依赖使用固定版本的既有编译缓存；源码版本、环境与本地依赖工件哈希受到检查，但本次没有从源码重建 Lean 编译器或所有第三方库。机械验证与原文语义对应的核对分别记录，不将“通过编译”表述为“整篇论文逐行形式化”。

此前的审计报告和开发记录保留作历史材料；本次主接口审计见 `reports/main_interface_audit_2026-10-01.txt`，实际验收状态以当前 `verification/acceptance.json` 为准。

# 主定理组装的开发记录

> 最终状态补充：2026-09-29 17:31:25 UTC，本轮165个本地模块全量重编、1659个定理/引理公理审计及准确类型/证明路线审计全部通过。以下记录保留撰写时的审查范围；其中“最终待验收”描述属于历史状态。当前正式结果见 `final_acceptance.md` 与 `../verification/acceptance.json`。

这是开发阶段记录，不能代替 `verification/acceptance.json` 绑定的最终全量重编译及公理审计。开发导入路径包含预置历史工件，最终验收路径不包含该缓存。

## 命题与连接

`shiYau2020_mitter_theorem` 独立证明 2020 年 Theorems 1.2/3.10 的全部函数元仿射结论；`shiYau2020_quadratic_theorem` 和 `shiYau2020_wong_quadratic_theorem` 分别给出 Theorem 3.7 与引言 Theorem 1.1 的准确条件命题。

新增 `unconditional_main_theorem` 由 2020 年结果导出二次自由性，再应用当前 Jacobi 版本的条件 Wong 主定理。`omega12_constant_without_quadraticFree` 是其可见矩阵元投影。两个新增定理都只要求真实三维光滑模型的估计代数有限维、线性秩为二。

组装首次编译在 `hqE` 的算子等式运输处失败。修复只显式展开多项式函数元成员定义，再重写算子等式；未改变任何定理签名。独立审计报告已通过逆向恢复旧源码哈希确认唯一差异。失败编译的临时产物没有被接受进开发缓存。

## 成功记录

| 模块 | 秒数 | 源码 SHA256 | 开发日志 |
|---|---:|---|---|
| `Wong.ShiYau2020MainProof` | 124.811 | `e57306d3ad18964e67cce958caa16e4c104f259ec9f7aa7da377acc5cc2e2d5b` | `development/Wong-ShiYau2020MainProof-20260929T220402.log` |
| `Wong.UnconditionalMainProof` | 108.11 | `b517048ef5a3cb883270b35a99fe4f15754709f8467b95fbb17d052bfdd38c75` | `development/Wong-UnconditionalMainProof-20260929T220718.log` |
| `Wong` | 108.787 | `10bb1e069ed401caead1d0acbfe3ab4dcb76d1dcb31d6475075867265108afae` | `development/Wong-20260929T221028.log` |
| `ProofRouteAudit` | 120.15 | `85747eb92d8fa60b92d88b3e3d0c0ecf60fa0a3d6d29c09e9ce3627e70733396` | `development/ProofRouteAudit-20260929T221247.log` |

三个 2020 主目标及两个新增综合结论的 `#print axioms` 输出均仅含 `propext`、`Classical.choice`、`Quot.sound`，没有 `sorryAx`。编译仍有 `letI` 风格提示，不称为零警告。

## 实际证明项的路线检查

开发阶段 `ProofRouteAudit` 成功通过全部准确类型包装和真实证明项遍历：

- 2020 仿射函数元定理到达真实五分支分类和各分支仿射性证明，不到达原 `main_theorem` 或新增无条件定理。
- 无条件 Wong 定理到达 2020 仿射函数元定理、原条件主定理与 `JacobiVisible.second_identity`。
- 条件 Wong 主定理及可见斜率定理到达新 Jacobi 桥，不到达被替换的 `head00/head11/head01`、`δ_δ_Y`、`singleAxisElimination`。

对应可达本地声明数分别为 2534、2738、2126、717、135（最后一个是独立 Jacobi 桥根）。这里包含自动生成的辅助声明，不等同于源码中的 theorem/lemma 数量。审计遍历 `Wong` 命名空间中的实际证明体；第三方库由另外的公理审计及固定依赖版本管理。

最终验收会在完整重建的本地产物上再次执行这些检查，开发成功不是最终成功的替代。

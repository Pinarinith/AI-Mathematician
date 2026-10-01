# 2020 扩展验收机制只读审计

审计时间：2026-09-29T13:51:57.523475+00:00。审计对象是本工程当前源码和正在运行的 `verify.py --clean`；**本报告不是最终 Lean 通过证书**。审计期间没有运行 Lean、修改数学源码、修改正在运行的验收脚本或中断构建。仅按协调授权在旧 README 顶部添加了“工作中”的历史说明。

## 结论

未发现需要停止或重启本次干净重编的材料性验收缺陷。最终通过仍须等 `verification/acceptance.json` 由当前运行写为 `passed: true`，并检查其绑定的完整构建、公理及证明路线报告。审计时该文件为 `passed: false`；进度明确是 `full_source_rebuild`、165 模块、无历史基线复用。

当前数学源码目录恰有165个模块，全部处于 `Wong` 入口依赖闭包中，没有未导入的遗留数学源码。静态复算得到1659个唯一的源码 `theorem`/`lemma` 名称，均位于 `Wong` 命名空间内。这是后续公理审计的预期清单数，尚不是该轮公理审计已经通过的宣告。

## 精确命题与无循环路线

`ProofRouteAudit.lean:43` 与 `:49` 直接书写2020正文 Thm3.10、Thm3.7 的完整类型；没有 `QuadraticFree`、Wong 仿射、额外 η 条件或预先适配坐标的输入假设。`:61` 直接书写最终无 quadratic-free 前提的 Wong 恒定类型。引言 Wong-only 结果通过冻结的 `ShiYau2020WongQuadraticClaim` 检查。

`frozen-statements.json` 所列的三个文件实际哈希均与对应 Research 原文件一致：`MainStatement.lean`、`ShiYau2020ModelReduction.lean`、`ShiYau2020IntroductionStatement.lean`。其中 `MainStatement` 的哈希另外硬编码于验收器。命题语义所引用的 `FunctionElementsAffine` 定义明确量化所有实际乘法函数元，并要求次数≤1；`polynomialSmooth` 是真实多项式求值。这两个定义所在文件也与 Research 原文件完全一致：

- `Wong/FunctionQuadraticRankConstraints.lean`：`6fbc7e3ccc516f7a0ec8843360bf873e430d1d264d4f755f8349d4b905e164b3`
- `Wong/PolynomialSmooth.lean`：`f42507202c76f4b225fc6263fb8bf3a3197546931bcb10e43e10578a98d6156a`

路线审计读取实际声明值，包括 theorem/opaque 的值，递归收集其使用的 `Wong` 常量，具有缺失即失败的检查：

- 2020 Mitter 根必须经过五分支结论和实际二次函数分类；不得到达 `main_theorem` 或 `unconditional_main_theorem`。
- 无条件综合根必须同时到达2020 Mitter、原 conditional 主定理和新 `Wong.JacobiVisible.second_identity`。
- 原 conditional 主定理及 visible 根必须到达新的 Jacobi 证明，并不得到达旧 `head00/head11/head01/δ_δ_Y` 或 `Wong.Visible.singleAxisElimination`。

该程序只遍历 `Wong` 前缀，符合本快照全部源码数学定理的命名范围；外部库公理由独立的传递公理审计约束。以上是程序将执行的检查，实际可达性结果仍以本轮 Lean 输出为准。

## 零占位与公理清单

`verify.py:244–266` 在编译／复用每个闭包模块前去除注释，拒绝 `sorry/admit/axiom/unsafe/native_decide/implemented_by/skipKernelTC`。本次独立静态扫描还检查了声明生成类元编程入口；165个数学模块中未见 `run_cmd/run_tac/elab/macro/initialize/addDecl` 等相关入口，未见非注释字符串、私有或 opaque 声明。这使当前简单词法扫描不存在由这些语法造成的实际遗漏。当前 `ProofRouteAudit.lean` 本身也无占位或绕过 token。

`verify.py:284–317` 生成全部1659个源码 theorem/lemma 的 `#print axioms`，要求每个名字都有输出，Lean 进程成功，且传递公理只属于 `propext/Classical.choice/Quot.sound`。该机制严格覆盖源码 theorem/lemma，**不应表述为枚举了 Lean 环境中每个自动生成常量、每个 def 或 instance**；这些定义被数学证明使用时，其依赖会进入公理的传递检查。所有数学源码仍须通过前述源码扫描和正常内核编译。

源码扫描是本工程的实用检查，不是对任意恶意 Lean 元程序的通用安全验证器；本次没有发现这类程序。无需为不存在的元程序重启构建或扩大信任机制。

## 构建隔离、快照与依赖绑定

- `verify.py:34` 在任何检查之前原子写入失败／进行中验收状态。因此本轮异常退出不能遗留旧的总体验收成功。
- `--clean` 删除 `.lake/verified/lib/lean` 及进度；本轮进度记录 `historical_baseline: null`。最终 `LEAN_PATH` 只有 `.lake/verified` 和 vendor 编译库，**不含** `.lake/development` 或旧 `.lake/build`。
- `dev-compile.py` 只写开发目录，并明确记录 `development_only_not_certified`。它没有完整验收器的审计门槛，这与其开发用途一致；其产物不可能通过当前最终导入路径被直接复用。
- 两个编译入口使用同一 `development/compiler.lock` 的 `fcntl` 独占锁。最终编译、公理审计、路线审计均使用该锁，避免开发与最终 Lean 进程同时占用资源。
- 每个最终模块记录源码 SHA、`.olean` SHA、直接本地依赖 `.olean` SHA、编译退出码和日志。每次编译后检查源文件未改变，全部模块完成后再次检查源码和工件；审计后还会再次检查整个快照。
- 公理报告和路线报告绑定 `fresh-build.json` 的哈希；总体验收绑定三个报告、验收脚本、源码清单、环境指纹和冻结命题映射。路线程序退出成功且出现最终成功标志才可通过。
- 精确 Lean release/commit、编译器文件哈希、mathlib 干净提交、依赖 manifest、固定归档及解压源码均被检查；环境变更不允许盲目复用本地工件。验收尾部再次检查环境。

审计时正在运行的 `verify.py` 文件哈希与启动时的验收记录一致；已完成模块的依赖哈希和磁盘工件哈希也一致。完整构建仍在进行，不能把此抽查误作全部165模块已完成。

**信任边界：**此次“全干净重编”指全部本地 Wong 源码。mathlib 及其他第三方库使用与已核对源码版本对应的既有编译缓存，未从源码重编或穷尽哈希其所有二进制；脚本和验收字段已明确披露该范围。Lean 编译器及其内核仍属于通常形式验证的可信基础。

## 交付前的材料修正

不需要修改当前运行脚本。最终交付文档须统一更新历史占位内容：

1. README 旧正文还说2020扩展不在认证范围，并描述旧四模块增量集成；本轮验收完成后应替换为实际165模块干净构建的范围及结果。审计中已添加工作中提示，尚未改写其历史正文。
2. `verification/retained-closure.json` 仍是旧123模块清单，并把现在已导入的2020模块列为 excluded。该文件不是验收脚本的输入，不影响当前结果；交付前应按当前闭包重生成，或移入明确的历史目录。
3. 在本轮最终通过之前，继承的 `fresh-build.json/axioms.json/proof-routes.json` 等旧成功材料均不能代表2020扩展通过。当前总体验收为 false；脚本将在到达相应阶段时覆盖这些文件。交付时以最新总体验收绑定的哈希链为准。

## 审计对象指纹

后续开发入口更新：`dev-compile.py` 现在也允许模块名 `ProofRouteAudit` 和 `AxiomAudit`，用于在开发缓存上预跑审计程序；仍只写 `.lake/development`，结果仍标记为 `development_only_not_certified`。这是调试入口扩展，不是数学证明模块或最终验收范围扩大。`verify.py` 与本报告审查的数学源码未因此改变。下表的开发脚本哈希已同步更新。

| 文件 | SHA256 |
|---|---|
| `verify.py` | `f19ed807c54c3dfcfe8fcfa080e20ca22842b0311da62e9e0cf620c9da5d78ca` |
| `ProofRouteAudit.lean` | `85747eb92d8fa60b92d88b3e3d0c0ecf60fa0a3d6d29c09e9ce3627e70733396` |
| `frozen-statements.json` | `0ef93dfb0bb0c5b9a391799e3c0defa04aaea91ed97bfdaa4c56ab726b023cb0` |
| `dev-compile.py` | `ed90db9191446dc33dc86c8ce3556f886b7424ff42444d28bbf7d04f607ecd60` |


## 最终验收通过补记（2026-09-29 17:31:25.982162 UTC）

以上正文保留首次只读审查时的进行中状态；此补记记录其后实际完成的验收，不回写历史审计结果。当前 `verification/acceptance.json` 为 `passed: true`。`fresh-build.json` 记录165个本地模块全部于本轮从源码重编，模式 `full_source_rebuild`、无历史基线、无跳过模块；开始时间为2026-09-29 13:27:40.154251 UTC，编译完成时间为17:28:12.274966 UTC。之后1659个源码 theorem/lemma 的公理审计、精确命题类型和实际证明路线审计全部通过，最终验收时间为17:31:25.982162 UTC。无 `sorryAx` 或额外数学公理，允许基础公理仍仅为 `propext`、`Classical.choice`、`Quot.sound`。

补记时已只读核对总证书中三个报告哈希与现有文件一致：

| 报告 | SHA256 |
|---|---|
| `verification/fresh-build.json` | `554577a219e6ff3b06059963ec35bf602c2dc83560b997317dbc52349470188c` |
| `verification/axioms.json` | `53bc0190199ebc6b224bf18d781f0b413ebe23bd731d6d28ee3e39854418c62c` |
| `verification/proof-routes.json` | `a061f112fcc844c06ca941a2badcd497b3dce860e91e22370d8b8b49860c9efd` |

验收脚本及证明路线审计程序仍使用上表所列的已审查指纹；补记未修改脚本、Lean源码或证书。README已依据实际通过记录更新；旧 Jacobi 材料保留其历史属性。第三方 Mathlib 编译缓存的信任边界保持不变，并未据本地全量重编宣称第三方库也已重建。

# 2020 原文主命题、实际模型与 Jacobi 连接：独立源级审计

> 最终状态补充：2026-09-29 17:31:25 UTC，本轮165个本地模块全量重编、1659个定理/引理公理审计及准确类型/证明路线审计全部通过。以下记录保留撰写时的审查范围；其中“最终待验收”描述属于历史状态。当前正式结果见 `final_acceptance.md` 与 `../verification/acceptance.json`。

审计人：独立子任务 `alternative_symbols`。审计日期：2026-09-29。

**结论：在下列版本绑定的源码与原文范围内，未发现主命题范围被削弱、额外假设 `QuadraticFree` 被隐藏、实际过滤模型被替换、五分支漏项，或由旧 `main_theorem` 循环证明 2020 主定理的问题。** 2020 的 Theorem 3.10 先独立证明，Theorem 3.7 随后由二次函数不存在推出；这一顺序在逻辑上成立。无二次自由假设的 Wong 常数结论再与已换用 Jacobi 收尾的旧主定理组合。

这是**数学对应和源码依赖审查**，不是本轮干净编译的内核证书。本审计任务未运行 Lean，也未修改任何 `.lean` 文件。最终交付仍须以冻结源码的全量 clean build、实际证明依赖图与公理审计为准。此前分支开发编译成功不替代这些最终检验。

## 1. 原文与 Lean 命题逐项对应

直接阅读所提供 `ShiYau2020.layout.txt` 的原文，未把旧 review 的判断当作依据。原文引用位置按该文件的文本行号计算；PDF 双栏导致提取的相邻行有跨栏内容，阅读时已按栏位语义区分。

| 原文 | Lean 对应 | 核对结果 |
|---|---|---|
| Theorem 1.1，原文 148–152 行：三维、rank 2、有限维估计代数；存在二次多项式时 Wong 矩阵常数 | `ShiYau2020IntroductionStatement.lean:11`，`ShiYau2020WongQuadraticClaim`；`ShiYau2020MainProof.lean:124` | 精确对应引言的 Wong-only 结论。 |
| Theorem 3.7，605–607 行：二次多项式存在时，Wong 常数且全部观测函数 affine | `ShiYau2020ModelReduction.lean:26`，`ShiYau2020QuadraticClaim`；`ShiYau2020MainProof.lean:114` | 比 Theorem 1.1 多出的观测函数结论被明确保留。 |
| Theorem 1.2，154–158 行；Theorem 3.10，709–712 行：全部函数元素 affine | `ShiYau2020ModelReduction.lean:18`，`ShiYau2020MitterClaim`；`ShiYau2020MainProof.lean:108` | 有限维、rank 2 是仅有的外部数学前提；无 `QuadraticFree`。 |
| 原文 Lemma 3.1，约 285–302 行：A、B1、B2、C1、C2 分类 | `QuadraticFunctionCaseSplit.lean:363,439` | 五种实际函数元素情况由真实二次见证推出；全函数空间限制保留。 |
| 用户当前所需的无外加二次自由假设 Wong 常数结论 | `UnconditionalMainProof.lean:10,15,22` | 用 2020 仿射函数定理先证明 `QuadraticFree`，再调用 Jacobi 版本的原主定理；这比引言 Theorem 1.1 的条件式结论更强，报告时应区分。 |

`FunctionElementsAffine`（`FunctionQuadraticRankConstraints.lean:104`）量化所有全局光滑 `u`，要求实际乘法算子 `multiplication u` 属于估计代数后，`u` 才由总次数 ≤1 的真实多项式表示。它没有只量化预先知道为多项式的函数。原文引言写 “degree one”，正文 3.10 明确写 affine；Lean 的 ≤1 包括常数和零，是正确读法。rank 2 时常数乘法算子本来就在代数中，不能把原文读成每个函数都恰为一次。

Lean 允许观测数 `m = 0`，而原文通常取正整数；`PublishedAffineInput` 的空观测分支用秩为零与 rank 2 矛盾消去，因此这里是无害的定义域扩展，没有借空观测假设规避非空情形。

## 2. 实际微分算子模型没有被替换

`MainStatement.lean` 中状态空间为 `Fin 3 → ℝ`，`Smooth` 是全局 `C∞` 函数子类型；坐标偏导是实际 Fréchet 导数，乘法算子是真实逐点乘法，算子属于 `Module.End ℝ Smooth`。估计代数是由真实 `L0` 与全部真实观测乘法算子生成的最小实 Lie 子代数。秩定义为其中齐次线性函数系数空间的维数，对应原文 rank。

定义为

- `D_i = ∂_i − M_{f_i}`；
- `η = Σ_i(∂_i f_i + f_i²) + Σ_j h_j²`；
- `L0 = 1/2 Σ_i D_i² − 1/2 M_η`。

`RootAnalyticBridges.lean:828–858` 的 `D_square_expanded` 和 `L0_eq_publishedExpandedL0` 进一步核实了原文展开式：`1/2 Δ − Σ_i f_i ∂_i − Σ_i ∂_i f_i − 1/2 Σ_j h_j²`。漂移散度和观测平方的符号、系数均一致。原文的正交扩散矩阵提供单位协方差，正是这里的单位扩散生成元。

这是一份估计代数的解析、微分算子命题认证；并未声称认证原文的随机微分方程解存在、过滤密度构造、数值模拟或滤波算法性能。这是形式化范围的说明，不是主估计代数命题的附加限制。

坐标规范化也发生在真实模型内：

- `CoordinateGenerators.lean:96,128,136` 证明变换后的实际漂移、观测满足 `eta_coordinateDrift`、`coordinateConjugation_L0` 和 `coordinateAlgebra_estimationAlgebra`，并证明有限维性、rank 的保持。
- `ShiYau2020ModelReduction.lean:94` 用 rank 单独给出的 `exists_coordinateAlgebra_adapted` 建立坐标适配，再将全部函数仿射性双向运输。这里没有调用那个需要 `hq` 的旧 `estimationAlgebra_adapted_coordinates`。
- `RootAnalyticBridges.lean:40–195` 的平移同样以真实 pullback 的漂移、观测定义，证明 η、L0 和生成代数相容。平移时保持齐次线性秩用到 `1 ∈ E`，后者从当前 rank 2 模型得到。
- 二次函数配方时隐藏方向系数的非零性明确提供给平移量的分母。正交旋转保持可观测坐标平面；B2 的两个坐标版本通过真实旋转转换。

因此分类结果中的 `f', h'` 并非任选的另一个抽象代数，而是经上述已证明变换得到的真实估计模型。分类反证只需产生同样有限维、rank 2 且带真实非仿射见证的规范模型，再证明该规范模型所有函数均仿射；不需要额外假定任意模型之间可反向传递矛盾。

## 3. 五分支穷尽及退化情形

下表使用原文的坐标 `x1,x2,x3`；Lean 下标为 `0,1,2`。

| 分支 | 源码实际保留的条件 | 组装中的关闭方法 |
|---|---|---|
| A | `x3² ∈ E`，且**每一个函数元素**的可见坐标二阶导均为零 | `functionElementsAffine_of_pure_hidden_square_whole_hessian_free` |
| B2 | `x1²+x3² ∈ E` | 平面径向 Wong 刚性与混合 Wong 为零，再由 B2 η/函数空间结论关闭 |
| B1 | `x1²+x2²+x3² ∈ E` | 全径向函数空间结论 |
| C1 | **全部函数元素**与 `x3` 无关，且 `x1²+x2² ∈ E` | C1 Wong 常数、可见 η Hessian 常数，再由隐藏无关闭包关闭 |
| C2 | 实际 `x1² ∈ E`，且全部函数元素形如 `c+a x1+b x2+q x1²` | C2 Wong 常数和可见 η Hessian 常数，再由隐藏无关闭包关闭 |

关键穷尽步骤如下。

1. `actual_quadratic_function_cases` 从一个真实、总次数恰为二的见证出发，按所有函数的隐藏二阶导是否为零分情形。
2. 全部隐藏二阶导为零时，`FunctionHiddenIndependence` 利用实际函数元素的仿射偏导、rank 混合约束和隐藏线性尾部排除，证明**所有**函数的隐藏一阶导为零。这里没有把“对一个见证成立”提升成未经证明的全空间条件。
3. 在此隐藏无关分支，提取非零可见二次型。若所有可见二次型都奇异，对一个非零型对角化并规范为 `x1²`；同时保留全空间奇异性。另一个型 `q` 和 `q+x1²` 的行列式同时为零迫使共同轴条件，得到完整 C2 形式。若存在非奇异型，用二次闭包产生可见径向型，得到 C1。
4. 若某个隐藏二阶导非零，则先配方平移，再对角化可见二次型。实际梯度内积闭包提供二次型的平方、立方等滤子，抽取含隐藏方向的等特征值投影，得到纯隐藏平方、两个 B2 版本或 B1。
5. **纯隐藏平方没有立即当成 A。** `actual_hidden_square_refined_model` 再检查全函数空间可见 Hessian 是否为零；若非零，从另一个实际函数提取可见二次型，与已存在的隐藏平方合并，转入 B2 或 B1。
6. 每个最终规范分支都由 `classification_model_case_not_functionElementsAffine` 保留真实非仿射见证；由非零二阶偏导直接与仿射性矛盾。

已核对的退化点包括：可见二次型秩 1、秩 2，重复特征值、相反符号、零可见特征值，隐藏特征值与可见特征值相等或不同，以及 B2 的两种坐标位置。`classification_visible_radial_mem` 在 `a,b ≠ 0` 时使用 `((a+b)q − q²_filter)/(ab)`，不要求 `a−b ≠ 0` 或 `a+b ≠ 0`；隐藏投影滤子的分母只在对应分支证明非零后使用。全空间奇异性在旋转后通过逆 pullback 运输，未仅保留选中二次型的奇异性。

## 4. 2020 无外加 hq；反向证明顺序不存在循环

`ShiYau2020MitterClaim` 的签名没有 `QuadraticFree`。适配版本仅多出从 rank 得到的两个坐标函数成员条件。`shiYau2020_adapted_mitter_theorem` 的逻辑是：

1. 使用已经内部证明的 Ocone 次数界，将“全部函数仿射”等价化为“没有实际二次函数”。
2. 对任意假定存在的实际二次函数，以算子外延性确认其确为对应多项式乘法算子。
3. 用完整五分支分类得到真实规范模型。
4. `classification_model_functionElementsAffine` 在该模型的每一个分支证明全部函数仿射。
5. 与该分支带有的真实非仿射见证矛盾。

这里进入反证后局部出现的 `hq` 是“该多项式总次数为 2”，而不是作为外部假设输入的 `QuadraticFree`；两者不能因变量同名而混淆。`shi_yau_affine_structure` 在分类组装中也是从有限维、rank 与两个坐标成员得到，不另加二次自由性。

随后 `shiYau2020_quadratic_theorem` 使用独立得到的 3.10。若给定二次多项式 `q` 的实际乘法算子在代数中，3.10 使其等于某个次数 ≤1 的 `p`。真实多项式求值的单射性给出 `p=q`，所以 `2 ≤ 1`，矛盾。由此推出 3.7 的 Wong 常数与观测仿射结论，再投影获得引言 1.1。

因此这是**先排除二次分支，再证明以二次分支为前提的条件定理**。逻辑成立，但不是对原文 3.7→3.10 的逐行证明次序复现，也不应描述成在某个可实现的二次模型中显式计算出观测仿射系数。该二次模型已被 3.10 证明不存在。

### `hqE` 编译修复的独立复核（本次刷新）

`ShiYau2020MainProof.lean:96–99` 唯一修改是把原先的直接等式运输 `hAeq ▸ hA` 展开成显式的三步证明：

```lean
have hqE : q ∈ polynomialFunctionElements f h := by
  change multiplication (polynomialSmooth q) ∈ estimationAlgebra f h
  rw [← hAeq]
  exact hA
```

`change` 仅展开 `polynomialFunctionElements` 的定义；`rw [← hAeq]` 使用前面已由算子外延性证明的 `A = multiplication (polynomialSmooth q)`；最后目标正是已给出的 `hA : A ∈ estimationAlgebra f h`。没有新增数学假设、定义、定理声明或推理来源。

本审计将当前文件的这一块精确替换回旧的一行写法，重建出的整文件 SHA256 为 `edd3390f12db1974e23dc336a66927d2778031f7efe1595491f8e5c63a3dbd0e`，与上一版报告保存的源哈希完全相同。因此可以字节级确认除这一处 proof-body 类型转换修复外，本文件没有其他变化，前述数学对应结论保持。

已只读检查主任务生成的 `development/Wong-ShiYau2020MainProof-20260929T220402.json` 与同名 `.log`：退出码 0，124.811 秒，`source_changed = false`，记录源码与当前文件 SHA 一致；三个公开目标的 `#print axioms` 仅列 `[propext, Classical.choice, Quot.sound]`。日志另含两处 `letI` 风格提示，不影响结论。JSON 状态明确为 `development_only_not_certified`。本次复核未运行 Lean；这份开发编译证据仍不替代待完成的全量 clean build、最终公理和 proof-route 验收。

## 5. 与新 Jacobi 主定理的连接

`UnconditionalMainProof.lean:15` 明确先取 `shiYau2020_mitter_theorem`，再以 `quadraticFree_iff_functionElementsAffine` 导出旧定理所需的 `hq`，最后调用 `main_theorem`。所以最终签名删除 `hq` 有真实证明支持，并非改写声明后把前提丢掉。

当前源级路线为：

`unconditional_main_theorem`
→ `shiYau2020_mitter_theorem` 提供 `hq`
→ `MainProof.main_theorem`
→ `SectorIHiddenBridge.mainClaim_of_remaining_visible_affine_slopes`
→ `VisibleHeads.visible_slopes_zero`
→ `VisibleElimination` 的规范斜率消去
→ `VisibleHeadContradiction.normalized_slope_zero_of_constant_heads`
→ `JacobiVisible.normalized_slope_zero_by_jacobi`。

最后一层旧名字只作同签名包装，实际调用新 Jacobi 桥。新桥从常主符号给出的双重交换子常数性出发，使用 `JacobiVisible.first_identity`、`second_identity` 与实际光滑算子关系完成斜率矛盾。它不需要旧的 η 三、四阶导数系数消去。旧主定理余下的隐藏/混合 Wong 斜率消去仍是该完整 Wong 定理的一部分，不能把全部证明描述为只剩一个 Jacobi 恒等式。

本节为直接源码路线核对；全体真实 proof-term 的可达性、旧 `head11/head01` 展开公式与 `singleAxisElimination` 不可达，仍留给最终 proof-route 证书。模块被 import 与某个定理在实际证明中被调用是不同概念。

## 6. 独立 import 闭包扫描

本报告生成时重新读取所有本地 `Wong/*.lean`，去除嵌套块注释、行注释及字符串，再解析 `import` 并递归追踪本地模块。没有运行编译器。对每个闭包还扫描了去注释源码中的 `sorry`、`axiom`、`native_decide` 标记，以及完整单词 `main_theorem`。

- `Wong.ShiYau2020MainProof`：157 个本地模块；包含 `Wong.MainProof`：false；包含 `Wong.JacobiVisible`：true。
  - `main_theorem` 源码出现模块：无。
  - 禁用标记命中模块：无。
  - 闭包 SHA256：`cd1c63a7efe70ab8c08dbd3124b81900d016bda6b8fe0fb828b94c374de366cb`。
- `Wong.UnconditionalMainProof`：159 个本地模块；包含 `Wong.MainProof`：true；包含 `Wong.JacobiVisible`：true。
  - `main_theorem` 源码出现模块：Wong.MainProof, Wong.UnconditionalMainProof。
  - 禁用标记命中模块：无。
  - 闭包 SHA256：`da635ca721093e833d4b4f583bd101cde2d6d0596be1828fdf0d860fec28f40d`。
- `Wong.MainProof`：117 个本地模块；包含 `Wong.MainProof`：true；包含 `Wong.JacobiVisible`：true。
  - `main_theorem` 源码出现模块：Wong.MainProof。
  - 禁用标记命中模块：无。
  - 闭包 SHA256：`5d0f65f5f1fe452ba511afd09cded478cc7c6b2712b078c194d051d7246727a8`。

2020 主证明闭包不包含旧主定理模块，也没有旧 `main_theorem` 可供调用。因此源码组装层面未出现以旧完整 Wong 主定理作为 2020 结果输入的循环。该闭包包含 `JacobiVisible` 是共享基础设施的结果；不能据此宣称 2020 的每一个真实 proof term 使用 Jacobi，也不能宣称两套证明的全部辅助模块完全互不相交。

闭包散列的规范格式为：模块名排序后逐行 `模块名 空格 源SHA256`，以换行连接且末尾不加换行，再取 SHA256。此散列绑定本次检查的所有本地依赖源码，不包含 mathlib 工件、编译器或外部包；这些仍由最终构建清单绑定。

## 7. 版本绑定与结论边界

以下哈希于报告生成时直接从当前共享工程读取。若后续编译修复改动了任何文件，相应源码数学改动须复核；本报告不会自动覆盖未来版本。

快照时间（UTC）：`2026-09-29T14:07:40.537620+00:00`。

原文 layout SHA256：`474d1457d14dd25f6c1fc18f5444a9adc41a79a61101a4960b8177842078bfe9`。

| 源文件 | SHA256 |
|---|---|
| `Wong/MainStatement.lean` | `e9f51310ade6a4539e43c3074a1b35ed35e34bd85946761d53c93183d842a5cc` |
| `Wong/FunctionQuadraticRankConstraints.lean` | `6fbc7e3ccc516f7a0ec8843360bf873e430d1d264d4f755f8349d4b905e164b3` |
| `Wong/ShiYau2020ModelReduction.lean` | `acf77811491108648c478a18eede8f9b8845bc6d2be5f8e97069d7f57d6cf375` |
| `Wong/ShiYau2020IntroductionStatement.lean` | `e5f3523cc7333fae63835f4248acfdee34459f14fc5621bfee96cc139f2e6b4b` |
| `Wong/ShiYau2020MainProof.lean` | `e57306d3ad18964e67cce958caa16e4c104f259ec9f7aa7da377acc5cc2e2d5b` |
| `Wong/QuadraticFunctionClassification.lean` | `4c93242d863264dff1085988b4841dd9cac999fe8c390641e7204ac2ab84b503` |
| `Wong/QuadraticFunctionCaseSplit.lean` | `33115c6044c6f9db3267d3fa780c145a35e77fd0c078c7a38663a60222cfd544` |
| `Wong/FunctionHiddenIndependence.lean` | `355594fb3a239d3e6e4aec7e84e967e4d9101b0a9ffd9230447690808010efee` |
| `Wong/CoordinateGenerators.lean` | `eaa80e5931e7f04ee587c81516bc0818e31492b21289c114c358a801a940885c` |
| `Wong/RootAnalyticBridges.lean` | `51baa8cd572798029ca11b25d6dafb35d8ef97458305b3163cbfb88562e02be1` |
| `Wong/PublishedAffineInput.lean` | `9b40a9778b8a91b4a6d811068605a3b79da9eb1c746bd257920abff02e997311` |
| `Wong/HiddenRadialEtaConclusion.lean` | `31feb1049d68aa0d2151137a4a8d17222540273bece451b2a06f2ddf0d20dd28` |
| `Wong/PlaneRadialWongRigidity.lean` | `6f335adcf06be91d57becc95f1f9355da099afdfc07462bcc3dae7e5dc3c44e6` |
| `Wong/B2EtaAnalysis.lean` | `0ce52d1b4480e103fe1bd76176aace556003f870e8408086017d35c7e2c55491` |
| `Wong/C1EtaConclusion.lean` | `8fb463d597015566cdd4d4cd85bf7a3e803d1a4ce46929f4764cd4efbbd0cdca` |
| `Wong/ConstantWongHiddenIndependentEtaClosure.lean` | `dfb059bcaf3756a96d3e64db28441f31e93ca431ca7831a1b596cabfcd13b841` |
| `Wong/C2Complete.lean` | `7dcee98997f96e87ef3f579c98b0959e5a880196fe0fd1fbd11dacb584d9ceff` |
| `Wong/UnconditionalMainProof.lean` | `b517048ef5a3cb883270b35a99fe4f15754709f8467b95fbb17d052bfdd38c75` |
| `Wong/MainProof.lean` | `16d41c9049aacf320337631fc602d5b5bfdad4cef30e45e6bc4278b8eb7e1359` |
| `Wong/SectorIHiddenBridge.lean` | `3c4112f040da4e87920011081286e857e6506484f4c290e7af1e46a67e0f8603` |
| `Wong/VisibleElimination.lean` | `f574a7fd48837b2691b60f7390bf61cdd1c03cb309232ba4c2c18b35ea5b23db` |
| `Wong/VisibleHeadContradiction.lean` | `42e454a2956cae1fc022f29071b9cd83846956f69874c8b010c859e6dbc743aa` |
| `Wong/JacobiVisible.lean` | `3bbf9708b02028bd99a7cf54fa4b9c8668a9119b6702ce5968c26d39ad915ed1` |

最终判断：原文主数学命题、实际单位扩散估计代数模型、全函数空间量化、五分支穷尽及与 Jacobi 主定理的逻辑组装在本快照中相符。本次未发现需要退回修改的数学对应问题。**本报告不单独证明所有辅助引理已由 Lean 接受；最终 clean build 和实际依赖/公理证书是独立且必要的验收层。**

# 开发缓存组件的历史证据核对

> 最终状态补充：2026-09-29 17:31:25 UTC，本轮165个本地模块全量重编、1659个定理/引理公理审计及准确类型/证明路线审计全部通过。以下记录保留撰写时的审查范围；其中“最终待验收”描述属于历史状态。当前正式结果见 `final_acceptance.md` 与 `../verification/acceptance.json`。

本报告仅为 2026-09-29 的历史证据预检，不是本次 Lean 验收证书。检查期间未调用编译器、未修改 Lean 源文件；独立的完整源码重编仍是最终认证依据。

## 范围与结果

覆盖 `development/provisional-cache.json` 中列出的 **32/32 个预置旧工件候选**。对照当前工程源码、Research 原源码及旧 `.olean`、旧 accepted/verified JSON、被记录哈希定位的编译日志。

- **29 个**找到明确记录为成功退出（exit 0）、与当前源码 SHA-256 一致、日志 SHA-256 一致、且日志公理打印正常的历史证据。
- 其中 **27 个**还具有匹配的旧 `.olean` SHA-256 记录；另 **2 个**只有源码、退出码、日志和公理证据，缺少旧工件哈希绑定。
- **3 个**缺少能把最终源码哈希与成功退出码绑定的历史记录，标为“未完全确认”；其末轮日志本身没有编译错误或 `sorryAx`，并打印了正常基础公理。
- **32 个**当前源码均与 Research 原目录对应源码一致；**32 个**预置开发工件均与 Research 对应旧工件一致。没有发现已选成功记录的源码或工件哈希不一致。
- 检查的 **32 份末轮/已绑定日志**均没有编译错误、`sorryAx` 或非基础公理打印。允许集合为 `propext`、`Classical.choice`、`Quot.sound`。

“exit 0”指旧 JSON 记录的明确字段，不是本轮重新执行编译器所得。没有重构旧编译时的完整依赖环境；这些证据不证明本轮 clean build 成功，也不能替代当前完整证明项闭包审计。

## 需要保留的疑点

1. `ConstantWongRadialEta`：`constant_wong_radial_eta.log` 有 2 项基础公理打印且无错误；未找到绑定当前最终源码哈希与 exit 0 的 accepted JSON。
2. `QuadraticFunctionCaseSplit`：`quadratic-function-case-split.log` 有 6 项基础公理打印且无错误；未找到对应最终源码的明确 exit 0 记录。
3. `VisibleFilteringHessianCompatibility`：`visible_filtering_hessian_compatibility.log` 有 1 项基础公理打印且无错误；未找到对应最终源码的明确 exit 0 记录。

以上是证据完整性不足，不应据此宣布模块编译失败。旧 `fresh-sources.json` 包含这三个模块的更早源码哈希，与当前版本不同；它不是最终编译 accepted 记录，不能据此绑定最终工件。早期 attempt 日志中的失败也不能替代末轮判断。

较弱的工件来源证据另有 `GlobalRiccatiQuadraticForm` 和 `GlobalRiccatiTestBound`：`state.json` 的对应组件记录有当前源码哈希、exit 0、匹配的日志哈希和正常公理打印，但未记录 `.olean` 哈希。本轮仅确认复制的预置工件与 Research 当前旧工件一致。

## 逐模块覆盖

下面的 JSON 与日志文件名均相对于旧审计目录：

`/Users/rinithpina/Documents/Research/Mitter_Conjecture/audit_unconditional_2026-09-18`

状态 A：源码、exit 0、日志、公理和旧工件哈希记录均相符；B：源码、exit 0、日志、公理相符，旧工件哈希未记录；C：只有正常末轮日志，最终源码/exit 0 绑定未确认。

| 模块 | 状态 | 历史记录 | 匹配/核对日志 |
|---|---|---|---|
| C1Constancy | A | C1Constancy-accepted.json | c1_constancy.log |
| C2Complete | A | c2-complete-accepted.json | c2-complete.log |
| ConstantWongClosureActual | A | constant-wong-closure-actual-verified-b.json | constant-wong-closure-actual.log |
| ConstantWongFiniteClosure | A | constant-wong-finite-closure-verified-b.json | constant-wong-finite-closure.log |
| ConstantWongHiddenScalarRigidity | A | ConstantWongHiddenScalarRigidity-accepted.json | constant_wong_hidden_scalar_rigidity.log |
| ConstantWongQuadraticEtaClosure | A | ConstantWongQuadraticEtaClosure-accepted.json | constant_wong_quadratic_eta_closure.log |
| ConstantWongRadialEta | C | 未找到最终成功绑定记录 | constant_wong_radial_eta.log |
| CoordinateCubicRiccati | A | coordinate-cubic-riccati-accepted.json | coordinate-cubic-riccati.log |
| CubicEtaRiccatiRigidity | A | CubicEtaRiccatiRigidity-accepted.json | cubic_eta_riccati_rigidity.log |
| DiagonalQuadraticCurvature | A | diagonal_quadratic_curvature.json | diagonal_quadratic_curvature.log |
| FunctionHiddenIndependence | A | function_hidden_independence.json | function_hidden_independence.log |
| GlobalRiccatiMomentAnalysis | A | GlobalRiccatiMomentAnalysis-accepted.json | global_riccati_moment_analysis.log |
| GlobalRiccatiOddRayMoment | A | GlobalRiccatiOddRayMoment-accepted.json | global_riccati_odd_ray_moment.log |
| GlobalRiccatiQuadraticForm | B | state.json/completed_internal_components/9 | global_riccati_quadratic_form.log |
| GlobalRiccatiTestBound | B | state.json/completed_internal_components/11 | global_riccati_test_bound.log |
| HiddenIndependentSectors | A | hidden-independent-sectors-accepted.json | hidden-independent-sectors.log |
| HiddenQuadraticShearRigidity | A | hidden_quadratic_shear_rigidity.json | hidden_quadratic_shear_rigidity.log |
| HiddenSquareWongRigidity | A | hidden_square_wong_rigidity.json | hidden_square_wong_rigidity.log |
| MomentumAxisLadder | A | momentum_axis_ladder.json | momentum_axis_ladder.log |
| PolynomialRayLift | A | polynomial-ray-lift-verified-b.json | polynomial-ray-lift.log |
| PureHiddenQuadraticEta | A | PureHiddenQuadraticEta-accepted.json | pure_hidden_quadratic_eta.log |
| QuadraticFunctionCaseSplit | C | 未找到最终成功绑定记录 | quadratic-function-case-split.log |
| QuadraticFunctionClassification | A | quadratic-function-classification-verified-b.json | quadratic-function-classification.log |
| QuadraticHiddenLinearTail | A | quadratic_hidden_linear_tail.json | quadratic_hidden_linear_tail.log |
| QuadraticObservationMoment | A | quadratic-observation-moment-verified-b.json | quadratic-observation-moment.log |
| ShiYau2020ModelReduction | A | shi-yau-2020-model-reduction-accepted.json | shi_yau_2020_model_reduction.log |
| SmoothCoordinateEuler | A | SmoothCoordinateEuler-accepted.json | smooth_coordinate_euler.log |
| SmoothEulerResolventRegularity | A | SmoothEulerResolventRegularity-accepted.json | smooth_euler_resolvent_regularity.log |
| SmoothPolynomialRegularity | A | SmoothPolynomialRegularity-accepted.json | smooth_polynomial_regularity.log |
| VisibleCubicEtaObservationRigidity | A | VisibleCubicEtaObservationRigidity-accepted.json | visible_cubic_eta_observation_rigidity.log |
| VisibleFilteringHessianCompatibility | C | 未找到最终成功绑定记录 | visible_filtering_hessian_compatibility.log |
| VisibleWongQuadraticAnalysis | A | VisibleWongQuadraticAnalysis-accepted.json | visible_wong_quadratic_analysis.log |

## 本轮读取的源码和日志指纹

以下指纹用于固定这次只读核对的对象；A/B 的源码和日志值同时匹配旧记录，C 的值仅为本轮读取结果。

| 模块 | 当前源码 SHA-256 | 历史日志 SHA-256 |
|---|---|---|
| C1Constancy | `91d5810b54f83609418eb794b80fd1638d7f40581c73e0c582ae0503ca51f876` | `84b6a515b8e3a916d30dff66373ae2bc1d5b45e4db83ae22c83970fc552b77b4` |
| C2Complete | `7dcee98997f96e87ef3f579c98b0959e5a880196fe0fd1fbd11dacb584d9ceff` | `60c4a21d09ef600d46c4c642e3fbfd758bb6b6827632771dc3aa9d4de956c535` |
| ConstantWongClosureActual | `2743354251caf6e95aadafa6455cf964fc4fed4b6f65a2a5ab7c64549a8ac124` | `7eda5582024ec72af109e68d2388999e5d2091e6a1dfebe80b89be91a07a543c` |
| ConstantWongFiniteClosure | `31d6deb360eec7acc7d2035dbad860fb88ea4d7db5d06a061812ad512ebcf121` | `f6a39df22e6342d432681ceed14993340eb4a5a46e0ebe08d8a9b43d522422c5` |
| ConstantWongHiddenScalarRigidity | `0ef13508fcb1833b9abbf4a31ff9fc83149d21be6d922c8ac04912e1d097d666` | `0c84ab56c2e5371481acb9aa8343561a24ba54d340705ca6295fa724081fd679` |
| ConstantWongQuadraticEtaClosure | `354118c691c376794e63832f217522fb98c92df10d17e3931f4053af69b3ab0f` | `c27f38238ac785ae3489766b0fefd19ac0a6adf0c2a99ab78a2dfb8c2d92165c` |
| ConstantWongRadialEta | `8f925b93edb8bdf3871fe28faa5ff13871f0f2bc31884fc7990bfa7b36576b3a` | `f580bd112f5b09f7ea3f1a0a90b048f546f356de21a28ad5859567aaaf5dc4ab` |
| CoordinateCubicRiccati | `6b5149ae8a8218791524b6d4a25bb56de20293a892b26069d679ceb58db3690a` | `8e99dbf0a22ad6f08cc9f3c351267d0ecb2dc356b03fb5f8319572677bc91a2d` |
| CubicEtaRiccatiRigidity | `c7945d2ebf110ad58df4622580e2154747e204c3ccf15ecf9fe44036ee395420` | `f5c7ffa6f2cad09e801b8ebe947f62c15d3bad665ce800ae9eeeb4b8d4cd6caf` |
| DiagonalQuadraticCurvature | `277718ab6b8778852f0663197ac93c51057d320dcb07723c367616742d3178b2` | `b6972cb1d367f6b4da03d834f12d9d2d92c0f66f4f32bfcd32e5107af7f9f8e7` |
| FunctionHiddenIndependence | `355594fb3a239d3e6e4aec7e84e967e4d9101b0a9ffd9230447690808010efee` | `b0cf7f796d48ce0d5b4eddcaee79d67a368b860f606cce71ced6d8170b7af086` |
| GlobalRiccatiMomentAnalysis | `f8c750279be10c5d9e3a0efc0082cc0b8151035038a31acbec0682bc68e44c72` | `118207c3a78ee181d6e75e9065c52d5804a207039a90371f1fe179337beddf78` |
| GlobalRiccatiOddRayMoment | `d59e3578ed0cfee24f6da48e9bb877c827e9cced60c4d0f17096cddfeb542b74` | `63a53f089740366e358053d992f51d670347c6b5cbc18730be8dcb267db740db` |
| GlobalRiccatiQuadraticForm | `579836253fbbc3d6179dbae9f2b79555930e9b5ed82650114d0c353776140729` | `88b90e6a7342d0e679ec5e96785a3fee470583b0725a126f1f9bb9a464925364` |
| GlobalRiccatiTestBound | `cf68e83371ceeb28d305787331076ac2abf0619b484e17384792cabc8be9f42f` | `98e0759c233c888e9b43b8924498f6c1367a568eb9366866587e53a48407ee49` |
| HiddenIndependentSectors | `b3b19554b4937e16ed479b5b8024b244bbe5364914c3539ab49d7f18db5d53ae` | `fce40eb89d26b2c0a5e1ef7417b2f3fc76d9053eb44a846abf41fbe20bb3d8fd` |
| HiddenQuadraticShearRigidity | `ac3af56727c59f87ce86fe2f0567de5b52344076b119d2b7df71b2c1e7eeaa43` | `884674a02a074eb8b3e6b5982c707503b1f8aef0cbe835ed33d3004f5f5d3bef` |
| HiddenSquareWongRigidity | `e70498d6d2e3599e24a7eee245d86826929330cc5ed717c6482c2abdf1bd5f8d` | `f0b371959944fa8be26130c0debe858a15cc0f84db4eef927de7a09a0d5f1eb5` |
| MomentumAxisLadder | `b33ae9ae72ba545f36effe662f2f933144fe9f76aaaf500a86d26e1fd5a3f5da` | `31861bc48fe64aa500db90a7aca12031032d6cef17053c79874f8f2954272a48` |
| PolynomialRayLift | `068f67f8830eb11505564595fa9ba06bc8751838a73e6b160ec999bbb5c6e389` | `8fb3daeeae007b2b571be8a3a6b2ee6e331b8b09aa86516de0df9cdf7308eb4d` |
| PureHiddenQuadraticEta | `9c90c219207339959604a4e388ac83b7fc250f6183828026f091eaec7b3d4e3e` | `2b15124f8cc25475e6dd473c6399eeba6911a7ab5bf830734e6f2e304ec1c8ef` |
| QuadraticFunctionCaseSplit | `33115c6044c6f9db3267d3fa780c145a35e77fd0c078c7a38663a60222cfd544` | `104a5d718828a7d5fd4620aadffff9d5a009f896bf60ada90501c57f295666ef` |
| QuadraticFunctionClassification | `4c93242d863264dff1085988b4841dd9cac999fe8c390641e7204ac2ab84b503` | `3034a9563d899d0b2ab6554fc53c7b4e92c4a9981166fba4ea240961f133fafc` |
| QuadraticHiddenLinearTail | `0e7d33d3d71665b54abdb93cc47ed6e83fa2d7a1c145663d3515556f953cd69a` | `9c3e94cf1b315d05d709488cac66d8e5e429e193aa986de5565c5ef34683b4da` |
| QuadraticObservationMoment | `ff7f2aff9a44f77d8dd555aa87ab7ef7208b0925a267eeeddc6edc2c30d2a9d1` | `66343e1bd2b571dbba55cfcb8c0e42f09ab9972c784fac8714288ac9b2b239b1` |
| ShiYau2020ModelReduction | `acf77811491108648c478a18eede8f9b8845bc6d2be5f8e97069d7f57d6cf375` | `e7d2d2bdfe2afafaf3b359aecb1438b2e1bb4b575c1a65f5e1e99328292ecda9` |
| SmoothCoordinateEuler | `d9ff4007e156b8b471a4e33e7c8cbe383de7d70da4d4c6d6a2a6d288218c398c` | `c84e48a51c277e862d4da5c015a932abf16f512a90b077323d8d3a6b74492a18` |
| SmoothEulerResolventRegularity | `950aa21162ff796708e7f11dce1449a525864d5c5f4cad608ed8e2a46c2c21a4` | `2ec4c1f4d2347f9bbc25a5e8cd71b7ada6fd570ed176ad47d417e2e279377472` |
| SmoothPolynomialRegularity | `d7ccdbafed4cb8c1eda6328442a0642f43506d67f3dc9f11cb27361d82f363d2` | `307404df70fff18d5b001389827b1e3563e904f621a52a993e69360a8467c8d3` |
| VisibleCubicEtaObservationRigidity | `522619e615792b65a7cb5924257289464fcfc46c56bc252d295c7045da2b51ba` | `d13638d8bba96bd2cc698de7715e7e76ade4df5cf55534b1e09771ed273e4d98` |
| VisibleFilteringHessianCompatibility | `c72d60b54741ed093d72eeed97a334aab7a6be339ed475f4d836cdc374ca41e9` | `c45fb6fc9053dda4e8e60d4ca0a3f92f1f0997979fdcb4afac871bbc7c93aed0` |
| VisibleWongQuadraticAnalysis | `862c4095af4899abfe99ac1c7c07f3e67c8565df564f6320d0370b246eb9ee3a` | `675221d5674d2b4abbaa5a30ae99579abf9cb67425e90fc14b7547366c5cab4b` |

本轮没有新增未解决的“旧末轮编译失败”发现。需要等待完整重编消除的重点是上述 C 类三模块，以及全部组件在当前依赖闭包下的可复现性。

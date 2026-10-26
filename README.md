# AmpCalc
Mathematica package for calculation of scattering amplitude

Files:

AmpCalc.m: The package

pin.m: Feynman rules for pion-nucleon scattering

BaryonChPT_PiNSdelta.nb: main file for calcualting one-loop amplitude of pion-nucleon scattering with explicit delta resonances

******************************
    De-Liang Yao
    School of Physics & Electronics
    Hunan University
    Changsha 410082
    P. R. China
******************************

# xAmplCalc 使用说明书

作者：De-Liang Yao（湖南大学）

英文版：[xAmplCalc.en.md](xAmplCalc.en.md)

`Package/xAmplCalc.m` 是一套单圈振幅化简程序。它自己定义洛伦兹结构、狄拉克代数、同位旋代数和传播子，把含圈动量 `k` 的振幅化成 Passarino–Veltman 函数或 Davydychev 标量积分 `I0`，再做张量约化、紫外极点分离和四维极限。

文件头注明：2014-01-07 起，`xTensorReduce` 消元后质量的顺序是 `m22, m12`。

本文件不是带 `BeginPackage` 的形式包。读入后，符号都落在当前上下文，通常是 `` Global` ``。

## 加载

在项目根目录下：

```wolfram
<< Package`xAmplCalc`;
```

或

```wolfram
Get["Package/xAmplCalc.m"];
```

圈动量固定为符号 `k`，时空维数固定为符号 `D`。度规缩并 `metrictensor[μ, μ]` 的值就是 `D`。

## 计算顺序

一条单圈振幅通常按下面的顺序处理。`xLoopAmplitude` 已经把前半段串在一起。

1. `xExpandPair`、`xDotSimplify`：展开动量、标量积和 `Dot`。
2. `xDiracContract`、`xDiracSimplify`、`xSU2Simplify`：收缩指标，化简狄拉克结构和 SU(2)。
3. `xClassifyFAD`：把不含 `k` 的分母拆成 `propagator`，合并其余 `FeynAmplDenominator`。
4. `xReduceK`、`xReduceK2`、`xFADReduce`：用分母线性关系消去分子里的 `k`。
5. `xUniqueFAD`、`xShiftK`：把其中一个传播子平移成 `k^2 - m^2`。
6. `xLoopAmplitude`：对 `k` 做张量分解，得到 `LFA0` … `LFE0` 或其张量形式。
7. `xTensorReduce` 或 `xTensorReduce2`：张量积分约到标量积分。
8. `xSetDto4` 或 `xLFUVdivergent`：取四维有限部分，或抽出紫外极点。

`xShiftK`、`xReduceK`、`xReduceK2` 要求表达式里只剩一个 `FeynAmplDenominator`。多个分母没有先合并时，它们会 `Print` 错误并 `Abort`。先调用 `xClassifyFAD`。

## 记号

TraditionalForm 下的排版由文件开头的 `MakeBoxes` 定义。

| 符号 | 含义 |
| --- | --- |
| `momentum[p, μ]` | 动量 `p` 的洛伦兹分量 |
| `scalarproduct[p, q]` | `p·q`。`Orderless`。`scalarproduct[p, p]` 自动变成 `scalarproduct[p]` |
| `metrictensor[μ, ν]` | 度规。`Orderless`。两个指标相同则为 `D` |
| `Levicivitaε[μ, ν, ρ, σ]` | 四维 Levi-Civita 符号 |
| `Diracgamma[μ]` | `γ^μ` |
| `Diracgamma5` | `γ^5` |
| `Diracsigma[μ, ν]` | `σ^{μν}` |
| `Diracslash[p]` | `p̸` |
| `Diracspinor[s, p, m]` | `s = 1` 为 `u`，`s = -1` 为 `v` |
| `DiracspinorU[p, m]`、`DiracspinorV[p, m]` | 上面两种旋量的简写 |
| `Dotgamma[...]` | 狄拉克空间的乘积 |
| `Dotisospin[...]` | 同位旋空间的乘积 |
| `Paulitau[i]` | 泡利矩阵 `τ_i`。`paulitau` 是未带指标的 `τ` |
| `KroneckerDelta2[i, j]` | 同位旋指标的 `δ_{ij}`，`Orderless` |
| `Levicivita2[i, j, k]` | 三维 `ε_{ijk}` |
| `FeynAmplDenominator[{q, m}, ...]` | `1/(q^2 - m^2)` 的乘积。`m` 是质量，不是质量平方 |
| `propagator[p, m]` | 不含圈动量的传播子，由 `xClassifyFAD` 拆出 |
| `k` | 圈动量 |
| `D` | 时空维数 |

Passarino–Veltman 函数。标量函数的参数是外动量平方和质量平方，质量平方的顺序与传播子顺序一致。

| 符号 | 参数 |
| --- | --- |
| `LFA0[m0^2]` | 一点 |
| `LFB0[p10, m0^2, m1^2]` | 两点。`p10 = (p1 - p0)^2` |
| `LFC0[p21, p32, p31, m0^2, m1^2, m2^2]` | 三点 |
| `LFD0[p21, p32, p43, p41, p31, p42, m0^2, …, m3^2]` | 四点 |
| `LFE0[...]` | 五点，只在张量分解里出现 |
| `LFA0i`、`LFB0i`、`LFC0i`、`LFD0i`、`LFE0i` | 对应的张量积分。洛伦兹指标放在最前面，后面是标量函数的那一组参数 |
| `DLFB0` | `B0` 对动量平方的导数，供 LoopTools 的 `DB0` 使用 |

另外三个记号：

- `UVepsR`：紫外极点的符号，TraditionalForm 显示为 `R`。
- `$mu`：维数正规化标度，TraditionalForm 显示为 `μ_d`。
- `$HIGHORDER`：`xIRRegularPart` 里高于所取阶的余项。

Davydychev 积分写成

```wolfram
I0[d, {{q1, m1, ν1}, {q2, m2, ν2}, ...}]
```

`d` 是维数，`qi` 是该传播子的动量，`mi` 是质量，`νi` 是幂次。幂次为 0 的传播子会被删掉。两个动量、质量都相同的传播子会把幂次相加。`I0[d, {}]` 在 `d === D` 或 `d =!= D` 时都定义为 `0`。`LFA0[0] = 0`。

## 文件读写

### xWrite、xRead

```wolfram
xWrite[exp, "filename", "directory"]
xRead["filename", "directory"]
```

目录可省略，默认是 `NotebookDirectory[]`。因此在 `.wl` 脚本里必须自己传入目录。`xWrite` 用 `Write`，`xRead` 用 `Read`，一次读写一个表达式。

### xSave、xLoad

```wolfram
xSave["name1", "name2", ..., "directory"]
xLoad[name1, name2, ..., "directory"]
```

`xSave` 把 `Symbol[name]` 的当前值 `Put` 到 `directory <> name <> ".dat"`。名字必须和符号名完全一致，不是字符串模式。目录字符串要自己带上结尾的 `/`。

`xLoad` 用 `Get` 读回，并赋给同名符号。它没有 `HoldAll`。符号如果已经有值，多参数形式会先求值，随后无法按符号名读文件。重新载入前先 `Clear` 这些符号。

`xSave::usage` 写的是“按字符串模式保存值和定义”。实现只保存精确符号名对应的值。

### xPrintTime

`HoldAll`。返回被计时表达式的结果。

```wolfram
xPrintTime[expr]
xPrintTime[expr, "message"]
```

单参数形式总是计时，并打印 `Time used: ... seconds`。双参数形式只有在 `$xPrintTimeMessageOn` 为 `True` 时才打印 `message` 并计时。这个开关的默认值是 `False`。`xLoopAmplitude` 内部用的是双参数形式，所以默认不打印各步耗时。

### xDrop

```wolfram
xDrop[list, n]
xDrop[list, {n1, n2, ...}]
```

按位置删除。整数形式删除第 `n` 个元素。列表形式先排序，再从后往前删，避免位置错位。空列表时原样返回。

## 代数化简

### xConstantQ

```wolfram
xConstantQ[c]
```

数值，或带 `Constant` 属性的符号，返回 `True`。`xExpandPair` 用它把常数提出因子。

### xExpandPair

```wolfram
xExpandPair[exp]
```

把 `momentum`、`scalarproduct`、`Diracslash` 里的动量和先 `Expand`，再按加法和常数因子分配。`xDotSimplify` 和 `xDiracSimplify` 会调用它。

### xDotSimplify

```wolfram
xDotSimplify[exp, SeparateDiracIsospin -> True]
```

先 `xExpandPair`。把 `Dot` 按加法拆开，把不含 `Diracslash`、`Diracgamma`、`Diracgamma5`、`Diracspinor`、`Paulitau` 的因子提出。

`SeparateDiracIsospin -> True`（默认）时，把乘积拆成 `Dotgamma` 和 `Dotisospin`。设为 `False` 时只整理 `Dot`，不拆空间。

### xDiracSimplify

```wolfram
xDiracSimplify[exp,
  ShiftGamma5 -> True,
  SimplifyGamma -> True,
  SimplifyMomentum -> True,
  SimplifySpinor -> True]
```

先做 `xDotSimplify`，再依次处理 `Dotgamma`：

- `ShiftGamma5`：把 `γ^5` 移到右边，并用 `(γ^5)^2 = 1`。
- `SimplifyGamma`：合并重复的 `γ^μ`，用度规缩并。
- `SimplifyMomentum`：合并重复的 `Diracslash`，得到标量积或 `momentum`。
- `SimplifySpinor`：对紧挨旋量的 `Diracslash` 使用狄拉克方程。`u(p,m)` 给出 `+m`，`v(p,m)` 给出 `-m`。

四个选项都可以单独关掉。

### xDiracContract、xDiracContract0

```wolfram
xDiracContract[exp]
xDiracContract0[exp]
```

收缩 `metrictensor`、`momentum`、`Diracgamma`、`Levicivitaε` 和 `Dotgamma` 的重复指标。缩并后恢复原来的函数头。

`xDiracContract` 直接 `Expand` 后替换。`xDiracContract0` 先用 `xSeparate` 把系数和张量结构分开，注释里写明这一步较慢。日常用 `xDiracContract`。

### xOrderDotGamma

```wolfram
xOrderDotGamma[exp]
```

按指标或动量的 `OrderedQ` 顺序重排 `Dotgamma` 里相邻的 `Diracgamma`、`Diracslash`，并产生相应的度规或标量积。

### xSU2Simplify

```wolfram
xSU2Simplify[exp]
```

先 `xDotSimplify` 再 `Expand`。对和式逐项处理。使用的关系是：

- `τ_0` 是单位矩阵，缩并后变成 `1`。
- `τ_i τ_j = δ_{ij} + I ε_{ijk} τ_k`。
- `δ_{ii} = 3`，`ε_{ijk}^2 = 6`。
- 两个 `ε` 按共同指标收缩成 `δ` 的乘积。

结果再经 `xUniqueLevicivita2`，把 `Levicivita2` 的指标排成标准顺序并乘上符号。

### xUniqueLevicivita2

```wolfram
xUniqueLevicivita2[exp]
```

表达式不含 `Levicivita2` 时原样返回。

### xSeparate

```wolfram
xSeparate[exp, head1, head2, ...]
{coefficients, structures} = xSeparate[exp, heads]
```

按给定函数头把表达式拆成系数和结构，用 `CoefficientArrays` 实现。返回 `{系数列表, 结构列表}`，两者点乘回到原式。输入是列表时，对每个元素分别拆分。

找不到相应结构时返回 `{{exp}, {1}}`。`Variables` 只在和、积、有理幂里找变量，包在其他函数头里的结构不会被拆出来。

## 传播子与圈动量

`FeynAmplDenominator[{q, m}]` 表示分母 `q^2 - m^2`。`xUniqueFAD`、`xShiftK` 用 `CoefficientList[..., k]` 读取 `q` 中 `k` 的系数，因此 `q` 应当是 `k` 的线性式。

### xClassifyFAD

```wolfram
xClassifyFAD[exp]
```

不含 `k` 的分母改写成 `propagator`。其余分母合并成一个 `FeynAmplDenominator`，并按第一分量排序。`xReduceK` 和 `xReduceK2` 会自己先调用它。

### xFADReduce

```wolfram
xFADReduce[exp]
```

对每个 `FeynAmplDenominator` 调用内部的 `xReduceFAD`。若后面的含 `k` 分母能线性表出第一个含 `k` 分母，就用部分分式降低分母个数，并递归。不含 `FeynAmplDenominator` 时原样返回。

### xUniqueFAD

```wolfram
xUniqueFAD[amp, sort -> True]
```

把每个传播子动量归一成 `k + 外动量`，质量除以 `|k 的系数|`。`sort -> True` 时按质量排序。输入是列表或和式时，逐项处理。

选项名是小写的 `sort`，不是 `Sort`。

### xShiftK

```wolfram
xShiftK[exp]
```

把第一个传播子平移，使其中的圈动量变成 `k`。分子里的 `k` 做同样平移，并调用 `xExpandPair` 和 `xDotSimplify`。

已经是 `k` 时不做平移。存在多于一个 `FeynAmplDenominator` 时中止。和式与列表会逐项处理。

### xReduceK

```wolfram
xReduceK[exp]
```

分子里若有 `scalarproduct[k, 外动量]`，且它能由各分母线性表出，就用分母的差把它消掉，从而降低分子里 `k` 的幂。不能表出时保留这项，继续处理其余因子。

不含 `FeynAmplDenominator` 或不含 `scalarproduct[k, _]` 时原样返回。多个 `FeynAmplDenominator` 时中止。

### xReduceK2

```wolfram
xReduceK2[exp]
```

专门消去分子中的 `scalarproduct[k]`。用第一个传播子的分母 `k^2 - m^2` 把它换成质量项和外动量标量积。多个 `FeynAmplDenominator` 时中止。

### xExtractK

```wolfram
xExtractK[amp]
```

把 `scalarproduct[k]`、`scalarproduct[k, p]` 和 `Diracslash[k]` 写成带新洛伦兹指标的 `momentum[k, μ]`、`Diracgamma[μ]`。`xLoopAmplitude` 用它收集张量积分的指标。指标由 `Unique` 生成。

## 圈积分

### xLoopAmplitude

```wolfram
xLoopAmplitude[amp, IntegrateMethod -> $PaVe]
```

没有 `FeynAmplDenominator` 时打印提示并 `Abort`。否则依次做：

`xDotSimplify` → `xDiracContract` → `xDiracSimplify` → `xSU2Simplify` → `xDiracContract` → `xReduceK` → `xReduceK2` → `xFADReduce` → `xClassifyFAD` → `xUniqueFAD` → `xShiftK`

然后把含 `k` 的部分按张量积分分解。`IntegrateMethod` 只接受两个值：

- `$PaVe`：调用 `xTensorDecompositonPaVe`，得到 `LFA0` … `LFE0`。
- `$Davy`：调用 `xTensorDecompositonDavy`，得到 `I0`。

其他值会 `Abort`。

不含传播子的项会被减掉，不加回结果。最后再做一次 `xDiracContract`。

### xLoopAmplitude0

```wolfram
xLoopAmplitude0[amp, IntegrateMethod -> $PaVe]
```

与 `xLoopAmplitude` 相同，但跳过 `xReduceK`、`xReduceK2` 和 `xFADReduce`。传播子仍会分类、归一和平移。

### xTensorDecompositonPaVe

函数名是 `Decompositon`，少一个 `i`。

```wolfram
xTensorDecompositonPaVe[indices, fad]
```

`indices` 是洛伦兹指标列表，`fad` 是已经平移好的 `FeynAmplDenominator`。不含传播子时返回 `0`。

第一个传播子在 `k -> 0` 后动量必须是 `0`，否则打印 `eRRorrrrrrrrrr`。这就是先做 `xShiftK` 的原因。

一点到五点分别写成 `LFA0i`/`LFA0`、`LFB0i`/`LFB0`、`LFC0i`/`LFC0`、`LFD0i`/`LFD0`、`LFE0i`/`LFE0`。秩为 0 时用标量函数。多于五点时用 `xPaVe`。

`Options` 里有 `$ABCDE -> False`，函数体却是 `If[True, ...]`，因此这个选项不改变分支。

分解公式对应 Denner、Dittmaier，Nucl. Phys. B 734 (2006) 62 的张量分解。

### xTensorDecompositonDavy

```wolfram
xTensorDecompositonDavy[indices, fad]
```

同样先 `xUniqueFAD`。标量情形返回 `I0[D, {{q, m, ν}, ...}]`。张量情形按 Davydychev 的对称张量分解，提升维数并升高传播子幂次，前面带 `Gamma` 因子。参考文献是 Phys. Lett. B 263 (1991) 107。

## 张量约化与四维极限

### xTensorReduce、xTensorReduce2

```wolfram
xTensorReduce[amp, $SetDto4 -> False]
xTensorReduce2[amp, $SetDto4 -> True]
```

把 `LFA0i`、`LFB0i`、`LFC0i`、`LFD0i` 约成标量积分。运动学矩阵的行列式为 0 时打印 `Error, Determinate zero`。

`xTensorReduce` 一次约到底，默认不取四维。`$SetDto4 -> True` 时对约化结果再调用 `xSetDto4`。

`xTensorReduce2` 每次只降一个指标，然后递归，直到没有张量积分。默认会取四维。没有张量积分时直接返回输入。

内部函数是 `xReduceTensor` 和 `xReduceTensorOnce`，一般不必直接调用。

### xSetDto4、xSetDto40

```wolfram
xSetDto4[amp]
```

`Listable`。把 `D` 换成 `4`，并保留 Denner 表里的紫外极点与 `(D-4)` 相乘后的有限贡献。实现范围是：

- `A`：标量和偶数个指标全为 0 的张量。
- `B`：到秩 5。
- `C`：到秩 7。
- `D`：到秩 7 中已经写出规则的那一部分。

没有匹配的圈函数时，只做 `D -> 4`。圈函数的有限部分仍保持符号，不会被数值化。

`xSetDto40` 是同一套规则的旧版本，`C` 只到秩 5，`D` 只到秩 1，并且不是 `Listable`。新计算用 `xSetDto4`。

### xLFUVdivergent

```wolfram
xLFUVdivergent[amp]
```

先 `xTensorReduce`。然后取紫外极点：`LFA0[m^2]` 贡献 `-m^2 UVepsR`，`LFB0` 贡献 `-UVepsR`，`LFC0` 和 `LFD0` 贡献 `0`。返回值是 `UVepsR` 乘以它的系数。

### xPVReductionRules、xPVReductionRules0

```wolfram
xPVReductionRules[loopAmpList]
xPVReductionRules0[loopAmpList]
```

输入是列表。抽出其中的张量积分，返回 `张量积分 -> 约化结果` 的规则。前者的右侧再经 `xCollect`。

### xDLFB0

```wolfram
xDLFB0[p, m1^2, m2^2]
```

`B0` 对第一个参数的导数，只在四维使用。参数是动量平方和两个质量平方。结果用 `LFA0` 和 `LFB0` 表示。

## LoopTools

这些函数依赖已经安装好的 LoopTools MathLink 可执行文件，`Install["LoopTools"]` 要能找到它。

### xLTForm

```wolfram
xLTForm[amp]
```

把 `LFA0`、`LFB0`、`LFC0`、`LFD0`、`DLFB0` 分别换成 `LoopTools`A0`、`B0`、`C0`、`D0`、`DB0`。张量函数换成 `B0i`、`C0i`、`D0i`，指标名由一串整数拼成，例如 `bb00`、`cc001`。

`LFA0i` 不走 `A0i`，而是先 `xTensorReduce` 再换成 `A0`。这里的系数因子是 `1`，`1/(16 π^2)` 放在 `xLoopTools` 里。

### xLTadapted

```wolfram
xLTadapted[amp]
```

LoopTools 直接算的张量秩有上限：`LFB0i` 的指标个数小于 4，`LFC0i` 小于 5，`LFD0i` 小于 6。超过上限的积分先做一次 `xReduceTensorOnce` 并 `xSetDto4`，重复到全部可算。

### xLoopTools

```wolfram
xLoopTools[amp, $subtractFactor -> -1, $renormalizationScale -> 0.939]
```

安装 LoopTools，设置 `SetDelta` 和 `SetMudim`。`SetMudim` 用的是 `$renormalizationScale^2`。然后返回

```wolfram
xLTForm[amp] / (16 Pi^2)
```

返回之前会 `Uninstall` 掉刚才打开的链接。函数给出的是 LoopTools 表达式，不是已经求出的数值。要数值计算，需要在链接仍然有效时对这个表达式求值。

`$subtractFactor` 传给 `SetDelta`。注释写明 LoopTools 里 `delta = 0` 对应 `MSbar`。

### xLFForm

```wolfram
xLFForm[exp]
```

把 LoopTools 风格的 `A0i`、`B0i`、`C0i`、`D0i` 换回本文件的 `LF*`。秩最高按 7 生成指标名。`A0i[aa0, ...]` 先变成 `A0`。`B0`、`C0`、`D0` 分别变回 `LFB0`、`LFC0`、`LFD0`。

`B0[x___]` 在代码里被替换成 `LFB0i[x]`，不是 `LFB0`。从 LoopTools 转回标量 `B0` 时要检查这一项。

## 标量积分的标准化

### xUniquePaVe

```wolfram
xUniquePaVe[amp]
```

在 `LFB0`、`LFC0`、`LFD0` 的动量置换里选一个代表元。排序键是 `{质量参数, 动量参数}`，质量优先。

### xOrderPaVe

```wolfram
xOrderPaVe[amp]
```

做同样的置换，但用 `Sort` 比较整个参数表，不区分质量和动量的优先级。

### ScalarBase、InScalarBase

```wolfram
ScalarBase[fad, OutPutForm -> ABCD]
InScalarBase[exp]
```

`ScalarBase` 接受 `FeynAmplDenominator` 或 `I0`。`OutPutForm -> ABCD` 时写成 `LFA0` … `LFD0`，并做 `xUniquePaVe`。传播子个数不是 1 到 4 时返回字符串 `"error in ScalarBase"`。其他 `OutPutForm` 值返回原来的 `fad`。

`InScalarBase` 把表达式中所有 `I0` 和 `FeynAmplDenominator` 都送进 `ScalarBase`。

`SF[exp]` 列出表达式里的 `LFA0`、`LFB0`、`LFC0`、`LFD0`。

## Davydychev 约化

### xToDavy

```wolfram
xToDavy[LF, {p1, p2, p3}]
```

`LF` 必须是 `LFA0`、`LFB0`、`LFC0` 或 `LFD0`。返回 `{I0[...], 标量积规则}`。`p1`、`p2`、`p3` 是用来重建外动量的辅助动量。质量参数先开方再写进 `I0`，因此它们应当是质量平方。

### xSchwingerPara

```wolfram
xSchwingerPara[I0[...]]
xSchwingerPara[I0[...], {{Z1, Z2, Z3, Z4}, {ζ1, ζ2, ζ3, ζ4}}]
```

对最多四个传播子做 Schwinger 参数化，积掉圈动量和整体参数 `λ`。返回 `{系数, myβ -> 指数里的二次型}`。默认参数名是 `$$Z1` … 和 `$$ζ1` …。

### ScalarReduce、ReduceScalar、RNSN

```wolfram
ScalarReduce[exp]
ScalarReduce[exp, mandelstamRules]
ReduceScalar[I0[...], mandelstamRules]
RNSN[I0[...]]
```

`ScalarReduce` 找出所有 `I0`，逐个调用 `ReduceScalar`。不给规则时使用 `{}`。

`ReduceScalar` 用 Davydychev 的递推，把积分降到 `ScalarBase` 能识别的标量积分。特殊情形直接给出 `LFB0[0,0,0]`。行列式组合无法处理时会 `Print` 并 `Abort`。

`RNSN` 返回 `{RN, SN, Det[RN], Det[SN]}`，分别是约化里的运动学矩阵和加边矩阵。

### xScalarReduce、xC0D0Reduce

```wolfram
xScalarReduce[I0[...], mandelstamRules]
xC0D0Reduce[C0orD0]
```

`xScalarReduce` 先把规则里的外动量换成本地动量 `pp1`、`pp2`、`pp3`。外动量平方为 0，或两条外动量之差的平方为 0 时，合并对应传播子，再调用 `ScalarReduce`。传播子合并会改变质量时，改走 `xLoopAmplitude`。

它会把全局变量 `$xPrintTimeMessageOn` 设为 `False`。

`xC0D0Reduce` 用 `xToDavy` 转成 `I0`，再调用 `xScalarReduce`，最后 `xCollect`。

### der

对标量积分的参数求导，再约回标量积分。

```wolfram
der[{n1}, LFA0[m^2]]
der[{n1, n2, n3}, LFB0[p, m1^2, m2^2]]
der[{n1, ..., n6}, LFC0[...]]
der[{n1, ..., n10}, LFD0[...]]
```

整数是对各个参数的求导阶数，顺序与函数参数顺序相同。`B0` 的三个整数依次对应动量平方和两个质量平方。一点函数的 `n1` 会乘上 `n1!`。`der[{n1}, LFA0[0]]` 定义为 `0`。

约化后使用下面的规则，不自动调用 `xSetDto4`：

```wolfram
ruleintD = {
  LFB0[0, 0, 0] -> LFB0[0, 0, 0],
  LFB0[0, m12, m22] /; m12 =!= m22 :> (LFA0[m12] - LFA0[m22]) / (m12 - m22),
  LFB0[0, m12, m22] /; m12 === m22 :> ((-2 + D) LFA0[m12]) / (2 m12),
  LFB0[m22, 0, m22] :> ((-2 + D) LFA0[m22]) / (2 (-3 + D) m22)
};
```

`ruleint` 是同一批积分在四维下的替换，把 `LFB0[0,0,0]` 设为 `0`。需要四维结果时，在 `der` 的输出上再使用 `ruleint` 和 `xSetDto4`。

## 费曼参数

### xMomentumIntegration

```wolfram
xMomentumIntegration[{x1, x2, ...}, fad]
```

对 `n` 个传播子引入 `n - 1` 个费曼参数。参数个数不够时中止。返回积掉圈动量之后的被积表达式，参数积分还没有做。结果里保留 `D`、`Gamma` 和参数的雅可比。

每个参数会被加上 `Constant` 属性。

`xMomentumIntegration0` 是旧的参数排序，新计算用 `xMomentumIntegration`。

### xIRRegularPart

```wolfram
xIRRegularPart[parameters, fad, power][mn, mandelstamRules, expandRules, α]
```

`power` 的模式是整数。它在费曼参数积分之后，把 `D = 4 - 2 eps` 展开到 `eps` 的一次，并按 `α` 的幂收集。紫外对数放在 `UVepsR` 里，标度是 `$mu`。高于 `power` 的项乘以 `$HIGHORDER`。

核子质量 `mn` 用来写

```wolfram
kappa[1] = mn^2 (UVR + Log[mn^2 / $mu^2])
kappa[2] = -(1 + UVR + Log[mn^2 / $mu^2])
```

以及更高点的 `kappa[3]`、`kappa[4]`。参数积分假设 `D > 50`。

## 运动学与收集

### Mandelstam 规则

```wolfram
xMandelstamRules2OffShell[{p1, p2, p3, p4}]
xMandelstamRules2OnShell[{m1, m2, m3, m4}]
```

`p1`、`p2` 入射，`p3`、`p4` 出射。`s`、`t`、`u` 是全局符号。

离壳版本保留 `scalarproduct[pi, pi]`。在壳版本把它们换成 `mi^2`，并且规则里的动量固定写成全局符号 `p1`、`p2`、`p3`、`p4`，不使用函数参数里的动量名。质量参数只决定 `m1^2` … `m4^2`。

### xCollect 到 xCollect4、xLFsimplify

四个 `xCollect` 都是 `Listable`。

| 函数 | 收集对象 | 系数处理 |
| --- | --- | --- |
| `xCollect` | `LFA0` … `LFD0`、对应的张量函数、`DLFB0` | `Simplify` |
| `xCollect2` | 同上 | `Together` |
| `xCollect3` | 再加 `Derivative[...][...][...]` | `Together` |
| `xCollect4` | 与 `xCollect3` 相同 | `Simplify` |

```wolfram
xLFsimplify[exp]
```

只对上面这些圈函数及其导数调用 `Simplify`，不重新收集整式。

## 使用时注意

- 圈动量必须叫 `k`。换名字之前，传播子化简和张量分解都不会把它当成圈动量。
- `xSave` 的目录要带结尾分隔符，例如 `Results/Temp/`。
- `xLoad` 前先 `Clear` 同名符号。
- `xWrite`、`xRead` 在脚本里不要依赖 `NotebookDirectory[]`。
- `xShiftK`、`xReduceK`、`xReduceK2` 遇到多个 `FeynAmplDenominator` 会中止。报错文字里的函数名有时写成 `xClassify` 或 `xClassfyFAD`，实际应调用 `xClassifyFAD`。
- `xLoopAmplitude` 丢掉不含传播子的项。树图贡献要单独保留。
- `xTensorDecompositonPaVe` 要求平移之后第一个传播子的动量为 `0`。
- `xSetDto4` 只替换它写了规则的紫外部分。其余圈函数保持符号。
- `xLoopTools` 在返回前卸载 MathLink。它设置的 `delta` 和 `μ^2` 只对那一次安装有效。
- `xScalarReduce` 会把 `$xPrintTimeMessageOn` 改成 `False`。
- `xUniqueFAD` 的选项是 `sort`，`xLoopAmplitude` 的选项是 `IntegrateMethod`，`xTensorReduce` 的选项是 `$SetDto4`。三个名字都要按这个大小写写。

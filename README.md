# ProgramAnalyser
The program analyser for the experiments in "Static Analysis of Posterior Inference in Bayesian Probabilistic Programming".

## Prerequisite

Install .NET, the version used in this project is .NET 6.

> https://dotnet.microsoft.com/en-us/download/dotnet/6.0

## Usage 

### Use `dotnet`
Assume `pwd` is in the directory with the `.fsproj` file, that is, 
use `cd dotnet runAnalyser` first when the terminal is at the current directory:

> dotnet run <file-path> < option >*

### Build in A Single File

1. Build a single file by:

> dotnet publish -r <run-time> -p:PublishSingleFile=true --self-contained true

where the `<run-time>` could be:
- Windows: win-x64, win-x86, win-arm, win-arm64.
- Linux: linux-x64, linux-musl-x64 (for Alpine), linux-arm, linux-arm64.
- macOS: osx-x64, osx-arm64 (for M1 Macs and later).

2. Run the file:

> dotnet run <file-path> < option >*

### Options:

- **`<file-path>`** : The path to the `.program` file. This is a required parameter.

- **`-O <output-path>`** : Specify the output path. Otherwise it will be the same as the `<program-path>` with extension changing to ".txt".

- **`-accuracy <accuracy-number>`** or **`-acc <accuracy-number>`** : Set the desired accuracy level for end-loop scores with a numeric value.

- **`-termination`** : Use the 'termination' termination type. This is the default.

- **`-direct`** : Use the 'direct' termination type.

- **`-concentration`** : Use the 'concentration' termination type.

- **`-truncate`** or **`-truncation`** : Enables truncation in the analysis (enabled by default).

- **`-no-truncation`** or **`-non-truncate`** : Run the analysis without truncation.

- **`-R<name>:<min>~<max>`**: Specify the range of a given variable in the program (no space).

- **`-m:<number>`**: Specify the division number `m` as in the paper (no space).

- **`-degree:<number>`**: Specify the degree number `d` as in the paper (no space).

## Default Example Configurations

```
# Table 1
dotnet run h-t-r-2-3.program -concentration -m:40
dotnet run h-t-r-2-3-inside-score.program -concentration -m:40
dotnet run pedestrian-beta.program -direct
dotnet run pedestrian-multiple-branches-v3.program -termination -degree:4
dotnet run pedestrian-multiple-branches-v4.program -termination -degree:4
dotnet run phylogenetic-model.program -no_truncate -termination -m:40 -Rp_lambda:0~2 -Rp_time:0~10
dotnet run random-walk-beta-inside-scorey-v1.program -termination
dotnet run random-walk-beta-inside-scorey-v2.program -termination
dotnet run random-walk-beta-inside-scorey-v3.program -termination
dotnet run random-walk-beta-inside-scorey-v4.program -termination
# Table 2
dotnet run para-estimation-recursive.program -no_truncate -direct -acc 1e-5 -Rp_p:0~1 -Rp_t:0~10 -degree:8
dotnet run pedestrian-beta-inside-v1.program -direct -acc 1e-4
dotnet run pedestrian-beta-inside-v2.program -direct -acc 1e-4
dotnet run pedestrian-beta-inside-v3.program -direct -acc 1e-4
dotnet run pedestrian-beta-inside-v4.program -direct -acc 1e-4
dotnet run pedestrian-deviation5.program -direct -acc 1e-4
dotnet run pedestrian-multiple-branches-v5.program -direct -acc 1e-4
dotnet run pedestrian.program -direct -acc 1e-4 -m:90 -degree:10
# Table 3
dotnet run add-uniform-unbounded-Q1.program -no_truncate -direct -Rp_x:0~1 -Rp_y:0~1
dotnet run add-uniform-unbounded-Q2.program -no_truncate -direct -Rp_x:0~1 -Rp_y:0~1
dotnet run cav-example-5-Q1.program -no_truncate -direct -m:10 -Rp_m:10~20 -Rp_i:0~20
dotnet run cav-example-5-Q2.program -no_truncate -direct -m:10 -Rp_m:10~20 -Rp_i:0~20
dotnet run cav-example-7-Q1.program -no_truncate -direct -Rp_c:0~30 -Rp_i:0~4
dotnet run cav-example-7-Q2.program -no_truncate -direct -Rp_c:0~30 -Rp_i:0~4
dotnet run growing-walk-Q1.program -no_truncate -direct -acc 1e-4 -Rp_t:0~0.1 -Rp_x:1~10 -degree:8
dotnet run growing-walk-Q2.program -no_truncate -direct -acc 1e-4 -Rp_t:0~0.1 -Rp_x:1~10 -degree:8
dotnet run random-box-walk-Q1.program -no_truncate -direct -Rp_x:-0.8~0.8 -Rp_t:0~10 -degree:4
```
